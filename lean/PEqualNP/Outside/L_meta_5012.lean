import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Tuple.Sort

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

namespace BoundarySources

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012

noncomputable def sources (n : ℕ) (C : Circuit) (B J : Finset ℕ) (w : ℕ) : Finset ℕ := by
  classical
  exact B.filter (fun b => Relation.ReflTransGen (CountCut.cutOrStep n C J) b w)

lemma step_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u v : ℕ)
    (hstep : CountCut.orWireStep n C u v) :
    wireVal n C u x = true → wireVal n C v x = true := by
  rintro hu
  obtain ⟨j, hj, rfl, hop, hread, hlt⟩ := hstep
  exact MixedFrontier.W_or n C x j hj hop u hread hlt hu

lemma path_value {n : ℕ} (C : Circuit) (J : Finset ℕ) (x : Fin n → Bool)
    {u v : ℕ} (hpath : Relation.ReflTransGen (CountCut.cutOrStep n C J) u v) :
    wireVal n C u x = true → wireVal n C v x = true := by
  induction hpath with
  | refl => exact id
  | tail _ hs ih => exact fun hu => step_value C x _ _ hs.1 (ih hu)

lemma wire_true_iff_source {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (B J : Finset ℕ)
    (hJ : ∀ w ∈ J, ∃ j < C.gates.length, w = n + j ∧ (gateAt C j).op = GateOp.or)
    (hparents : ∀ w ∈ J, ∀ b : Fin 2, opnd C (w - n) b ∈ B ∪ J)
    (x : Fin n → Bool) :
    ∀ w ∈ B ∪ J, wireVal n C w x = true ↔
      ∃ b ∈ sources n C B J w, wireVal n C b x = true := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    constructor
    · intro hv
      by_cases hb : w ∈ B
      · exact ⟨w, Finset.mem_filter.mpr ⟨hb, Relation.ReflTransGen.refl⟩, hv⟩
      have hwJ : w ∈ J := (Finset.mem_union.mp hw).resolve_left hb
      obtain ⟨j, hj, rfl, hop⟩ := hJ w hwJ
      obtain ⟨_, hinp, ha, hb, _⟩ := CriticalEdge.gate2 hAO hj
      have hh : CriticalEdge.isAnd C j = false := by simp [CriticalEdge.isAnd, hop]
      have hrec := CriticalEdge.val_rec C hAO x j hj
      change CriticalEdge.val n C x (n + j) = true at hv
      rw [hrec] at hv
      simp only [hh, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at hv
      have pick : ∀ d : Fin 2, wireVal n C (opnd C j d) x = true →
          ∃ b ∈ sources n C B J (n + j), wireVal n C b x = true := by
        intro d hd
        have hdmem : opnd C j d ∈ (gateAt C j).inputs := by
          rw [hinp]
          fin_cases d <;> simp
        have hdlt := hAO.2.1 j hj _ hdmem
        have hdpar : opnd C j d ∈ B ∪ J := by
          simpa using hparents (n + j) hwJ d
        obtain ⟨b, hbS, hbV⟩ := (ih (opnd C j d) hdlt hdpar).mp hd
        obtain ⟨hbB, hbPath⟩ := Finset.mem_filter.mp hbS
        refine ⟨b, Finset.mem_filter.mpr ⟨hbB, hbPath.tail ?_⟩, hbV⟩
        exact ⟨⟨j, hj, rfl, hop, hdmem, hdlt⟩, hwJ⟩
      rcases hv with hv | hv
      · exact pick 0 hv
      · exact pick 1 hv
    · rintro ⟨b, hb, hv⟩
      exact path_value C J x (Finset.mem_filter.mp hb).2 hv

lemma wire_eq_sourceOr {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (B J : Finset ℕ)
    (hJ : ∀ w ∈ J, ∃ j < C.gates.length, w = n + j ∧ (gateAt C j).op = GateOp.or)
    (hparents : ∀ w ∈ J, ∀ b : Fin 2, opnd C (w - n) b ∈ B ∪ J)
    (x : Fin n → Bool) (w : ℕ) (hw : w ∈ B ∪ J) :
    wireVal n C w x = TwoOrBuild.sourceOr C.gates (List.ofFn x) (sources n C B J w) := by
  apply Bool.eq_iff_iff.mpr
  rw [wire_true_iff_source C hAO B J hJ hparents x w hw]
  simp [TwoOrBuild.sourceOr, TwoOrBuild.run, wireVal, Circuit.wires]

lemma sources_subset (n : ℕ) (C : Circuit) (B J : Finset ℕ) (w : ℕ) :
    sources n C B J w ⊆ B := by
  classical
  exact Finset.filter_subset _ _

lemma two_sources_union (n : ℕ) (C : Circuit) (B J : Finset ℕ) (r s : ℕ)
    (hused : ∀ b ∈ B, ∃ j ∈ J, CountCut.cutOrStep n C J b j)
    (hroot : ∀ j ∈ J, Relation.ReflTransGen (CountCut.cutOrStep n C J) j r ∨
      Relation.ReflTransGen (CountCut.cutOrStep n C J) j s) :
    sources n C B J r ∪ sources n C B J s = B := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (sources_subset n C B J r) (sources_subset n C B J s)
  · intro b hb
    obtain ⟨j, hj, hstep⟩ := hused b hb
    rcases hroot j hj with hr | hs
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hb, (Relation.ReflTransGen.single hstep).trans hr⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hb, (Relation.ReflTransGen.single hstep).trans hs⟩)

lemma pairCost_le_gates (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (B J : Finset ℕ) (hdis : Disjoint B J) (r s : ℕ) (hr : r ∈ J) (hs : s ∈ J)
    (hparents : ∀ j ∈ J, ∀ d : Fin 2, opnd C (j - n) d ∈ B ∪ J)
    (hused : ∀ b ∈ B, ∃ j ∈ J, CountCut.cutOrStep n C J b j)
    (hroot : ∀ j ∈ J, Relation.ReflTransGen (CountCut.cutOrStep n C J) j r ∨
      Relation.ReflTransGen (CountCut.cutOrStep n C J) j s)
    (hSr : (sources n C B J r).Nonempty) (hSs : (sources n C B J s).Nonempty) :
    TwoOrBuild.pairCost (sources n C B J r) (sources n C B J s) ≤ J.card := by
  classical
  have hU := two_sources_union n C B J r s hused hroot
  have hR : ({r, s} : Finset ℕ) ⊆ B ∪ J := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> exact Finset.mem_union_right _ (by assumption)
  have hused' : ∀ b ∈ B, ∃ j ∈ J, b = opnd C (j - n) 0 ∨ b = opnd C (j - n) 1 := by
    intro b hb
    obtain ⟨j, hj, hstep⟩ := hused b hb
    exact ⟨j, hj, CountCut.orStep_operand_eq n C hAO b j hstep.1⟩
  have hroot' : ∀ j ∈ J, ∃ w ∈ ({r, s} : Finset ℕ),
      Relation.ReflTransGen (CountCut.cutOrStep n C J) j w := by
    intro j hj
    rcases hroot j hj with hjr | hjs
    · exact ⟨r, by simp, hjr⟩
    · exact ⟨s, by simp, hjs⟩
  by_cases hI : sources n C B J r ∩ sources n C B J s = ∅
  · have hbound := CountCut.circuit_cut_boundary_le_gates_add_two n C hAO B J {r, s}
      hdis (by have := Finset.card_insert_le r ({s} : Finset ℕ); simp_all)
      (fun j hj => hparents j hj 0) (fun j hj => hparents j hj 1) hR hused' hroot'
    have hcard := Finset.card_union_add_card_inter (sources n C B J r) (sources n C B J s)
    rw [hU, hI, Finset.card_empty] at hcard
    have hrpos := Finset.card_pos.mpr hSr
    have hspos := Finset.card_pos.mpr hSs
    simp only [TwoOrBuild.pairCost, if_pos hI]
    omega
  · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hI
    obtain ⟨hbr, hbs⟩ := Finset.mem_inter.mp hb
    obtain ⟨hbB, hpathr⟩ := Finset.mem_filter.mp hbr
    have hpaths := (Finset.mem_filter.mp hbs).2
    have hbound := CountCut.circuit_cut_shared_source_boundary_le_gates_add_one n C hAO
      B J {r, s} hdis (fun j hj => hparents j hj 0) (fun j hj => hparents j hj 1)
      hR hused' hroot' b (Finset.mem_union_left _ hbB) (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption)
    simp only [TwoOrBuild.pairCost, if_neg hI, hU]
    omega

end BoundarySources

namespace MixedCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.CriticalEdge
open PEqualNP.Outside.L_meta_5012.MixedFrontier
open PEqualNP.Outside.L_meta_5012.MixedReach

def region (n : ℕ) (C : Circuit) (g h : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun k =>
    ∃ a ∈ ({g, h} : Finset ℕ), ∃ b : Fin 2, OrReaches n C (opnd C a b) k

def pureRegion (n : ℕ) (C : Circuit) (s : Fin n → Bool) (g h : ℕ) : Finset ℕ :=
  (region n C g h).filter fun k => ∃ c : Bool, ∀ i ∈ orIn n C (n + k), s i = c

def mixedRegion (n : ℕ) (C : Circuit) (s : Fin n → Bool) (g h : ℕ) : Finset ℕ :=
  region n C g h \ pureRegion n C s g h

lemma region_mem {n : ℕ} (C : Circuit) (g h k : ℕ) :
    k ∈ region n C g h ↔ k < C.gates.length ∧
      ∃ a ∈ ({g, h} : Finset ℕ), ∃ b : Fin 2, OrReaches n C (opnd C a b) k := by
  simp only [region, Finset.mem_filter, Finset.mem_range]

lemma junk_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hj : j ∈ junk G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2.1⟩

lemma operand_mem {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (a : ℕ)
    (ha : a < C.gates.length) (b : Fin 2) : opnd C a b ∈ (gateAt C a).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem' C a ha)
  unfold opnd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

lemma and_ancestor_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hT : TopForm G C) (a k : ℕ)
    (ha : a < C.gates.length) (hk : k < C.gates.length)
    (haop : (gateAt C a).op = GateOp.and) (hkop : (gateAt C k).op = GateOp.and)
    (hcone : InCone n C k a) : k ∈ junk G C := by
  have hnb : ¬ BelowF G C k := fun hb => hT k hk a ha hkop hb haop hcone
  have hex : ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
    by_contra h
    apply hnb
    intro x hx
    by_contra hf
    exact h ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  obtain ⟨x, hx, hf⟩ := hex
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkop, hk, x, hx, hf⟩

lemma region_only_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (k : ℕ) (hk : k ∈ region n C g h) : (gateAt C k).op = GateOp.or := by
  obtain ⟨hklt, a, hapair, b, hr⟩ := (region_mem C g h k).mp hk
  have haj : a ∈ junk G C := by rwa [hpair]
  obtain ⟨halt, haop⟩ := junk_data G C a haj
  have hbmem := operand_mem C hAO a halt b
  have hblt := hAO.2.1 a halt _ hbmem
  have hcone := reach_cone n C a halt _ hbmem hblt k hr
  rcases hAO.1 _ (gateAt_mem' C k hklt) with hop | hop
  · have hkj := and_ancestor_junk G C hT a k halt hklt haop hop hcone
    rw [hpair] at hkj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hapair hkj
    rcases hapair with haeq | haeq <;> rcases hkj with hkeq | hkeq
    · subst a
      subst k
      have := inCone_lt n C g g hcone
      omega
    · subst a
      subst k
      exact (hhg hcone).elim
    · subst a
      subst k
      exact (hgh hcone).elim
    · subst a
      subst k
      have := inCone_lt n C h h hcone
      omega
  · exact hop

lemma orSets_trans {n : ℕ} (C : Circuit) :
    ∀ k < C.gates.length, ∀ j, j ∈ (orSets n C).getD k [] →
      ∀ r, r ∈ (orSets n C).getD j [] → r ∈ (orSets n C).getD k [] := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk j hj r hr
    rcases (orSets_mem_iff n C k j hk).mp hj with heq | ⟨hop, w, hw, hn, hlt, hmem⟩
    · subst j
      exact hr
    · have hsub := ih (w - n) (by omega) (by omega) j hmem r hr
      exact (orSets_mem_iff n C k r hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hsub⟩)

lemma orReaches_transitive {n : ℕ} (C : Circuit) (w k r : ℕ)
    (hw : w < n + C.gates.length) (hk : OrReaches n C w k)
    (hr : OrReaches n C (n + k) r) : OrReaches n C w r := by
  obtain ⟨hn, hmem⟩ := hk
  obtain ⟨_, hinner⟩ := hr
  have heq : n + k - n = k := by omega
  rw [heq] at hinner
  exact ⟨hn, orSets_trans C (w - n) (by omega) k hmem r hinner⟩

lemma region_predecessor_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (k : ℕ) (hk : k ∈ region n C g h) (r : ℕ)
    (hread : n + r ∈ (gateAt C k).inputs) : r ∈ region n C g h := by
  have hop := region_only_or G C hAO hT g h hpair hgh hhg k hk
  obtain ⟨hklt, a, hapair, b, hreach⟩ := (region_mem C g h k).mp hk
  have hrk := hAO.2.1 k hklt (n + r) hread
  have hrlt : r < C.gates.length := by omega
  have hrreach := orReach_trans n C k hklt hop (n + r) hread hrk r (orReach_self n C r hrlt)
  have haj : a ∈ junk G C := by rwa [hpair]
  have halt := (junk_data G C a haj).1
  have hoblt := hAO.2.1 a halt _ (operand_mem C hAO a halt b)
  exact (region_mem C g h r).mpr ⟨hrlt, a, hapair, b,
    orReaches_transitive C _ k r (by omega) hreach hrreach⟩

lemma region_or_ancestor_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (g h : ℕ) (hpair : junk G C = {g, h})
    (k : ℕ) (hk : k ∈ region n C g h) (r : ℕ)
    (hr : OrReaches n C (n + k) r) : r ∈ region n C g h := by
  obtain ⟨hklt, a, hapair, b, hreach⟩ := (region_mem C g h k).mp hk
  have hrmem := hr.2
  have heq : n + k - n = k := by omega
  rw [heq] at hrmem
  have hrlt : r < C.gates.length := by
    rcases orSets_cone n C k hklt r hrmem with h | h
    · omega
    · have := inCone_lt n C k r h
      omega
  have haj : a ∈ junk G C := by rwa [hpair]
  have halt := (junk_data G C a haj).1
  have hoblt := hAO.2.1 a halt _ (operand_mem C hAO a halt b)
  exact (region_mem C g h r).mpr ⟨hrlt, a, hapair, b,
    orReaches_transitive C _ k r (by omega) hreach hr⟩

lemma region_gate_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (k : ℕ) (hk : k ∈ region n C g h) (x : Fin n → Bool) :
    W n C x (n + k) = true ↔ ∃ i ∈ orIn n C (n + k), x i = true := by
  constructor
  · intro hv
    have hops : ∀ a < C.gates.length,
        (gateAt C a).op = GateOp.and ∨ (gateAt C a).op = GateOp.or :=
      fun a ha => hAO.1 _ (gateAt_mem' C a ha)
    rcases down n C x hops (n + k) hv with hi | ⟨a, ha, hr, haop, _⟩
    · exact hi
    · have haK := region_or_ancestor_closed G C hAO g h hpair k hk a hr
      have hor := region_only_or G C hAO hT g h hpair hgh hhg a haK
      rw [haop] at hor
      cases hor
  · rintro ⟨i, hi, hx⟩
    exact orIn_val C x (n + k) i hi hx

lemma region_support_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (k : ℕ) (hk : k ∈ region n C g h) : (orIn n C (n + k)).Nonempty := by
  have hklt := ((region_mem C g h k).mp hk).1
  have hv := W_all_true C hAO (n + k) (by omega)
  obtain ⟨i, hi, _⟩ := (region_gate_semantics G C hAO hT g h hpair hgh hhg k hk _).mp hv
  exact ⟨i, hi⟩

lemma pureRegion_predecessor_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (k : ℕ) (hk : k ∈ pureRegion n C s g h) (r : ℕ)
    (hread : n + r ∈ (gateAt C k).inputs) : r ∈ pureRegion n C s g h := by
  obtain ⟨hkK, c, hmono⟩ := Finset.mem_filter.mp hk
  have hop := region_only_or G C hAO hT g h hpair hgh hhg k hkK
  have hklt := ((region_mem C g h k).mp hkK).1
  have hrK := region_predecessor_closed G C hAO hT g h hpair hgh hhg k hkK r hread
  have hsub := orIn_or_step C k hklt hop (n + r) hread (hAO.2.1 k hklt _ hread)
  exact Finset.mem_filter.mpr ⟨hrK, c, fun i hi => hmono i (hsub hi)⟩

lemma not_monochromatic_mixed {n : ℕ} (s : Fin n → Bool) (S : Finset (Fin n))
    (hpure : ¬ ∃ c : Bool, ∀ i ∈ S, s i = c) :
    ∀ c : Bool, ∃ i ∈ S, s i = c := by
  intro c
  by_contra h
  push Not at h
  apply hpure
  refine ⟨!c, ?_⟩
  intro i hi
  have hbool : ∀ a b : Bool, a ≠ b → a = !b := by decide
  exact hbool (s i) c (h i hi)

lemma mixedRegion_mem {n : ℕ} (C : Circuit) (s : Fin n → Bool) (g h k : ℕ) :
    k ∈ mixedRegion n C s g h ↔ k ∈ region n C g h ∧
      ∀ c : Bool, ∃ i ∈ orIn n C (n + k), s i = c := by
  constructor
  · intro hk
    obtain ⟨hkK, hkP⟩ := Finset.mem_sdiff.mp hk
    refine ⟨hkK, not_monochromatic_mixed s _ ?_⟩
    intro hpure
    exact hkP (Finset.mem_filter.mpr ⟨hkK, hpure⟩)
  · rintro ⟨hkK, hmix⟩
    refine Finset.mem_sdiff.mpr ⟨hkK, ?_⟩
    intro hkP
    exact mixed_not_monochromatic s _ hmix (Finset.mem_filter.mp hkP).2

lemma mixedRegion_boundary_raw_or_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (k : ℕ) (hk : k ∈ mixedRegion n C s g h) (w : ℕ)
    (hread : w ∈ (gateAt C k).inputs)
    (hout : ∀ r ∈ mixedRegion n C s g h, w ≠ n + r) :
    w < n ∨ ∃ r ∈ pureRegion n C s g h, w = n + r := by
  by_cases hw : w < n
  · exact Or.inl hw
  right
  obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w - n, by omega⟩
  have hkK := (Finset.mem_sdiff.mp hk).1
  have hrK := region_predecessor_closed G C hAO hT g h hpair hgh hhg k hkK r hread
  refine ⟨r, ?_, rfl⟩
  by_contra hnot
  exact hout r (Finset.mem_sdiff.mpr ⟨hrK, hnot⟩) rfl

lemma all_mixed_mem_region {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g, h}) (k : ℕ) (hk : k < C.gates.length)
    (hmix : ∀ c : Bool, ∃ i ∈ orIn n C (n + k), s i = c) :
    k ∈ region n C g h := by
  obtain ⟨a, ha, b, hr⟩ := least_mixed_reaches_junk G C s hbip hL hT hJ k hk hmix
  exact (region_mem C g h k).mpr ⟨hk, a, by rwa [← hpair], b, hr⟩

lemma mixedRegion_or_reader_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (k : ℕ) (hk : k ∈ mixedRegion n C s g h) (r : ℕ)
    (hr : r < C.gates.length) (hrop : (gateAt C r).op = GateOp.or)
    (hread : n + k ∈ (gateAt C r).inputs) : r ∈ mixedRegion n C s g h := by
  obtain ⟨_, hmix⟩ := (mixedRegion_mem C s g h k).mp hk
  have hsub := orIn_or_step C r hr hrop (n + k) hread (hL.1.2.1 r hr _ hread)
  have hmixr : ∀ c : Bool, ∃ i ∈ orIn n C (n + r), s i = c := by
    intro c
    obtain ⟨i, hi, hc⟩ := hmix c
    exact ⟨i, hsub hi, hc⟩
  exact (mixedRegion_mem C s g h r).mpr
    ⟨all_mixed_mem_region G C s hbip hL hT hJ g h hpair r hr hmixr, hmixr⟩

lemma mixedRegion_external_reader_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (k : ℕ) (hk : k ∈ mixedRegion n C s g h) (r : ℕ)
    (hr : r < C.gates.length) (hnot : r ∉ mixedRegion n C s g h)
    (hread : n + k ∈ (gateAt C r).inputs) : r ∈ junk G C := by
  rcases hL.1.1 _ (gateAt_mem' C r hr) with hop | hop
  · obtain ⟨hkK, hmix⟩ := (mixedRegion_mem C s g h k).mp hk
    have hklt := ((region_mem C g h k).mp hkK).1
    have hlen := hL.1.2.2 _ (gateAt_mem' C r hr)
    obtain ⟨p, hp, heq⟩ := List.getElem_of_mem hread
    have hp' : p < 2 := by omega
    have hb : opnd C r ⟨p, hp'⟩ = n + k := by
      unfold opnd
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
      exact heq
    apply mixed_and_frontier_junk G C s hbip hL.1 hT hJ k hmix r hr hop ⟨p, hp'⟩
    rw [hb]
    exact orReach_self n C k hklt
  · exact (hnot (mixedRegion_or_reader_closed G C s hbip hL hT hJ g h hpair k hk r hr hop hread)).elim

lemma mixedRegion_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hfun : circuitFun n C = graphFun G ∅) (g h k : ℕ)
    (hk : k ∈ mixedRegion n C s g h) : n + k ≠ C.output := by
  obtain ⟨hkK, hmix⟩ := (mixedRegion_mem C s g h k).mp hk
  have hklt := ((region_mem C g h k).mp hkK).1
  intro he
  apply mixed_not_or_output G C s hbip hfun k hmix
  rw [← he]
  exact orReach_self n C k hklt

lemma junk_not_mem_region {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j ∈ junk G C) : j ∉ region n C g h := by
  intro hreg
  have hor := region_only_or G C hAO hT g h hpair hgh hhg j hreg
  have hand := (junk_data G C j hj).2
  rw [hand] at hor
  cases hor

end MixedCut

namespace MixedCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.MixedFrontier
open PEqualNP.Outside.L_meta_5012.MixedReach

lemma raw_or_region_wire_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w : ℕ) (hw : w < n ∨ ∃ k ∈ region n C g h, w = n + k) (x : Fin n → Bool) :
    wireVal n C w x = decide (∃ i ∈ orIn n C w, x i = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  rcases hw with hraw | ⟨k, hk, rfl⟩
  · change W n C x w = true ↔ _
    constructor
    · intro hv
      rw [W_input n C x w hraw] at hv
      exact ⟨⟨w, hraw⟩, (orIn_mem n C w _).mpr (Or.inl rfl), hv⟩
    · rintro ⟨i, hi, hx⟩
      exact orIn_val C x w i hi hx
  · exact region_gate_semantics G C hAO hT g h hpair hgh hhg k hk x

lemma raw_or_region_support_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w : ℕ) (hw : w < n ∨ ∃ k ∈ region n C g h, w = n + k) :
    (orIn n C w).Nonempty := by
  rcases hw with hraw | ⟨k, hk, rfl⟩
  · exact ⟨⟨w, hraw⟩, (orIn_mem n C w _).mpr (Or.inl rfl)⟩
  · exact region_support_nonempty G C hAO hT g h hpair hgh hhg k hk

lemma raw_or_pure_support_monochromatic {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (g h w : ℕ) (hw : w < n ∨ ∃ k ∈ pureRegion n C s g h, w = n + k) :
    ∃ c : Bool, ∀ i ∈ orIn n C w, s i = c := by
  rcases hw with hraw | ⟨k, hk, rfl⟩
  · refine ⟨s ⟨w, hraw⟩, ?_⟩
    intro i hi
    rcases (orIn_mem n C w i).mp hi with heq | ⟨k, hk, hr, _, _⟩
    · have hiw : i = (⟨w, hraw⟩ : Fin n) := Fin.ext heq
      rw [hiw]
    · have := hr.1
      omega
  · exact (Finset.mem_filter.mp hk).2

lemma mixedRegion_boundary_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (k : ℕ) (hk : k ∈ mixedRegion n C s g h) (w : ℕ)
    (hread : w ∈ (gateAt C k).inputs)
    (hout : ∀ r ∈ mixedRegion n C s g h, w ≠ n + r) :
    (orIn n C w).Nonempty ∧ (∃ c : Bool, ∀ i ∈ orIn n C w, s i = c) ∧
      ∀ x : Fin n → Bool, wireVal n C w x = decide (∃ i ∈ orIn n C w, x i = true) := by
  have hw := mixedRegion_boundary_raw_or_pure G C s hAO hT g h hpair hgh hhg k hk w hread hout
  have hwK : w < n ∨ ∃ a ∈ region n C g h, w = n + a := by
    rcases hw with hraw | ⟨a, ha, heq⟩
    · exact Or.inl hraw
    · exact Or.inr ⟨a, (Finset.mem_filter.mp ha).1, heq⟩
  exact ⟨raw_or_region_support_nonempty G C hAO hT g h hpair hgh hhg w hwK,
    raw_or_pure_support_monochromatic C s g h w hw,
    raw_or_region_wire_semantics G C hAO hT g h hpair hgh hhg w hwK⟩

end MixedCut

namespace Reorder

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


open PEqualNP.TopForm PEqualNP.CleanedNonEdge

def wireMap (n N : ℕ) (p : Equiv.Perm (Fin N)) (w : ℕ) : ℕ :=
  if w < n then w
  else if h : w - n < N then n + (p ⟨w - n, h⟩).val
  else n + N

def mappedGate (n N : ℕ) (p : Equiv.Perm (Fin N)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wireMap n N p)⟩

def permute (n : ℕ) (C : Circuit) (p : Equiv.Perm (Fin C.gates.length)) : Circuit :=
  ⟨List.ofFn (fun k => mappedGate n C.gates.length p C.gates[(p.symm k).val]),
    wireMap n C.gates.length p C.output⟩

def DependencyOrder (n : ℕ) (C : Circuit) (p : Equiv.Perm (Fin C.gates.length)) : Prop :=
  ∀ i j : Fin C.gates.length, n + i.val ∈ (gateAt C j.val).inputs → (p i).val < (p j).val

lemma wireMap_input {n N : ℕ} (p : Equiv.Perm (Fin N)) (w : ℕ) (hw : w < n) :
    wireMap n N p w = w := by simp [wireMap, hw]

lemma wireMap_gate {n N : ℕ} (p : Equiv.Perm (Fin N)) (j : Fin N) :
    wireMap n N p (n + j.val) = n + (p j).val := by
  simp [wireMap, Nat.not_lt.mpr (Nat.le_add_right n j.val), j.isLt]

lemma wireMap_large {n N : ℕ} (p : Equiv.Perm (Fin N)) (w : ℕ) (hw : n + N ≤ w) :
    wireMap n N p w = n + N := by
  have hn : ¬ w < n := by omega
  have hN : ¬ w - n < N := by omega
  simp [wireMap, hn, hN]

lemma permute_length (n : ℕ) (C : Circuit) (p : Equiv.Perm (Fin C.gates.length)) :
    (permute n C p).gates.length = C.gates.length := by simp [permute]

lemma permute_gateAt (n : ℕ) (C : Circuit) (p : Equiv.Perm (Fin C.gates.length))
    (k : Fin C.gates.length) :
    gateAt (permute n C p) k.val = mappedGate n C.gates.length p C.gates[(p.symm k).val] := by
  simp [permute, gateAt, List.getD_eq_getElem?_getD, k.isLt]

lemma gateAt_get (C : Circuit) (j : Fin C.gates.length) : gateAt C j.val = C.gates[j.val] :=
  List.getD_eq_getElem _ _ j.isLt

lemma wireMap_operand_lt {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (p : Equiv.Perm (Fin C.gates.length)) (hp : DependencyOrder n C p)
    (j : Fin C.gates.length) (w : ℕ) (hw : w ∈ (gateAt C j.val).inputs) :
    wireMap n C.gates.length p w < n + (p j).val := by
  have hb := hC.2.1 j.val j.isLt w hw
  by_cases hn : w < n
  · rw [wireMap_input p w hn]
    omega
  · have hi : w - n < C.gates.length := by have := j.isLt; omega
    let i : Fin C.gates.length := ⟨w - n, hi⟩
    have heq : n + i.val = w := by dsimp [i]; omega
    have hdep := hp i j (by rwa [heq])
    rw [← heq, wireMap_gate]
    omega

lemma permute_isAO2 {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (p : Equiv.Perm (Fin C.gates.length)) (hp : DependencyOrder n C p) :
    IsAO2 n (permute n C p) := by
  apply ok_ao
  intro k hk
  have hk' : k < C.gates.length := by simpa only [List.length_ofFn] using hk
  let q : Fin C.gates.length := ⟨k, hk'⟩
  let j : Fin C.gates.length := p.symm q
  obtain ⟨o, a, b, hgt, hop, ha, hb⟩ := ao_ok C hC j.val j.isLt
  have hinputs : (gateAt C j.val).inputs = [a, b] := by
    rw [gateAt_get C j, hgt]
  refine ⟨o, wireMap n C.gates.length p a, wireMap n C.gates.length p b, ?_, hop, ?_, ?_⟩
  · simp only [List.getElem_ofFn]
    change mappedGate n C.gates.length p C.gates[j.val] = _
    rw [hgt]
    rfl
  · have h := wireMap_operand_lt C hC p hp j a (by rw [hinputs]; simp)
    simpa [j, q] using h
  · have h := wireMap_operand_lt C hC p hp j b (by rw [hinputs]; simp)
    simpa [j, q] using h

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run C.gates (List.ofFn x)).getD w false

lemma wv_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = (List.ofFn x).getD w false :=
  run_input C.gates (List.ofFn x) w (by simpa using hw)

lemma wv_gate {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool)
    (j : Fin C.gates.length) :
    wv n C x (n + j.val) = (gateAt C j.val).op.eval
      ((gateAt C j.val).inputs.map (wv n C x)) := by
  have h := run_gate C.gates (List.ofFn x) j.val j.isLt
  rw [List.length_ofFn] at h
  change (run C.gates (List.ofFn x)).getD (n + j.val) false = _
  rw [h, ← gateAt_get C j]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [if_pos (hC.2.1 j.val j.isLt w hw)]
  rfl

lemma permute_wv_gate {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (p : Equiv.Perm (Fin C.gates.length)) (hp : DependencyOrder n C p) (x : Fin n → Bool) :
    ∀ k : ℕ, ∀ hk : k < C.gates.length,
      wv n (permute n C p) x (n + k) = wv n C x (n + (p.symm ⟨k, hk⟩).val) := by
  have hD := permute_isAO2 C hC p hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    let q : Fin C.gates.length := ⟨k, hk⟩
    let j : Fin C.gates.length := p.symm q
    have hkD : k < (permute n C p).gates.length := by simpa only [permute_length] using hk
    have hrec := wv_gate (permute n C p) hD x ⟨k, hkD⟩
    rw [permute_gateAt n C p q] at hrec
    change wv n (permute n C p) x (n + k) = wv n C x (n + j.val)
    rw [hrec, wv_gate C hC x j, gateAt_get C j]
    simp only [mappedGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hw' : w ∈ (gateAt C j.val).inputs := by rwa [gateAt_get C j]
    have hb := hC.2.1 j.val j.isLt w hw'
    by_cases hn : w < n
    · rw [Function.comp_apply, wireMap_input p w hn, wv_input _ x w hn, wv_input _ x w hn]
    · have hi : w - n < C.gates.length := by have := j.isLt; omega
      let i : Fin C.gates.length := ⟨w - n, hi⟩
      have heq : n + i.val = w := by dsimp [i]; omega
      have hdep : (p i).val < k := by
        have h := hp i j (by rwa [heq])
        simpa [j, q] using h
      have hh := ih (p i).val hdep (p i).isLt
      have hsym : p.symm ⟨(p i).val, (p i).isLt⟩ = i := p.symm_apply_apply i
      rw [hsym] at hh
      rw [Function.comp_apply, ← heq, wireMap_gate]
      exact hh

lemma permute_wv {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (p : Equiv.Perm (Fin C.gates.length)) (hp : DependencyOrder n C p)
    (x : Fin n → Bool) (w : ℕ) :
    wv n (permute n C p) x (wireMap n C.gates.length p w) = wv n C x w := by
  by_cases hn : w < n
  · rw [wireMap_input p w hn, wv_input _ x w hn, wv_input _ x w hn]
  by_cases hN : w - n < C.gates.length
  · let j : Fin C.gates.length := ⟨w - n, hN⟩
    have heq : n + j.val = w := by dsimp [j]; omega
    have hh := permute_wv_gate C hC p hp x (p j).val (p j).isLt
    have hsym : p.symm ⟨(p j).val, (p j).isLt⟩ = j := p.symm_apply_apply j
    rw [hsym] at hh
    rw [← heq, wireMap_gate]
    exact hh
  · have hw : n + C.gates.length ≤ w := by omega
    rw [wireMap_large p w hw]
    change (run (permute n C p).gates (List.ofFn x)).getD (n + C.gates.length) false =
      (run C.gates (List.ofFn x)).getD w false
    rw [List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn, permute_length]),
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; exact hw)]

lemma permute_semantics {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (p : Equiv.Perm (Fin C.gates.length)) (hp : DependencyOrder n C p) :
    IsAO2 n (permute n C p) ∧ (permute n C p).size = C.size ∧
      circuitFun n (permute n C p) = circuitFun n C ∧
      ∀ x : Fin n → Bool, ∀ w : ℕ,
        wireVal n (permute n C p) (wireMap n C.gates.length p w) x = wireVal n C w x := by
  refine ⟨permute_isAO2 C hC p hp, permute_length n C p, ?_, ?_⟩
  · funext x
    exact permute_wv C hC p hp x C.output
  · exact permute_wv C hC p hp

noncomputable def sortPerm {N : ℕ} (key : Fin N → ℕ) : Equiv.Perm (Fin N) :=
  (Tuple.sort key).symm

lemma sortPerm_key_lt {N : ℕ} (key : Fin N → ℕ) (i j : Fin N)
    (hkey : key i < key j) : (sortPerm key i).val < (sortPerm key j).val := by
  by_contra h
  have hle : sortPerm key j ≤ sortPerm key i := by change _ ≤ _; omega
  have hs := Tuple.monotone_sort key hle
  have hkey' : key j ≤ key i := by simpa [sortPerm, Function.comp_apply] using hs
  omega

lemma sortPerm_prefix {N : ℕ} (key : Fin N → ℕ) (a : ℕ) (j : Fin N) :
    (sortPerm key j).val < (Finset.univ.filter (fun i : Fin N => key i < a)).card ↔ key j < a := by
  let σ := Tuple.sort key
  let Q : Finset (Fin N) := Finset.univ.filter (fun k => key (σ k) < a)
  let R : Finset (Fin N) := Finset.univ.filter (fun k => key k < a)
  have himage : Q.image σ = R := by
    ext i
    simp only [Q, R, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hi
      exact ⟨σ.symm i, by simpa only [Equiv.apply_symm_apply] using hi, σ.apply_symm_apply i⟩
  have hcard : Q.card = R.card := by
    rw [← himage, Finset.card_image_of_injective Q σ.injective]
  have hcut := Tuple.lt_card_lt_iff_apply_lt_of_monotone
    (j := sortPerm key j) (a := a) (Tuple.monotone_sort key)
  change (sortPerm key j).val < Q.card ↔ key (σ (sortPerm key j)) < a at hcut
  rw [hcard] at hcut
  simpa [σ, sortPerm] using hcut

def PredecessorClosed (n : ℕ) (C : Circuit) (S : Finset (Fin C.gates.length)) : Prop :=
  ∀ i j : Fin C.gates.length, j ∈ S → n + i.val ∈ (gateAt C j.val).inputs → i ∈ S

def priorityKey {N : ℕ} (S : Finset (Fin N)) (j : Fin N) : ℕ :=
  if j ∈ S then j.val else N + j.val

lemma priorityKey_lt_iff {N : ℕ} (S : Finset (Fin N)) (j : Fin N) :
    priorityKey S j < N ↔ j ∈ S := by
  by_cases hj : j ∈ S
  · simp [priorityKey, hj, j.isLt]
  · simp only [priorityKey, if_neg hj]
    have : ¬ N + j.val < N := by omega
    simp [this, hj]

lemma closed_hoist_dependency {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (S : Finset (Fin C.gates.length)) (hS : PredecessorClosed n C S) :
    DependencyOrder n C (sortPerm (priorityKey S)) := by
  intro i j hdep
  have hback := hC.2.1 j.val j.isLt (n + i.val) hdep
  have hij : i.val < j.val := by omega
  apply sortPerm_key_lt
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp only [priorityKey, if_pos hi, if_pos hj]
    exact hij
  · simp only [priorityKey, if_pos hi, if_neg hj]
    have := i.isLt
    omega
  · exact (hi (hS i j hj hdep)).elim
  · simp only [priorityKey, if_neg hi, if_neg hj]
    omega

lemma closed_hoist_prefix {N : ℕ} (S : Finset (Fin N)) (j : Fin N) :
    (sortPerm (priorityKey S) j).val < S.card ↔ j ∈ S := by
  have hset : Finset.univ.filter (fun i : Fin N => priorityKey S i < N) = S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, priorityKey_lt_iff]
  have h := sortPerm_prefix (priorityKey S) N j
  rwa [hset, priorityKey_lt_iff] at h

lemma closed_hoist_stable {N : ℕ} (S : Finset (Fin N)) (i j : Fin N)
    (hmem : i ∈ S ↔ j ∈ S) (hij : i.val < j.val) :
    (sortPerm (priorityKey S) i).val < (sortPerm (priorityKey S) j).val := by
  apply sortPerm_key_lt
  by_cases hi : i ∈ S
  · have hj := hmem.mp hi
    simp only [priorityKey, if_pos hi, if_pos hj]
    exact hij
  · have hj : j ∉ S := fun h => hi (hmem.mpr h)
    simp only [priorityKey, if_neg hi, if_neg hj]
    omega

lemma closed_hoist_semantics {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (S : Finset (Fin C.gates.length)) (hS : PredecessorClosed n C S) :
    IsAO2 n (permute n C (sortPerm (priorityKey S))) ∧
      (permute n C (sortPerm (priorityKey S))).size = C.size ∧
      circuitFun n (permute n C (sortPerm (priorityKey S))) = circuitFun n C ∧
      ∀ x : Fin n → Bool, ∀ w : ℕ,
        wireVal n (permute n C (sortPerm (priorityKey S)))
          (wireMap n C.gates.length (sortPerm (priorityKey S)) w) x = wireVal n C w x := by
  exact permute_semantics C hC _ (closed_hoist_dependency C hC S hS)

def blockKey {N : ℕ} (P K : Finset (Fin N)) (j : Fin N) : ℕ :=
  if j ∈ P then j.val else if j ∈ K then N + j.val else 2 * N + j.val

lemma blockKey_small_iff {N : ℕ} (P K : Finset (Fin N)) (j : Fin N) :
    blockKey P K j < N ↔ j ∈ P := by
  have hjN := j.isLt
  constructor
  · intro hlt
    by_contra hjP
    unfold blockKey at hlt
    rw [if_neg hjP] at hlt
    split_ifs at hlt <;> omega
  · intro hjP
    simpa only [blockKey, if_pos hjP] using hjN

lemma blockKey_large_iff {N : ℕ} (P K : Finset (Fin N)) (hPK : P ⊆ K) (j : Fin N) :
    blockKey P K j < 2 * N ↔ j ∈ K := by
  have hjN := j.isLt
  constructor
  · intro hlt
    by_contra hjK
    have hjP : j ∉ P := fun h => hjK (hPK h)
    simp only [blockKey, if_neg hjP, if_neg hjK] at hlt
    omega
  · intro hjK
    unfold blockKey
    by_cases hjP : j ∈ P
    · rw [if_pos hjP]
      omega
    · rw [if_neg hjP, if_pos hjK]
      omega

lemma two_closed_hoist_dependency {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (P K : Finset (Fin C.gates.length))
    (hP : PredecessorClosed n C P) (hK : PredecessorClosed n C K) :
    DependencyOrder n C (sortPerm (blockKey P K)) := by
  intro i j hdep
  have hback := hC.2.1 j.val j.isLt (n + i.val) hdep
  have hij : i.val < j.val := by omega
  have hiN := i.isLt
  apply sortPerm_key_lt
  by_cases hiP : i ∈ P <;> by_cases hjP : j ∈ P
  · simp only [blockKey, if_pos hiP, if_pos hjP]
    exact hij
  · simp only [blockKey, if_pos hiP, if_neg hjP]
    by_cases hjK : j ∈ K
    · rw [if_pos hjK]
      omega
    · rw [if_neg hjK]
      omega
  · exact (hiP (hP i j hjP hdep)).elim
  · simp only [blockKey, if_neg hiP, if_neg hjP]
    by_cases hiK : i ∈ K <;> by_cases hjK : j ∈ K
    · rw [if_pos hiK, if_pos hjK]
      omega
    · rw [if_pos hiK, if_neg hjK]
      omega
    · exact (hiK (hK i j hjK hdep)).elim
    · rw [if_neg hiK, if_neg hjK]
      omega

lemma two_closed_hoist_prefix_small {N : ℕ} (P K : Finset (Fin N)) (j : Fin N) :
    (sortPerm (blockKey P K) j).val < P.card ↔ j ∈ P := by
  have hset : Finset.univ.filter (fun i : Fin N => blockKey P K i < N) = P := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockKey_small_iff]
  have h := sortPerm_prefix (blockKey P K) N j
  rwa [hset, blockKey_small_iff] at h

lemma two_closed_hoist_prefix_large {N : ℕ} (P K : Finset (Fin N)) (hPK : P ⊆ K) (j : Fin N) :
    (sortPerm (blockKey P K) j).val < K.card ↔ j ∈ K := by
  have hset : Finset.univ.filter (fun i : Fin N => blockKey P K i < 2 * N) = K := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockKey_large_iff P K hPK]
  have h := sortPerm_prefix (blockKey P K) (2 * N) j
  rwa [hset, blockKey_large_iff P K hPK] at h

lemma two_closed_hoist_middle {N : ℕ} (P K : Finset (Fin N)) (hPK : P ⊆ K) (j : Fin N) :
    (P.card ≤ (sortPerm (blockKey P K) j).val ∧
      (sortPerm (blockKey P K) j).val < K.card) ↔ j ∈ K \ P := by
  have hs := two_closed_hoist_prefix_small P K j
  have hl := two_closed_hoist_prefix_large P K hPK j
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨hl.mp hhi, fun h => by have := hs.mpr h; omega⟩
  · rintro ⟨hK, hP⟩
    refine ⟨?_, hl.mpr hK⟩
    by_contra h
    apply hP
    exact hs.mp (by omega)

lemma two_closed_hoist_stable {N : ℕ} (P K : Finset (Fin N)) (i j : Fin N)
    (hP : i ∈ P ↔ j ∈ P) (hK : i ∈ K ↔ j ∈ K) (hij : i.val < j.val) :
    (sortPerm (blockKey P K) i).val < (sortPerm (blockKey P K) j).val := by
  apply sortPerm_key_lt
  by_cases hiP : i ∈ P
  · have hjP := hP.mp hiP
    simp only [blockKey, if_pos hiP, if_pos hjP]
    exact hij
  · have hjP : j ∉ P := fun h => hiP (hP.mpr h)
    simp only [blockKey, if_neg hiP, if_neg hjP]
    by_cases hiK : i ∈ K
    · have hjK := hK.mp hiK
      rw [if_pos hiK, if_pos hjK]
      omega
    · have hjK : j ∉ K := fun h => hiK (hK.mpr h)
      rw [if_neg hiK, if_neg hjK]
      omega

lemma two_closed_hoist_semantics {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (P K : Finset (Fin C.gates.length))
    (hP : PredecessorClosed n C P) (hK : PredecessorClosed n C K) :
    IsAO2 n (permute n C (sortPerm (blockKey P K))) ∧
      (permute n C (sortPerm (blockKey P K))).size = C.size ∧
      circuitFun n (permute n C (sortPerm (blockKey P K))) = circuitFun n C ∧
      ∀ x : Fin n → Bool, ∀ w : ℕ,
        wireVal n (permute n C (sortPerm (blockKey P K)))
          (wireMap n C.gates.length (sortPerm (blockKey P K)) w) x = wireVal n C w x := by
  exact permute_semantics C hC _ (two_closed_hoist_dependency C hC P K hP hK)

lemma permute_gateAt_old (n : ℕ) (C : Circuit) (p : Equiv.Perm (Fin C.gates.length))
    (j : Fin C.gates.length) :
    gateAt (permute n C p) (p j).val = mappedGate n C.gates.length p (gateAt C j.val) := by
  simpa only [Equiv.symm_apply_apply, gateAt_get] using permute_gateAt n C p (p j)

lemma permute_isLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (p : Equiv.Perm (Fin C.gates.length))
    (hp : DependencyOrder n C p) : IsLeastAO G (permute n C p) := by
  obtain ⟨hAO, hsize, hfun, _⟩ := permute_semantics C hC.1 p hp
  refine ⟨hAO, hfun.trans hC.2.1, ?_⟩
  intro D hD hDF
  rw [hsize]
  exact hC.2.2 D hD hDF

lemma take_isAO2 {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (t out : ℕ) :
    IsAO2 n ⟨C.gates.take t, out⟩ := by
  apply ok_ao
  intro j hj
  have hj' : j < C.gates.length := by simp only [List.length_take] at hj; omega
  obtain ⟨o, a, b, heq, hop, ha, hb⟩ := ao_ok C hC j hj'
  refine ⟨o, a, b, ?_, hop, ha, hb⟩
  simpa only [List.getElem_take] using heq

lemma take_wireVal {n : ℕ} (C : Circuit) (t out : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + min t C.gates.length) :
    wireVal n ⟨C.gates.take t, out⟩ w x = wireVal n C w x := by
  have h := run_prefix (C.gates.take t) (C.gates.drop t) (List.ofFn x) w
    (by simpa only [List.length_ofFn, List.length_take] using hw)
  rw [List.take_append_drop] at h
  exact h.symm

end Reorder

namespace Region

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

def remapSuffix (gs : List Gate) (f : ℕ → ℕ → ℕ) : List Gate :=
  List.ofFn fun j : Fin gs.length =>
    ⟨gs[j].op, gs[j].inputs.map (f j)⟩

lemma remapSuffix_length (gs : List Gate) (f : ℕ → ℕ → ℕ) :
    (remapSuffix gs f).length = gs.length := by
  simp [remapSuffix]

lemma remapSuffix_get (gs : List Gate) (f : ℕ → ℕ → ℕ)
    (j : ℕ) (hj : j < gs.length) :
    (remapSuffix gs f)[j]'(by simpa [remapSuffix_length] using hj) =
      ⟨gs[j].op, gs[j].inputs.map (f j)⟩ := by
  simp [remapSuffix]

lemma append_get (p s : List Gate) (j : ℕ) (hj : j < s.length) :
    (p ++ s)[p.length + j]'(by simp; omega) = s[j] := by
  simp

lemma append_get_left (p s : List Gate) (j : ℕ) (hj : j < p.length) :
    (p ++ s)[j]'(by simp; omega) = p[j] := by
  simp [List.getElem_append_left hj]

lemma remapSuffix_ok (n : ℕ) (p s : List Gate) (f : ℕ → ℕ → ℕ)
    (hp : Ok n p)
    (hs : ∀ j (hj : j < s.length),
      ∃ o a b, s[j] = ⟨o, [a, b]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or))
    (hf : ∀ j (hj : j < s.length), ∀ w ∈ s[j].inputs,
      f j w < n + p.length + j) :
    Ok n (p ++ remapSuffix s f) := by
  intro j hj
  by_cases hjp : j < p.length
  · rw [append_get_left p _ j hjp]
    exact hp j hjp
  · have hj' : j - p.length < s.length := by
      simp only [List.length_append, remapSuffix_length] at hj
      omega
    have hjrem : j - p.length < (remapSuffix s f).length := by
      simpa only [remapSuffix_length] using hj'
    have heq : j = p.length + (j - p.length) := by omega
    obtain ⟨o, a, b, hg, hop⟩ := hs (j - p.length) hj'
    have ha := hf (j - p.length) hj' a (by rw [hg]; simp)
    have hb := hf (j - p.length) hj' b (by rw [hg]; simp)
    refine ⟨o, f (j - p.length) a, f (j - p.length) b, ?_, hop, by omega, by omega⟩
    have hget := append_get p (remapSuffix s f) (j - p.length) hjrem
    have hget' : (p ++ remapSuffix s f)[j] = (remapSuffix s f)[j - p.length] := by
      simpa only [← heq] using hget
    rw [hget', remapSuffix_get s f _ hj', hg]
    rfl

lemma ao_grammar {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C)
    (p s : List Gate) (hgs : C.gates = p ++ s) :
    ∀ j (hj : j < s.length),
      ∃ o a b, s[j] = ⟨o, [a, b]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) := by
  intro j hj
  have hmem : s[j] ∈ C.gates := by
    rw [hgs]
    exact List.mem_append_right _ (List.getElem_mem hj)
  have hop := hC.1 _ hmem
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hC.2.2 _ hmem)
  refine ⟨s[j].op, a, b, ?_, hop⟩
  cases h : s[j]
  simp only [h] at hin ⊢
  cases hin
  rfl

lemma ao_suffix_back {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C)
    (p s : List Gate) (hgs : C.gates = p ++ s) :
    ∀ j (hj : j < s.length), ∀ w ∈ s[j].inputs, w < n + p.length + j := by
  intro j hj w hw
  have hi : p.length + j < C.gates.length := by rw [hgs]; simp; omega
  have hgate : gateAt C (p.length + j) = s[j] := by
    rw [gateAt, hgs, List.getD_eq_getElem _ _ (by simp; omega), append_get p s j hj]
  have hh := hC.2.1 (p.length + j) hi w (by rwa [hgate])
  omega

lemma run_append_gate (p s : List Gate) (x : List Bool) (j : ℕ) (hj : j < s.length)
    (hback : ∀ w ∈ s[j].inputs, w < x.length + p.length + j) :
    (run (p ++ s) x).getD (x.length + p.length + j) false =
      s[j].op.eval (s[j].inputs.map fun w => (run (p ++ s) x).getD w false) := by
  have h := run_gate (p ++ s) x (p.length + j) (by simp; omega)
  rw [append_get p s j hj] at h
  rw [show x.length + p.length + j = x.length + (p.length + j) by omega, h]
  congr 1
  apply List.map_congr_left
  intro w hw
  exact if_pos (by have := hback w hw; omega)

def LocalSim (R : Bool → Bool → Prop) (oldP newP s : List Gate)
    (f : ℕ → ℕ → ℕ) (x : List Bool) : Prop :=
  ∀ j (hj : j < s.length) (u v : ℕ → Bool),
    (∀ w < x.length + oldP.length, u w = (run oldP x).getD w false) →
    (∀ w < x.length + newP.length, v w = (run newP x).getD w false) →
    (∀ i < j, R (u (x.length + oldP.length + i)) (v (x.length + newP.length + i))) →
    R (s[j].op.eval (s[j].inputs.map u))
      (s[j].op.eval (s[j].inputs.map fun w => v (f j w)))

lemma block_transfer (oldP newP s : List Gate) (f : ℕ → ℕ → ℕ)
    (x : List Bool) (R : Bool → Bool → Prop)
    (hold : ∀ j (hj : j < s.length), ∀ w ∈ s[j].inputs,
      w < x.length + oldP.length + j)
    (hnew : ∀ j (hj : j < s.length), ∀ w ∈ s[j].inputs,
      f j w < x.length + newP.length + j)
    (hlocal : LocalSim R oldP newP s f x) :
    ∀ j < s.length,
      R ((run (oldP ++ s) x).getD (x.length + oldP.length + j) false)
        ((run (newP ++ remapSuffix s f) x).getD (x.length + newP.length + j) false) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hR := hlocal j hj
      (fun w => (run (oldP ++ s) x).getD w false)
      (fun w => (run (newP ++ remapSuffix s f) x).getD w false)
      (fun w hw => run_prefix oldP s x w hw)
      (fun w hw => run_prefix newP (remapSuffix s f) x w hw)
      (fun i hi => ih i hi (by omega))
    have hj' : j < (remapSuffix s f).length := by simpa [remapSuffix_length] using hj
    have hback' : ∀ w ∈ (remapSuffix s f)[j].inputs,
        w < x.length + newP.length + j := by
      rw [remapSuffix_get s f j hj]
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact hnew j hj v hv
    rw [run_append_gate oldP s x j hj (hold j hj),
      run_append_gate newP (remapSuffix s f) x j hj' hback', remapSuffix_get s f j hj]
    simpa only [List.map_map, Function.comp_def] using hR

def replaceBlock (n : ℕ) (p oldRegion newRegion s : List Gate)
    (f : ℕ → ℕ → ℕ) (j : ℕ) : Circuit :=
  ⟨(p ++ newRegion) ++ remapSuffix s f, n + (p ++ newRegion).length + j⟩

lemma replaceBlock_size (n : ℕ) (p oldRegion newRegion s : List Gate)
    (f : ℕ → ℕ → ℕ) (j : ℕ) :
    (replaceBlock n p oldRegion newRegion s f j).size =
      p.length + newRegion.length + s.length := by
  simp [replaceBlock, Circuit.size, remapSuffix_length, Nat.add_assoc]

lemma replaceBlock_shorter (n : ℕ) (p oldRegion newRegion s : List Gate)
    (f : ℕ → ℕ → ℕ) (j : ℕ) (hshort : newRegion.length < oldRegion.length) :
    (replaceBlock n p oldRegion newRegion s f j).size <
      (⟨(p ++ oldRegion) ++ s, n + (p ++ oldRegion).length + j⟩ : Circuit).size := by
  rw [replaceBlock_size]
  simp only [Circuit.size, List.length_append]
  omega

lemma replaceBlock_ao (n : ℕ) (p oldRegion newRegion s : List Gate)
    (f : ℕ → ℕ → ℕ) (j : ℕ)
    (hold : TopForm.IsAO2 n ⟨(p ++ oldRegion) ++ s, n + (p ++ oldRegion).length + j⟩)
    (hprefix : Ok n (p ++ newRegion))
    (hf : ∀ k (hk : k < s.length), ∀ w ∈ s[k].inputs,
      f k w < n + (p ++ newRegion).length + k) :
    TopForm.IsAO2 n (replaceBlock n p oldRegion newRegion s f j) := by
  apply ok_ao
  apply remapSuffix_ok n (p ++ newRegion) s f hprefix
  · exact ao_grammar _ hold (p ++ oldRegion) s rfl
  · exact hf

lemma replaceBlock_eval (n : ℕ) (p oldRegion newRegion s : List Gate)
    (f : ℕ → ℕ → ℕ) (j : ℕ) (hj : j < s.length)
    (hold : TopForm.IsAO2 n ⟨(p ++ oldRegion) ++ s, n + (p ++ oldRegion).length + j⟩)
    (hf : ∀ k (hk : k < s.length), ∀ w ∈ s[k].inputs,
      f k w < n + (p ++ newRegion).length + k)
    (x : List Bool) (hx : x.length = n) (R : Bool → Bool → Prop)
    (hlocal : LocalSim R (p ++ oldRegion) (p ++ newRegion) s f x) :
    R ((⟨(p ++ oldRegion) ++ s, n + (p ++ oldRegion).length + j⟩ : Circuit).eval x)
      ((replaceBlock n p oldRegion newRegion s f j).eval x) := by
  have hb := ao_suffix_back _ hold (p ++ oldRegion) s rfl
  have h := block_transfer (p ++ oldRegion) (p ++ newRegion) s f x R
    (by simpa only [hx] using hb) (by simpa only [hx] using hf) hlocal j hj
  simpa only [hx, replaceBlock, Circuit.eval, Circuit.wires, run] using h

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

lemma run_mono (n : ℕ) (gs : List Gate) (hgs : Ok n gs)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ i < n, x.getD i false = true → y.getD i false = true) :
    ∀ w < n + gs.length,
      (run gs x).getD w false = true → (run gs y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw htrue
    by_cases hin : w < n
    · rw [run_input gs x w (by omega)] at htrue
      rw [run_input gs y w (by omega)]
      exact hxy w hin htrue
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < gs.length := by omega
    obtain ⟨o, a, b, hg, hop, ha, hb⟩ := hgs j hj
    have rx := run_gate gs x j hj
    have ry := run_gate gs y j hj
    rw [hx, hg] at rx
    rw [hy, hg] at ry
    simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb] at rx ry
    rw [rx] at htrue
    rw [ry]
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, Bool.and_eq_true] at htrue ⊢
      exact ⟨ih a ha (by omega) htrue.1, ih b hb (by omega) htrue.2⟩
    · simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq,
        Bool.or_false, Bool.or_eq_true] at htrue ⊢
      rcases htrue with h | h
      · exact Or.inl (ih a ha (by omega) h)
      · exact Or.inr (ih b hb (by omega) h)

lemma eval_mono {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro hx
  by_cases hout : C.output < n + C.gates.length
  · exact run_mono n C.gates (ao_ok C hC) (List.ofFn x) (List.ofFn y)
      (by simp) (by simp) (by
        intro i hi hxi
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          dif_pos hi, Option.getD_some] using hxy ⟨i, hi⟩ (by
            simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
              dif_pos hi, Option.getD_some] using hxi)) C.output hout hx
  · have hfalse : C.eval (List.ofFn x) = false := by
      change (run C.gates (List.ofFn x)).getD C.output false = false
      exact List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
    rw [hfalse] at hx
    cases hx

lemma graphFun_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma least_block_contradiction (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p oldRegion newRegion s : List Gate) (f : ℕ → ℕ → ℕ) (j : ℕ) (hj : j < s.length)
    (hL : TopForm.IsLeastAO G
      ⟨(p ++ oldRegion) ++ s, n + (p ++ oldRegion).length + j⟩)
    (hprefix : TopForm.IsAO2 n ⟨p ++ newRegion, 0⟩)
    (hf : ∀ k (hk : k < s.length), ∀ w ∈ s[k].inputs,
      f k w < n + (p ++ newRegion).length + k)
    (hshort : newRegion.length < oldRegion.length)
    (hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      LocalSim (fun old new => new = true → old = true)
        (p ++ oldRegion) (p ++ newRegion) s f (List.ofFn x))
    (hedge : ∀ u v : Fin n, G.Adj u v →
      LocalSim (fun old new => old = true → new = true)
        (p ++ oldRegion) (p ++ newRegion) s f
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))) : False := by
  let D := replaceBlock n p oldRegion newRegion s f j
  have hAO : TopForm.IsAO2 n D :=
    replaceBlock_ao n p oldRegion newRegion s f j hL.1 (ao_ok _ hprefix) hf
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hDx
      cases hxF : graphFun G ∅ x with
      | true => rfl
      | false =>
        have hs := replaceBlock_eval n p oldRegion newRegion s f j hj hL.1 hf
          (List.ofFn x) (by simp) (fun old new => new = true → old = true)
          (hnegative x hxF)
        have hold := hs hDx
        change circuitFun n _ x = true at hold
        rw [hL.2.1, hxF] at hold
        cases hold
    · intro hxF
      obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_true G x).mp hxF
      have hpair : D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = true := by
        have hs := replaceBlock_eval n p oldRegion newRegion s f j hj hL.1 hf
          (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (by simp)
          (fun old new => old = true → new = true) (hedge u v huv)
        apply hs
        change circuitFun n _ (PEqualNP.EdgeOwnership.pairInput u v) = true
        rw [hL.2.1]
        exact (graphFun_true G _).mpr ⟨u, v, huv,
          by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩
      apply eval_mono D hAO (PEqualNP.EdgeOwnership.pairInput u v) x ?_ hpair
      intro i hi
      have hi' : i = u ∨ i = v := by simpa [PEqualNP.EdgeOwnership.pairInput] using hi
      rcases hi' with rfl | rfl <;> assumption
  have hmin := hL.2.2 D hAO hDF
  have hsize := replaceBlock_shorter n p oldRegion newRegion s f j hshort
  change D.size < _ at hsize
  omega

end Region

namespace Reorder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma wireMap_inverse_valid {n N : ℕ} (p : Equiv.Perm (Fin N)) (w : ℕ) (hw : w < n + N) :
    wireMap n N p.symm (wireMap n N p w) = w := by
  by_cases hn : w < n
  · rw [wireMap_input p w hn, wireMap_input p.symm w hn]
  · let j : Fin N := ⟨w - n, by omega⟩
    have heq : n + j.val = w := by dsimp [j]; omega
    rw [← heq, wireMap_gate, wireMap_gate, p.symm_apply_apply]

lemma wireMap_injective_valid {n N : ℕ} (p : Equiv.Perm (Fin N))
    (u v : ℕ) (hu : u < n + N) (hv : v < n + N)
    (heq : wireMap n N p u = wireMap n N p v) : u = v := by
  have h := congrArg (wireMap n N p.symm) heq
  rwa [wireMap_inverse_valid p u hu, wireMap_inverse_valid p v hv] at h

lemma wireMap_image_card {n N : ℕ} (p : Equiv.Perm (Fin N)) (S : Finset ℕ)
    (hS : ∀ w ∈ S, w < n + N) : (S.image (wireMap n N p)).card = S.card := by
  apply Finset.card_image_iff.mpr
  intro u hu v hv heq
  exact wireMap_injective_valid p u v (hS u hu) (hS v hv) heq

lemma wireMap_image_inter {n N : ℕ} (p : Equiv.Perm (Fin N)) (S T : Finset ℕ)
    (hS : ∀ w ∈ S, w < n + N) (hT : ∀ w ∈ T, w < n + N) :
    S.image (wireMap n N p) ∩ T.image (wireMap n N p) = (S ∩ T).image (wireMap n N p) := by
  ext w
  constructor
  · intro hw
    obtain ⟨hs, ht⟩ := Finset.mem_inter.mp hw
    obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hs
    obtain ⟨b, hb, hbw⟩ := Finset.mem_image.mp ht
    have hab := wireMap_injective_valid p a b (hS a ha) (hT b hb) (haw.trans hbw.symm)
    subst b
    exact Finset.mem_image.mpr ⟨a, Finset.mem_inter.mpr ⟨ha, hb⟩, haw⟩
  · intro hw
    obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hw
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨a, (Finset.mem_inter.mp ha).1, haw⟩,
      Finset.mem_image.mpr ⟨a, (Finset.mem_inter.mp ha).2, haw⟩⟩

lemma wireMap_prefix_iff {n N : ℕ} (p : Equiv.Perm (Fin N)) (S : Finset (Fin N))
    (hp : ∀ j : Fin N, (p j).val < S.card ↔ j ∈ S) (w : ℕ) (hw : w < n + N) :
    wireMap n N p w < n + S.card ↔ w < n ∨ ∃ j ∈ S, w = n + j.val := by
  by_cases hn : w < n
  · rw [wireMap_input p w hn]
    constructor
    · intro _; exact Or.inl hn
    · intro _; omega
  · let j : Fin N := ⟨w - n, by omega⟩
    have heq : n + j.val = w := by dsimp [j]; omega
    rw [← heq, wireMap_gate]
    constructor
    · intro h
      exact Or.inr ⟨j, (hp j).mp (by omega), rfl⟩
    · rintro (h | ⟨k, hk, hkj⟩)
      · omega
      · have hkj' : k = j := Fin.ext (by omega)
        subst k
        have h := (hp j).mpr hk
        omega

lemma wireMap_two_closed_small_iff {n N : ℕ} (P K : Finset (Fin N))
    (w : ℕ) (hw : w < n + N) :
    wireMap n N (sortPerm (blockKey P K)) w < n + P.card ↔
      w < n ∨ ∃ j ∈ P, w = n + j.val := by
  exact wireMap_prefix_iff _ P (two_closed_hoist_prefix_small P K) w hw

lemma wireMap_two_closed_large_iff {n N : ℕ} (P K : Finset (Fin N)) (hPK : P ⊆ K)
    (w : ℕ) (hw : w < n + N) :
    wireMap n N (sortPerm (blockKey P K)) w < n + K.card ↔
      w < n ∨ ∃ j ∈ K, w = n + j.val := by
  exact wireMap_prefix_iff _ K (two_closed_hoist_prefix_large P K hPK) w hw

lemma two_closed_hoist_output_suffix {n : ℕ} (C : Circuit)
    (P K : Finset (Fin C.gates.length)) (hPK : P ⊆ K)
    (houtLo : n ≤ C.output) (houtHi : C.output < n + C.gates.length)
    (houtK : ∀ j ∈ K, n + j.val ≠ C.output) :
    ∃ j < C.gates.length - K.card,
      (permute n C (sortPerm (blockKey P K))).output = n + K.card + j := by
  let q : Fin C.gates.length := ⟨C.output - n, by omega⟩
  have hq : n + q.val = C.output := by dsimp [q]; omega
  have hqK : q ∉ K := fun h => houtK q h hq
  have hge : K.card ≤ (sortPerm (blockKey P K) q).val := by
    by_contra h
    exact hqK ((two_closed_hoist_prefix_large P K hPK q).mp (by omega))
  have hlt := (sortPerm (blockKey P K) q).isLt
  refine ⟨(sortPerm (blockKey P K) q).val - K.card, by omega, ?_⟩
  change wireMap n C.gates.length (sortPerm (blockKey P K)) C.output = _
  rw [← hq, wireMap_gate]
  omega

end Reorder

namespace BoundaryColors

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open ColorProjection

noncomputable def color {n : ℕ} (A : ℕ → Finset (Fin n)) (s : Fin n → Bool)
    (w : ℕ) : Bool :=
  if h : ∃ c : Bool, ∀ i ∈ A w, s i = c then Classical.choose h else false

lemma color_spec {n : ℕ} (A : ℕ → Finset (Fin n)) (s : Fin n → Bool)
    (w : ℕ) (h : ∃ c : Bool, ∀ i ∈ A w, s i = c) :
    ∀ i ∈ A w, s i = color A s w := by
  simp only [color, dif_pos h]
  exact Classical.choose_spec h

lemma setOr_ext {n : ℕ} (A B : Finset (Fin n))
    (h : ∀ x : Fin n → Bool, setOr A x = setOr B x) : A = B := by
  ext i
  have hi := congrArg (fun b : Bool => b = true) (h (pairInput i i))
  simpa [setOr, pairInput] using hi

lemma support_union_eq {n : ℕ} (S : Finset ℕ) (A : ℕ → Finset (Fin n))
    (T : Finset (Fin n)) (V : ℕ → (Fin n → Bool) → Bool)
    (hV : ∀ w ∈ S, ∀ x : Fin n → Bool, V w x = setOr (A w) x)
    (hsem : ∀ x : Fin n → Bool,
      decide (∃ w ∈ S, V w x = true) = setOr T x) : S.biUnion A = T := by
  apply setOr_ext
  intro x
  rw [← hsem x]
  apply Bool.eq_iff_iff.mpr
  simp only [setOr, decide_eq_true_eq, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, ⟨w, hw, hi⟩, hx⟩
    exact ⟨w, hw, (hV w hw x).trans (decide_eq_true ⟨i, hi, hx⟩)⟩
  · rintro ⟨w, hw, hv⟩
    rw [hV w hw x] at hv
    obtain ⟨i, hi, hx⟩ := of_decide_eq_true hv
    exact ⟨i, ⟨w, hw, hi⟩, hx⟩

lemma source_each_color {n : ℕ} (S : Finset ℕ) (A : ℕ → Finset (Fin n))
    (T : Finset (Fin n)) (s : Fin n → Bool)
    (hmono : ∀ w ∈ S, ∃ c : Bool, ∀ i ∈ A w, s i = c)
    (hunion : S.biUnion A = T)
    (hmixed : ¬ ∃ c : Bool, ∀ i ∈ T, s i = c) (c : Bool) :
    ∃ w ∈ S, color A s w = c := by
  by_contra hnone
  apply hmixed
  refine ⟨!c, ?_⟩
  intro i hi
  rw [← hunion] at hi
  obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
  have hne : color A s w ≠ c := fun hc => hnone ⟨w, hw, hc⟩
  have hc : color A s w = !c := by
    cases hcw : color A s w <;> cases c <;> simp_all
  exact (color_spec A s w (hmono w hw) i hiw).trans hc

lemma source_projection_semantics {n : ℕ} (S : Finset ℕ)
    (A : ℕ → Finset (Fin n)) (T : Finset (Fin n)) (s : Fin n → Bool)
    (V : ℕ → Bool) (x : Fin n → Bool)
    (hmono : ∀ w ∈ S, ∃ c : Bool, ∀ i ∈ A w, s i = c)
    (hunion : S.biUnion A = T)
    (hV : ∀ w ∈ S, V w = setOr (A w) x) (c : Bool) :
    decide (∃ w ∈ S.filter (fun w => color A s w = c), V w = true) =
      setOr (project T s c) x := by
  rw [← hunion]
  exact source_projection_eq S A (color A s) s c x V hV
    (fun w hw => color_spec A s w (hmono w hw))

lemma product_project_decreases {n : ℕ} (A B : Finset (Fin n))
    (s : Fin n → Bool) (c : Bool) (x : Fin n → Bool) :
    (setOr A x && setOr (project B s c) x) = true →
      (setOr A x && setOr B x) = true := by
  simp only [Bool.and_eq_true]
  exact fun h => ⟨h.1, project_le B s c x h.2⟩

lemma product_projection_boundary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (s : Fin n → Bool) (c : Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hA : ∀ a ∈ A, s a = c) (hdis : Disjoint A B) :
    (∀ x : Fin n → Bool, (setOr A x && setOr (project B s (!c)) x) = true →
      (setOr A x && setOr B x) = true) ∧
    (∀ u v, G.Adj u v →
      (setOr A (pairInput u v) && setOr B (pairInput u v)) = true →
      (setOr A (pairInput u v) && setOr (project B s (!c)) (pairInput u v)) = true) := by
  refine ⟨fun x => product_project_decreases A B s (!c) x, ?_⟩
  intro u v huv ht
  rwa [product_project_pair A B s c hA hdis u v (hbip u v huv)]

end BoundaryColors

namespace OutputSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open MixedFrontier MixedReach MixedCut

lemma graphFun_diagonal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i : Fin n) : graphFun G ∅ (pairInput i i) = false := by
  simp [graphFun, pairInput]

lemma output_orIn_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) :
    orIn n C C.output = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hv := orIn_val C (pairInput i i) C.output i hi (by simp [pairInput])
  change circuitFun n C (pairInput i i) = true at hv
  rw [hF, graphFun_diagonal] at hv
  contradiction

lemma output_not_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) : n ≤ C.output := by
  by_contra h
  have hraw : C.output < n := by omega
  have hi : (⟨C.output, hraw⟩ : Fin n) ∈ orIn n C C.output :=
    (orIn_mem n C C.output _).mpr (Or.inl rfl)
  rw [output_orIn_empty G C hF] at hi
  exact Finset.notMem_empty _ hi

lemma region_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (k : ℕ) (hk : k ∈ region n C g h) : n + k ≠ C.output := by
  intro heq
  have hne := region_support_nonempty G C hAO hT g h hpair hgh hhg k hk
  rw [heq, output_orIn_empty G C hF] at hne
  exact Finset.not_nonempty_empty hne

end OutputSupport

namespace TwoOrBuild

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma circuit_output_valid_of_true {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (htrue : circuitFun n C x = true) : C.output < n + C.gates.length := by
  by_contra h
  have hout : (run C.gates (List.ofFn x)).length ≤ C.output := by
    rw [run_length, List.length_ofFn]
    omega
  have hfalse : circuitFun n C x = false := List.getD_eq_default _ _ hout
  rw [hfalse] at htrue
  contradiction

lemma sourceOr_all_true {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (S : Finset ℕ) (hS : ∀ w ∈ S, w < n + C.gates.length)
    (hne : S.Nonempty) : sourceOr C.gates (List.ofFn (fun _ : Fin n => true)) S = true := by
  obtain ⟨w, hw⟩ := hne
  apply decide_eq_true
  exact ⟨w, hw, MixedFrontier.W_all_true C hC w (hS w hw)⟩

lemma two_color_projection_circuits_valid (n : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (color : ℕ → Bool) (c d : Bool) (S T : Finset ℕ)
    (hS : ∀ w ∈ S, w < n + C.gates.length) (hT : ∀ w ∈ T, w < n + C.gates.length)
    (hSmixed : HasBoth color S) (hTmixed : HasBoth color T) :
    ∃ (hs : List Gate) (wS wT : ℕ),
      PEqualNP.TopForm.IsAO2 n ⟨C.gates ++ hs, wS⟩ ∧
      PEqualNP.TopForm.IsAO2 n ⟨C.gates ++ hs, wT⟩ ∧
      (∀ g ∈ hs, g.op = GateOp.or) ∧ hs.length < pairCost S T ∧
      wS < n + (C.gates ++ hs).length ∧ wT < n + (C.gates ++ hs).length ∧
      ∀ x : Fin n → Bool,
        circuitFun n ⟨C.gates ++ hs, wS⟩ x = sourceOr C.gates (List.ofFn x) (projectColor color c S) ∧
        circuitFun n ⟨C.gates ++ hs, wT⟩ x = sourceOr C.gates (List.ofFn x) (projectColor color d T) := by
  obtain ⟨hs, wS, wT, hAO1, hAO2, hops, hlen, heval⟩ :=
    two_color_projection_circuits n C hC color c d S T hS hT hSmixed hTmixed
  have hall := heval (fun _ => true)
  have htrueS : circuitFun n ⟨C.gates ++ hs, wS⟩ (fun _ => true) = true := by
    rw [hall.1]
    exact sourceOr_all_true C hC _
      (fun w hw => hS w (project_subset color c S hw)) (project_nonempty color c S hSmixed)
  have htrueT : circuitFun n ⟨C.gates ++ hs, wT⟩ (fun _ => true) = true := by
    rw [hall.2]
    exact sourceOr_all_true C hC _
      (fun w hw => hT w (project_subset color d T hw)) (project_nonempty color d T hTmixed)
  exact ⟨hs, wS, wT, hAO1, hAO2, hops, hlen,
    circuit_output_valid_of_true _ _ htrueS, circuit_output_valid_of_true _ _ htrueT, heval⟩

end TwoOrBuild

namespace ActualCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012
open MixedCut MixedFrontier MixedReach

def wires (n : ℕ) (C : Circuit) (s : Fin n → Bool) (g h : ℕ) : Finset ℕ :=
  (mixedRegion n C s g h).image (fun k => n + k)

def boundary (n : ℕ) (C : Circuit) (s : Fin n → Bool) (g h : ℕ) : Finset ℕ :=
  ((mixedRegion n C s g h).biUnion fun k => (gateAt C k).inputs.toFinset) \
    wires n C s g h

lemma wires_card {n : ℕ} (C : Circuit) (s : Fin n → Bool) (g h : ℕ) :
    (wires n C s g h).card = (mixedRegion n C s g h).card := by
  apply Finset.card_image_iff.mpr
  intro a _ b _ hab
  exact Nat.add_left_cancel hab

lemma boundary_disjoint {n : ℕ} (C : Circuit) (s : Fin n → Bool) (g h : ℕ) :
    Disjoint (boundary n C s g h) (wires n C s g h) := by
  exact Finset.sdiff_disjoint

lemma wires_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g) :
    ∀ w ∈ wires n C s g h, ∃ k < C.gates.length,
      w = n + k ∧ (gateAt C k).op = GateOp.or := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  have hkK := (Finset.mem_sdiff.mp hk).1
  exact ⟨k, ((region_mem C g h k).mp hkK).1, rfl,
    region_only_or G C hAO hT g h hpair hgh hhg k hkK⟩

lemma boundary_parents {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (hAO : IsAO2 n C) (g h : ℕ) :
    ∀ w ∈ wires n C s g h, ∀ b : Fin 2,
      opnd C (w - n) b ∈ boundary n C s g h ∪ wires n C s g h := by
  intro w hw b
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  have hklt := ((region_mem C g h k).mp (Finset.mem_sdiff.mp hk).1).1
  have hinp := operand_mem C hAO k hklt b
  have hmem : opnd C k b ∈ (mixedRegion n C s g h).biUnion
      (fun j => (gateAt C j).inputs.toFinset) :=
    Finset.mem_biUnion.mpr ⟨k, hk, List.mem_toFinset.mpr hinp⟩
  have hsub : (mixedRegion n C s g h).biUnion (fun j => (gateAt C j).inputs.toFinset) ⊆
      boundary n C s g h ∪ wires n C s g h := by
    intro u hu
    by_cases hj : u ∈ wires n C s g h
    · exact Finset.mem_union_right _ hj
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, hj⟩)
  simpa using hsub hmem

lemma boundary_used {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g) :
    ∀ b ∈ boundary n C s g h, ∃ w ∈ wires n C s g h,
      CountCut.cutOrStep n C (wires n C s g h) b w := by
  intro b hb
  obtain ⟨hb, _⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨k, hk, hread⟩ := Finset.mem_biUnion.mp hb
  have hkK := (Finset.mem_sdiff.mp hk).1
  have hklt := ((region_mem C g h k).mp hkK).1
  have hread' := List.mem_toFinset.mp hread
  have hw : n + k ∈ wires n C s g h := Finset.mem_image.mpr ⟨k, hk, rfl⟩
  exact ⟨n + k, hw, ⟨⟨k, hklt, rfl,
    region_only_or G C hAO hT g h hpair hgh hhg k hkK, hread',
    hAO.2.1 k hklt b hread'⟩, hw⟩⟩

lemma boundary_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w : ℕ) (hw : w ∈ boundary n C s g h) :
    (w < n ∨ ∃ k ∈ pureRegion n C s g h, w = n + k) ∧
    (orIn n C w).Nonempty ∧ (∃ c : Bool, ∀ i ∈ orIn n C w, s i = c) ∧
      ∀ x : Fin n → Bool, wireVal n C w x = decide (∃ i ∈ orIn n C w, x i = true) := by
  obtain ⟨hw, hout⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨k, hk, hread⟩ := Finset.mem_biUnion.mp hw
  have hout' : ∀ r ∈ mixedRegion n C s g h, w ≠ n + r := by
    intro r hr heq
    exact hout (Finset.mem_image.mpr ⟨r, hr, heq.symm⟩)
  exact ⟨mixedRegion_boundary_raw_or_pure G C s hAO hT g h hpair hgh hhg k hk w
    (List.mem_toFinset.mp hread) hout',
    mixedRegion_boundary_support G C s hAO hT g h hpair hgh hhg k hk w
    (List.mem_toFinset.mp hread) hout'⟩

lemma wires_forward_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g, h}) :
    ∀ u ∈ wires n C s g h, ∀ v, CountCut.orWireStep n C u v → v ∈ wires n C s g h := by
  intro u hu v hv
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨r, hr, rfl, hrop, hread, _⟩ := hv
  exact Finset.mem_image.mpr ⟨r,
    mixedRegion_or_reader_closed G C s hbip hL hT hJ g h hpair k hk r hr hrop hread, rfl⟩

lemma mixed_wire_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g, h}) (w : ℕ) (hw : w < n + C.gates.length)
    (hmix : ∀ c : Bool, ∃ i ∈ orIn n C w, s i = c) : w ∈ wires n C s g h := by
  have hn : n ≤ w := by
    by_contra hn
    have hpure := raw_or_pure_support_monochromatic C s g h w (Or.inl (by omega))
    exact mixed_not_monochromatic s _ hmix hpure
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hk : k < C.gates.length := by omega
  exact Finset.mem_image.mpr ⟨k, (mixedRegion_mem C s g h k).mpr
    ⟨all_mixed_mem_region G C s hbip hL hT hJ g h hpair k hk hmix, hmix⟩, rfl⟩

lemma wires_two_roots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g, h})
    (hpureg : ∃ c : Bool, ∀ i ∈ side (n := n) C g (1 - bg), s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1 - bh), s i = c) :
    ∀ w ∈ wires n C s g h,
      Relation.ReflTransGen (CountCut.cutOrStep n C (wires n C s g h)) w (opnd C g bg) ∨
      Relation.ReflTransGen (CountCut.cutOrStep n C (wires n C s g h)) w (opnd C h bh) := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  have hmem : n + k ∈ wires n C s g h := Finset.mem_image.mpr ⟨k, hk, rfl⟩
  obtain ⟨hkK, hmix⟩ := (mixedRegion_mem C s g h k).mp hk
  have hklt := ((region_mem C g h k).mp hkK).1
  have hc := wires_forward_closed G C s hbip hL hT hJ g h hpair
  rcases least_mixed_two_operand_coverage G C s hbip hL hT hJ g h bg bh hpair
      hpureg hpureh k hklt hmix with hr | hr
  · exact Or.inl (CountCut.closed_path_is_cutPath n C _ hc hmem
      (CountCut.orReaches_path n C _ k hr)).2
  · exact Or.inr (CountCut.closed_path_is_cutPath n C _ hc hmem
      (CountCut.orReaches_path n C _ k hr)).2

lemma sources_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w : ℕ) (hw : w ∈ wires n C s g h) :
    (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) w).Nonempty := by
  have hJ := wires_or G C s hAO hT g h hpair hgh hhg
  obtain ⟨k, hk, rfl, _⟩ := hJ w hw
  have hv : wireVal n C (n + k) (fun _ => true) = true := W_all_true C hAO _ (by omega)
  obtain ⟨b, hb, _⟩ := (BoundarySources.wire_true_iff_source C hAO _ _ hJ
    (boundary_parents C s hAO g h) (fun _ => true) _ (Finset.mem_union_right _ hw)).mp hv
  exact ⟨b, hb⟩

lemma mixed_operand_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g, h}) (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2)
    (hmix : ∀ c : Bool, ∃ i ∈ side (n := n) C a b, s i = c) :
    opnd C a b ∈ wires n C s g h := by
  have halt := (junk_data G C a ha).1
  have hw := hL.1.2.1 a halt _ (operand_mem C hL.1 a halt b)
  exact mixed_wire_mem G C s hbip hL hT hJ g h hpair _ (by omega) hmix

lemma pairCost_le_mixedRegion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∃ c : Bool, ∀ i ∈ side (n := n) C g (1 - bg), s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1 - bh), s i = c)
    (hmixg : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c) :
    TwoOrBuild.pairCost
      (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C g bg))
      (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C h bh)) ≤
      (mixedRegion n C s g h).card := by
  have hgj : g ∈ junk G C := by rw [hpair]; simp
  have hhj : h ∈ junk G C := by rw [hpair]; simp
  have hrg := mixed_operand_mem G C s hbip hL hT hJ g h hpair g hgj bg hmixg
  have hrh := mixed_operand_mem G C s hbip hL hT hJ g h hpair h hhj bh hmixh
  have hbound := BoundarySources.pairCost_le_gates n C hL.1
    (boundary n C s g h) (wires n C s g h) (boundary_disjoint C s g h)
    (opnd C g bg) (opnd C h bh) hrg hrh
    (boundary_parents C s hL.1 g h)
    (boundary_used G C s hL.1 hT g h hpair hgh hhg)
    (wires_two_roots G C s hbip hL hT hJ g h bg bh hpair hpureg hpureh)
    (sources_nonempty G C s hL.1 hT g h hpair hgh hhg _ hrg)
    (sources_nonempty G C s hL.1 hT g h hpair hgh hhg _ hrh)
  simpa only [wires_card] using hbound

end ActualCut

namespace RegionLocal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5012.Region

lemma gate_eval_imp (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : ℕ → Bool) (h : ∀ w ∈ g.inputs, u w = true → v w = true) :
    g.op.eval (g.inputs.map u) = true → g.op.eval (g.inputs.map v) = true := by
  intro hu
  rcases hop with ho | ho
  · have hu' : ∀ w ∈ g.inputs, u w = true := by
      simpa [ho, GateOp.eval, List.all_eq_true] using hu
    have hv : ∀ w ∈ g.inputs, v w = true := fun w hw => h w hw (hu' w hw)
    simpa [ho, GateOp.eval, List.all_eq_true] using hv
  · obtain ⟨w, hw, hwu⟩ : ∃ w ∈ g.inputs, u w = true := by
      simpa [ho, GateOp.eval, List.any_eq_true] using hu
    have hv : ∃ w ∈ g.inputs, v w = true := ⟨w, hw, h w hw hwu⟩
    simpa [ho, GateOp.eval, List.any_eq_true] using hv

lemma localSim_of_prefix_gate (R : Bool → Bool → Prop) (oldP newP : List Gate)
    (g : Gate) (f : ℕ → ℕ) (x : List Bool) (u v : ℕ → Bool)
    (hOld : ∀ w ∈ g.inputs, w < x.length + oldP.length)
    (hNew : ∀ w ∈ g.inputs, f w < x.length + newP.length)
    (hu : ∀ w < x.length + oldP.length, u w = (run oldP x).getD w false)
    (hv : ∀ w < x.length + newP.length, v w = (run newP x).getD w false)
    (hgate : R (g.op.eval (g.inputs.map fun w => (run oldP x).getD w false))
      (g.op.eval (g.inputs.map fun w => (run newP x).getD (f w) false))) :
    R (g.op.eval (g.inputs.map u)) (g.op.eval (g.inputs.map fun w => v (f w))) := by
  have hmu : g.inputs.map u = g.inputs.map (fun w => (run oldP x).getD w false) :=
    List.map_congr_left (fun w hw => hu w (hOld w hw))
  have hmv : g.inputs.map (fun w => v (f w)) =
      g.inputs.map (fun w => (run newP x).getD (f w) false) :=
    List.map_congr_left (fun w hw => hv (f w) (hNew w hw))
  rwa [hmu, hmv]

lemma localSim_of_targets (R : Bool → Bool → Prop)
    (hrefl : ∀ z : Bool, R z z)
    (hcompat : ∀ (g : Gate), (g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ u v : ℕ → Bool, (∀ w ∈ g.inputs, R (u w) (v w)) →
      R (g.op.eval (g.inputs.map u)) (g.op.eval (g.inputs.map v)))
    (p q r s : List Gate) (f : ℕ → ℕ → ℕ) (x : List Bool) (targets : Finset ℕ)
    (hops : ∀ k (hk : k < s.length), s[k].op = GateOp.and ∨ s[k].op = GateOp.or)
    (hback : ∀ k (hk : k < s.length), ∀ w ∈ s[k].inputs,
      w < x.length + (p ++ q).length + k)
    (hkeep : ∀ k w, w < x.length + p.length → f k w = w)
    (hshift : ∀ k w, x.length + (p ++ q).length ≤ w →
      f k w = x.length + (p ++ r).length + (w - (x.length + (p ++ q).length)))
    (hordinary : ∀ k (hk : k < s.length), k ∉ targets → ∀ w ∈ s[k].inputs,
      w < x.length + p.length ∨ x.length + (p ++ q).length ≤ w)
    (htOld : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs,
      w < x.length + (p ++ q).length)
    (htNew : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs,
      f k w < x.length + (p ++ r).length)
    (htarget : ∀ k (hk : k < s.length), k ∈ targets →
      R (s[k].op.eval (s[k].inputs.map fun w => (run (p ++ q) x).getD w false))
        (s[k].op.eval (s[k].inputs.map fun w => (run (p ++ r) x).getD (f k w) false))) :
    LocalSim R (p ++ q) (p ++ r) s f x := by
  classical
  intro k hk u v hu hv hprevious
  by_cases hkt : k ∈ targets
  · exact localSim_of_prefix_gate R (p ++ q) (p ++ r) s[k] (f k) x u v
      (htOld k hk hkt) (htNew k hk hkt) hu hv (htarget k hk hkt)
  · apply hcompat s[k] (hops k hk) u (fun w => v (f k w))
    intro w hw
    rcases hordinary k hk hkt w hw with hp | hs
    · have hpo : w < x.length + (p ++ q).length := by simp only [List.length_append]; omega
      have hpn : w < x.length + (p ++ r).length := by simp only [List.length_append]; omega
      rw [hkeep k w hp, hu w hpo, hv w hpn,
        run_prefix p q x w hp, run_prefix p r x w hp]
      exact hrefl _
    · have hi : w - (x.length + (p ++ q).length) < k := by
        have := hback k hk w hw
        omega
      have hprev := hprevious _ hi
      rw [hshift k w hs]
      have heq : x.length + (p ++ q).length + (w - (x.length + (p ++ q).length)) = w := by omega
      rwa [heq] at hprev

lemma localSim_forward_of_targets (p q r s : List Gate) (f : ℕ → ℕ → ℕ)
    (x : List Bool) (targets : Finset ℕ)
    (hops : ∀ k (hk : k < s.length), s[k].op = GateOp.and ∨ s[k].op = GateOp.or)
    (hback : ∀ k (hk : k < s.length), ∀ w ∈ s[k].inputs, w < x.length + (p ++ q).length + k)
    (hkeep : ∀ k w, w < x.length + p.length → f k w = w)
    (hshift : ∀ k w, x.length + (p ++ q).length ≤ w →
      f k w = x.length + (p ++ r).length + (w - (x.length + (p ++ q).length)))
    (hordinary : ∀ k (hk : k < s.length), k ∉ targets → ∀ w ∈ s[k].inputs,
      w < x.length + p.length ∨ x.length + (p ++ q).length ≤ w)
    (htOld : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs, w < x.length + (p ++ q).length)
    (htNew : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs, f k w < x.length + (p ++ r).length)
    (htarget : ∀ k (hk : k < s.length), k ∈ targets →
      s[k].op.eval (s[k].inputs.map fun w => (run (p ++ q) x).getD w false) = true →
        s[k].op.eval (s[k].inputs.map fun w => (run (p ++ r) x).getD (f k w) false) = true) :
    LocalSim (fun old new => old = true → new = true) (p ++ q) (p ++ r) s f x :=
  localSim_of_targets _ (fun _ h => h) gate_eval_imp p q r s f x targets
    hops hback hkeep hshift hordinary htOld htNew htarget

lemma localSim_reverse_of_targets (p q r s : List Gate) (f : ℕ → ℕ → ℕ)
    (x : List Bool) (targets : Finset ℕ)
    (hops : ∀ k (hk : k < s.length), s[k].op = GateOp.and ∨ s[k].op = GateOp.or)
    (hback : ∀ k (hk : k < s.length), ∀ w ∈ s[k].inputs, w < x.length + (p ++ q).length + k)
    (hkeep : ∀ k w, w < x.length + p.length → f k w = w)
    (hshift : ∀ k w, x.length + (p ++ q).length ≤ w →
      f k w = x.length + (p ++ r).length + (w - (x.length + (p ++ q).length)))
    (hordinary : ∀ k (hk : k < s.length), k ∉ targets → ∀ w ∈ s[k].inputs,
      w < x.length + p.length ∨ x.length + (p ++ q).length ≤ w)
    (htOld : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs, w < x.length + (p ++ q).length)
    (htNew : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs, f k w < x.length + (p ++ r).length)
    (htarget : ∀ k (hk : k < s.length), k ∈ targets →
      s[k].op.eval (s[k].inputs.map fun w => (run (p ++ r) x).getD (f k w) false) = true →
        s[k].op.eval (s[k].inputs.map fun w => (run (p ++ q) x).getD w false) = true) :
    LocalSim (fun old new => new = true → old = true) (p ++ q) (p ++ r) s f x :=
  localSim_of_targets _ (fun _ h => h)
    (fun g ho u v h => gate_eval_imp g ho v u h) p q r s f x targets
    hops hback hkeep hshift hordinary htOld htNew htarget

def blockMap (n : ℕ) (p q r : List Gate) (targetWire : ℕ → ℕ) (k w : ℕ) : ℕ :=
  if w < n + p.length then w
  else if n + (p ++ q).length ≤ w then
    n + (p ++ r).length + (w - (n + (p ++ q).length))
  else targetWire k

lemma blockMap_keep (n : ℕ) (p q r : List Gate) (targetWire : ℕ → ℕ) :
    ∀ k w, w < n + p.length → blockMap n p q r targetWire k w = w := by
  intro k w hw
  simp only [blockMap, if_pos hw]

lemma blockMap_shift (n : ℕ) (p q r : List Gate) (targetWire : ℕ → ℕ) :
    ∀ k w, n + (p ++ q).length ≤ w → blockMap n p q r targetWire k w =
      n + (p ++ r).length + (w - (n + (p ++ q).length)) := by
  intro k w hw
  have hnot : ¬ w < n + p.length := by simp only [List.length_append] at hw; omega
  simp only [blockMap, if_neg hnot, if_pos hw]

lemma blockMap_region (n : ℕ) (p q r : List Gate) (targetWire : ℕ → ℕ)
    (k w : ℕ) (hlo : n + p.length ≤ w) (hhi : w < n + (p ++ q).length) :
    blockMap n p q r targetWire k w = targetWire k := by
  have hnot : ¬ w < n + p.length := by omega
  have hnot' : ¬ n + (p ++ q).length ≤ w := by omega
  simp only [blockMap, if_neg hnot, if_neg hnot']

lemma blockMap_prefix_bound (n : ℕ) (p q r : List Gate) (targetWire : ℕ → ℕ)
    (k w : ℕ) (hw : w < n + (p ++ q).length)
    (ht : targetWire k < n + (p ++ r).length) :
    blockMap n p q r targetWire k w < n + (p ++ r).length := by
  by_cases hp : w < n + p.length
  · rw [blockMap_keep n p q r targetWire k w hp]
    simp only [List.length_append]
    omega
  · rw [blockMap_region n p q r targetWire k w (by omega) hw]
    exact ht

lemma blockMap_back (n : ℕ) (p q r s : List Gate) (targetWire : ℕ → ℕ)
    (targets : Finset ℕ)
    (hback : ∀ k (hk : k < s.length), ∀ w ∈ s[k].inputs, w < n + (p ++ q).length + k)
    (hordinary : ∀ k (hk : k < s.length), k ∉ targets → ∀ w ∈ s[k].inputs,
      w < n + p.length ∨ n + (p ++ q).length ≤ w)
    (hroot : ∀ k ∈ targets, targetWire k < n + (p ++ r).length) :
    ∀ k (hk : k < s.length), ∀ w ∈ s[k].inputs,
      blockMap n p q r targetWire k w < n + (p ++ r).length + k := by
  intro k hk w hw
  by_cases hp : w < n + p.length
  · rw [blockMap_keep n p q r targetWire k w hp]
    simp only [List.length_append]
    omega
  · by_cases hs : n + (p ++ q).length ≤ w
    · rw [blockMap_shift n p q r targetWire k w hs]
      have := hback k hk w hw
      omega
    · have hkt : k ∈ targets := by
        by_contra hnot
        exact (hordinary k hk hnot w hw).elim hp hs
      rw [blockMap_region n p q r targetWire k w (by omega) (by omega)]
      have := hroot k hkt
      omega

lemma least_block_with_targets (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p q r s : List Gate) (targetWire : ℕ → ℕ) (targets : Finset ℕ)
    (j : ℕ) (hj : j < s.length)
    (hL : TopForm.IsLeastAO G ⟨(p ++ q) ++ s, n + (p ++ q).length + j⟩)
    (hprefix : TopForm.IsAO2 n ⟨p ++ r, 0⟩)
    (hshort : r.length < q.length)
    (hroot : ∀ k ∈ targets, targetWire k < n + (p ++ r).length)
    (hordinary : ∀ k (hk : k < s.length), k ∉ targets → ∀ w ∈ s[k].inputs,
      w < n + p.length ∨ n + (p ++ q).length ≤ w)
    (htOld : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs,
      w < n + (p ++ q).length)
    (hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      ∀ k (hk : k < s.length), k ∈ targets →
      s[k].op.eval (s[k].inputs.map fun w =>
        (run (p ++ r) (List.ofFn x)).getD (blockMap n p q r targetWire k w) false) = true →
      s[k].op.eval (s[k].inputs.map fun w => (run (p ++ q) (List.ofFn x)).getD w false) = true)
    (hedge : ∀ u v : Fin n, G.Adj u v → ∀ k (hk : k < s.length), k ∈ targets →
      s[k].op.eval (s[k].inputs.map fun w =>
        (run (p ++ q) (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD w false) = true →
      s[k].op.eval (s[k].inputs.map fun w =>
        (run (p ++ r) (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD
          (blockMap n p q r targetWire k w) false) = true) : False := by
  have hb := ao_suffix_back _ hL.1 (p ++ q) s rfl
  have hops : ∀ k (hk : k < s.length), s[k].op = GateOp.and ∨ s[k].op = GateOp.or := by
    intro k hk
    obtain ⟨o, a, b, heq, hop⟩ := ao_grammar _ hL.1 (p ++ q) s rfl k hk
    simpa only [heq] using hop
  have htNew : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs,
      blockMap n p q r targetWire k w < n + (p ++ r).length := by
    intro k hk hkt w hw
    exact blockMap_prefix_bound n p q r targetWire k w (htOld k hk hkt w hw) (hroot k hkt)
  apply least_block_contradiction n G p q r s (blockMap n p q r targetWire) j hj hL hprefix
    (blockMap_back n p q r s targetWire targets hb hordinary hroot) hshort
  · intro x hx
    apply localSim_reverse_of_targets p q r s (blockMap n p q r targetWire) (List.ofFn x)
      targets hops
      (by simpa only [List.length_ofFn] using hb)
      (by simpa only [List.length_ofFn] using blockMap_keep n p q r targetWire)
      (by simpa only [List.length_ofFn] using blockMap_shift n p q r targetWire)
      (by simpa only [List.length_ofFn] using hordinary)
      (by simpa only [List.length_ofFn] using htOld)
      (by simpa only [List.length_ofFn] using htNew)
    exact hnegative x hx
  · intro u v huv
    apply localSim_forward_of_targets p q r s (blockMap n p q r targetWire)
      (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) targets hops
      (by simpa only [List.length_ofFn] using hb)
      (by simpa only [List.length_ofFn] using blockMap_keep n p q r targetWire)
      (by simpa only [List.length_ofFn] using blockMap_shift n p q r targetWire)
      (by simpa only [List.length_ofFn] using hordinary)
      (by simpa only [List.length_ofFn] using htOld)
      (by simpa only [List.length_ofFn] using htNew)
    exact hedge u v huv

end RegionLocal

namespace HoistTransport
open PEqualNP.EdgeOwnership
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Reorder TwoOrBuild

def boundedSet (N : ℕ) (S : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.val ∈ S)

lemma boundedSet_mem (N : ℕ) (S : Finset ℕ) (i : Fin N) :
    i ∈ boundedSet N S ↔ i.val ∈ S := by simp [boundedSet]

lemma boundedSet_card (N : ℕ) (S : Finset ℕ) (hS : ∀ i ∈ S, i < N) :
    (boundedSet N S).card = S.card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi; exact (boundedSet_mem N S i).mp hi
  · intro i hi j hj hij; exact Fin.ext hij
  · intro i hi; exact ⟨⟨i, hS i hi⟩, (boundedSet_mem N S _).mpr hi, rfl⟩

lemma boundedSet_subset {N : ℕ} {S T : Finset ℕ} (h : S ⊆ T) :
    boundedSet N S ⊆ boundedSet N T := by
  intro i hi; exact (boundedSet_mem _ _ _).mpr (h ((boundedSet_mem _ _ _).mp hi))

lemma boundedSet_closed {n : ℕ} (C : Circuit) (S : Finset ℕ)
    (hS : ∀ k ∈ S, ∀ r, n + r ∈ (gateAt C k).inputs → r ∈ S) :
    Reorder.PredecessorClosed n C (boundedSet C.gates.length S) := by
  intro i j hj hdep
  exact (boundedSet_mem _ _ _).mpr (hS j.val ((boundedSet_mem _ _ _).mp hj) i.val hdep)

lemma pairCost_image {n N : ℕ} (p : Equiv.Perm (Fin N)) (S T : Finset ℕ)
    (hS : ∀ w ∈ S, w < n + N) (hT : ∀ w ∈ T, w < n + N) :
    pairCost (S.image (wireMap n N p)) (T.image (wireMap n N p)) = pairCost S T := by
  have hi := wireMap_image_inter p S T hS hT
  have hu : ∀ w ∈ S ∪ T, w < n + N := by
    intro w hw; rcases Finset.mem_union.mp hw with h | h
    · exact hS w h
    · exact hT w h
  simp only [pairCost, hi, Finset.image_eq_empty, ← Finset.image_union]
  rw [wireMap_image_card p S hS, wireMap_image_card p T hT, wireMap_image_card p (S ∪ T) hu]

def movedColor {n N : ℕ} (p : Equiv.Perm (Fin N)) (color : ℕ → Bool) (w : ℕ) : Bool :=
  color (wireMap n N p.symm w)

lemma movedColor_map {n N : ℕ} (p : Equiv.Perm (Fin N)) (color : ℕ → Bool)
    (w : ℕ) (hw : w < n + N) :
    movedColor (n := n) p color (wireMap n N p w) = color w := by
  simp only [movedColor, wireMap_inverse_valid p w hw]

lemma projectColor_image {n N : ℕ} (p : Equiv.Perm (Fin N)) (color : ℕ → Bool)
    (c : Bool) (S : Finset ℕ) (hS : ∀ w ∈ S, w < n + N) :
    projectColor (movedColor (n := n) p color) c (S.image (wireMap n N p)) =
      (projectColor color c S).image (wireMap n N p) := by
  ext w
  simp only [projectColor, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hc⟩
    exact ⟨u, ⟨hu, by rwa [movedColor_map p color u (hS u hu)] at hc⟩, rfl⟩
  · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, by rwa [movedColor_map p color u (hS u hu)]⟩

lemma hasBoth_image {n N : ℕ} (p : Equiv.Perm (Fin N)) (color : ℕ → Bool)
    (S : Finset ℕ) (hS : ∀ w ∈ S, w < n + N) (h : HasBoth color S) :
    HasBoth (movedColor (n := n) p color) (S.image (wireMap n N p)) := by
  intro c
  obtain ⟨w, hw, hc⟩ := h c
  exact ⟨wireMap n N p w, Finset.mem_image.mpr ⟨w, hw, rfl⟩,
    (movedColor_map p color w (hS w hw)).trans hc⟩

lemma sourceOr_image (gs hs : List Gate) (x : List Bool) (S : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ w ∈ S, (TwoOrBuild.run hs x).getD (f w) false =
      (TwoOrBuild.run gs x).getD w false) :
    sourceOr hs x (S.image f) = sourceOr gs x S := by
  unfold sourceOr
  congr 1
  apply propext
  constructor
  · rintro ⟨w, hw, hv⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨u, hu, by rwa [h u hu] at hv⟩
  · rintro ⟨w, hw, hv⟩
    exact ⟨f w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, by rwa [h w hw]⟩


lemma hoist_prefix_wireVal {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (P K : Finset (Fin C.gates.length))
    (hP : PredecessorClosed n C P) (hK : PredecessorClosed n C K)
    (w : ℕ) (hw : w < n ∨ ∃ j ∈ P, w = n + j.val) (x : Fin n → Bool) :
    wireVal n ⟨(permute n C (sortPerm (blockKey P K))).gates.take P.card, 0⟩
      (wireMap n C.gates.length (sortPerm (blockKey P K)) w) x = wireVal n C w x := by
  have hvalid : w < n + C.gates.length := by
    rcases hw with h | ⟨j, hj, rfl⟩
    · omega
    · omega
  have hsmall := (wireMap_two_closed_small_iff P K w hvalid).mpr hw
  have hcard : P.card ≤ C.gates.length := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ P
  rw [take_wireVal _ P.card 0 x _ (by
    simpa only [permute, List.length_ofFn, Fintype.card_fin, Nat.min_eq_left hcard] using hsmall)]
  exact (two_closed_hoist_semantics C hAO P K hP hK).2.2.2 x w

lemma hoist_prefix_sourceOr {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (P K : Finset (Fin C.gates.length))
    (hP : PredecessorClosed n C P) (hK : PredecessorClosed n C K)
    (S : Finset ℕ) (hS : ∀ w ∈ S, w < n ∨ ∃ j ∈ P, w = n + j.val)
    (x : Fin n → Bool) :
    sourceOr ((permute n C (sortPerm (blockKey P K))).gates.take P.card)
      (List.ofFn x) (S.image (wireMap n C.gates.length (sortPerm (blockKey P K)))) =
    sourceOr C.gates (List.ofFn x) S := by
  apply sourceOr_image
  intro w hw
  exact hoist_prefix_wireVal C hAO P K hP hK w (hS w hw) x

lemma hoist_projected_sourceOr {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (P K : Finset (Fin C.gates.length))
    (hP : PredecessorClosed n C P) (hK : PredecessorClosed n C K)
    (S : Finset ℕ) (hS : ∀ w ∈ S, w < n ∨ ∃ j ∈ P, w = n + j.val)
    (color : ℕ → Bool) (c : Bool) (x : Fin n → Bool) :
    sourceOr ((permute n C (sortPerm (blockKey P K))).gates.take P.card) (List.ofFn x)
      (projectColor (movedColor (n := n) (sortPerm (blockKey P K)) color) c
        (S.image (wireMap n C.gates.length (sortPerm (blockKey P K))))) =
    sourceOr C.gates (List.ofFn x) (projectColor color c S) := by
  rw [projectColor_image _ color c S (by
    intro w hw
    rcases hS w hw with h | ⟨j, hj, rfl⟩
    · omega
    · omega)]
  apply hoist_prefix_sourceOr C hAO P K hP hK
  intro w hw
  exact hS w (Finset.mem_filter.mp hw).1


lemma region_bounded {n : ℕ} (C : Circuit) (g h : ℕ) :
    ∀ k ∈ MixedCut.region n C g h, k < C.gates.length := by
  intro k hk; exact ((MixedCut.region_mem C g h k).mp hk).1

lemma pureRegion_bounded {n : ℕ} (C : Circuit) (s : Fin n → Bool) (g h : ℕ) :
    ∀ k ∈ MixedCut.pureRegion n C s g h, k < C.gates.length := by
  intro k hk; exact region_bounded C g h k (Finset.mem_filter.mp hk).1

lemma region_fin_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g) :
    PredecessorClosed n C (boundedSet C.gates.length (MixedCut.region n C g h)) := by
  exact boundedSet_closed C _ (MixedCut.region_predecessor_closed G C hAO hT g h hpair hgh hhg)

lemma pureRegion_fin_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g) :
    PredecessorClosed n C (boundedSet C.gates.length (MixedCut.pureRegion n C s g h)) := by
  exact boundedSet_closed C _ (MixedCut.pureRegion_predecessor_closed G C s hAO hT g h hpair hgh hhg)

lemma pureRegion_fin_subset {n : ℕ} (C : Circuit) (s : Fin n → Bool) (g h : ℕ) :
    boundedSet C.gates.length (MixedCut.pureRegion n C s g h) ⊆
      boundedSet C.gates.length (MixedCut.region n C g h) := by
  exact boundedSet_subset (Finset.filter_subset _ _)

lemma mixedRegion_card_sub {n : ℕ} (C : Circuit) (s : Fin n → Bool) (g h : ℕ) :
    (MixedCut.mixedRegion n C s g h).card =
      (boundedSet C.gates.length (MixedCut.region n C g h)).card -
      (boundedSet C.gates.length (MixedCut.pureRegion n C s g h)).card := by
  rw [boundedSet_card _ _ (region_bounded C g h),
    boundedSet_card _ _ (pureRegion_bounded C s g h)]
  exact Finset.card_sdiff_of_subset (Finset.filter_subset _ _)

lemma raw_or_pure_fin {n : ℕ} (C : Circuit) (s : Fin n → Bool) (g h w : ℕ)
    (hw : w < n ∨ ∃ k ∈ MixedCut.pureRegion n C s g h, w = n + k) :
    w < n ∨ ∃ k ∈ boundedSet C.gates.length (MixedCut.pureRegion n C s g h),
      w = n + k.val := by
  rcases hw with h | ⟨k, hk, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨k, pureRegion_bounded C s g h k hk⟩,
      (boundedSet_mem _ _ _).mpr hk, he⟩

end HoistTransport

namespace JunkActivity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open MixedFrontier MixedReach MixedCut

lemma operand_raw_or_region {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (g h a : ℕ) (ha : a ∈ ({g, h} : Finset ℕ)) (halt : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n ∨ ∃ k ∈ region n C g h, opnd C a b = n + k := by
  by_cases hraw : opnd C a b < n
  · exact Or.inl hraw
  obtain ⟨k, heq⟩ : ∃ k, opnd C a b = n + k := ⟨opnd C a b - n, by omega⟩
  have hbound := hAO.2.1 a halt _ (operand_mem C hAO a halt b)
  have hklt : k < C.gates.length := by omega
  refine Or.inr ⟨k, (region_mem C g h k).mpr ⟨hklt, a, ha, b, ?_⟩, heq⟩
  rw [heq]
  exact orReach_self n C k hklt

lemma independent_side_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2) : (side (n := n) C a b).Nonempty := by
  have hamem : a ∈ ({g, h} : Finset ℕ) := by rwa [← hpair]
  exact raw_or_region_support_nonempty G C hAO hT g h hpair hgh hhg _
    (operand_raw_or_region C hAO g h a hamem (junk_data G C a ha).1 b)

lemma independent_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2) (x : Fin n → Bool) :
    gateVal n C a x =
      (ColorProjection.setOr (side (n := n) C a b) x &&
        ColorProjection.setOr (side (n := n) C a (1 - b)) x) := by
  have hamem : a ∈ ({g, h} : Finset ℕ) := by rwa [← hpair]
  obtain ⟨halt, hop⟩ := junk_data G C a ha
  have hsem : ∀ d : Fin 2, wireVal n C (opnd C a d) x =
      ColorProjection.setOr (side (n := n) C a d) x := by
    intro d
    exact raw_or_region_wire_semantics G C hAO hT g h hpair hgh hhg _
      (operand_raw_or_region C hAO g h a hamem halt d) x
  have hrec := CriticalEdge.val_rec C hAO x a halt
  have his : CriticalEdge.isAnd C a = true := by simp [CriticalEdge.isAnd, hop]
  rw [his, if_pos rfl] at hrec
  change gateVal n C a x = (wireVal n C (opnd C a 0) x && wireVal n C (opnd C a 1) x) at hrec
  rw [hsem 0, hsem 1] at hrec
  fin_cases b
  · exact hrec
  · change gateVal n C a x =
      (ColorProjection.setOr (side (n := n) C a 1) x && ColorProjection.setOr (side (n := n) C a 0) x)
    rw [Bool.and_comm]
    exact hrec

lemma independent_mixed_active {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2)
    (hmix : ∀ c : Bool, ∃ i ∈ side (n := n) C a b, s i = c) :
    ∃ c : Bool, gateVal n C a (mono s c) = true := by
  exact product_active_mono_of_mixed_factor C s a _ _
    (independent_product G C hAO hT g h hpair hgh hhg a ha b)
    hmix (independent_side_nonempty G C hAO hT g h hpair hgh hhg a ha (1 - b))

lemma two_mixed_active {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hmixg : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c) :
    ∀ a ∈ junk G C, ∃ c : Bool, gateVal n C a (mono s c) = true := by
  intro a ha
  have hamem : a ∈ ({g, h} : Finset ℕ) := by rwa [← hpair]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hamem
  rcases hamem with hag | hah
  · subst a
    exact independent_mixed_active G C s hAO hT g h hpair hgh hhg g ha bg hmixg
  · subst a
    exact independent_mixed_active G C s hAO hT g h hpair hgh hhg h ha bh hmixh

end JunkActivity

namespace ActualBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open MixedCut MixedFrontier MixedReach

lemma source_boundary_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w u : ℕ)
    (hu : u ∈ BoundarySources.sources n C (ActualCut.boundary n C s g h)
      (ActualCut.wires n C s g h) w) :
    (u < n ∨ ∃ k ∈ pureRegion n C s g h, u = n + k) ∧
      (orIn n C u).Nonempty ∧ (∃ c : Bool, ∀ i ∈ orIn n C u, s i = c) ∧
      ∀ x : Fin n → Bool, wireVal n C u x = ColorProjection.setOr (orIn n C u) x := by
  exact ActualCut.boundary_pure G C s hAO hT g h hpair hgh hhg u
    (BoundarySources.sources_subset n C _ _ w hu)

lemma source_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w u : ℕ)
    (hu : u ∈ BoundarySources.sources n C (ActualCut.boundary n C s g h)
      (ActualCut.wires n C s g h) w) : u < n + C.gates.length := by
  rcases (source_boundary_data G C s hAO hT g h hpair hgh hhg w u hu).1 with
    hraw | ⟨k, hk, rfl⟩
  · omega
  · have hklt := ((region_mem C g h k).mp (Finset.mem_filter.mp hk).1).1
    omega

lemma mixed_wire_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w : ℕ) (hw : w ∈ ActualCut.wires n C s g h) (x : Fin n → Bool) :
    wireVal n C w x = ColorProjection.setOr (orIn n C w) x := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  exact raw_or_region_wire_semantics G C hAO hT g h hpair hgh hhg (n + k)
    (Or.inr ⟨k, (Finset.mem_sdiff.mp hk).1, rfl⟩) x

lemma source_support_union {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w : ℕ) (hw : w ∈ ActualCut.wires n C s g h) :
    (BoundarySources.sources n C (ActualCut.boundary n C s g h)
      (ActualCut.wires n C s g h) w).biUnion (orIn n C) = orIn n C w := by
  apply BoundaryColors.support_union_eq _ _ _ (wireVal n C)
  · intro u hu x
    exact (source_boundary_data G C s hAO hT g h hpair hgh hhg w u hu).2.2.2 x
  · intro x
    have heq := BoundarySources.wire_eq_sourceOr C hAO
      (ActualCut.boundary n C s g h) (ActualCut.wires n C s g h)
      (ActualCut.wires_or G C s hAO hT g h hpair hgh hhg)
      (ActualCut.boundary_parents C s hAO g h) x w (Finset.mem_union_right _ hw)
    change TwoOrBuild.sourceOr C.gates (List.ofFn x) _ = _
    rw [← heq]
    exact mixed_wire_semantics G C s hAO hT g h hpair hgh hhg w hw x

lemma sources_hasBoth {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w : ℕ) (hw : w ∈ ActualCut.wires n C s g h) :
    TwoOrBuild.HasBoth (BoundaryColors.color (orIn n C) s)
      (BoundarySources.sources n C (ActualCut.boundary n C s g h)
        (ActualCut.wires n C s g h) w) := by
  intro c
  apply BoundaryColors.source_each_color _ _ (orIn n C w) s
  · intro u hu
    exact (source_boundary_data G C s hAO hT g h hpair hgh hhg w u hu).2.2.1
  · exact source_support_union G C s hAO hT g h hpair hgh hhg w hw
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    exact mixed_not_monochromatic s _ ((mixedRegion_mem C s g h k).mp hk).2

lemma source_projection_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (w : ℕ) (hw : w ∈ ActualCut.wires n C s g h) (c : Bool) (x : Fin n → Bool) :
    TwoOrBuild.sourceOr C.gates (List.ofFn x)
      (TwoOrBuild.projectColor (BoundaryColors.color (orIn n C) s) c
        (BoundarySources.sources n C (ActualCut.boundary n C s g h)
          (ActualCut.wires n C s g h) w)) =
      ColorProjection.setOr (ColorProjection.project (orIn n C w) s c) x := by
  apply BoundaryColors.source_projection_semantics _ _ (orIn n C w) s (fun u => wireVal n C u x) x
  · intro u hu
    exact (source_boundary_data G C s hAO hT g h hpair hgh hhg w u hu).2.2.1
  · exact source_support_union G C s hAO hT g h hpair hgh hhg w hw
  · intro u hu
    exact (source_boundary_data G C s hAO hT g h hpair hgh hhg w u hu).2.2.2 x

end ActualBoundary

namespace CompleteMixedCase
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open Reorder HoistTransport TwoOrBuild

lemma smaller_projection_prefix {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (P K : Finset (Fin C.gates.length))
    (hP : PredecessorClosed n C P) (hK : PredecessorClosed n C K)
    (S T : Finset ℕ)
    (hS : ∀ w ∈ S, w < n ∨ ∃ j ∈ P, w = n + j.val)
    (hT : ∀ w ∈ T, w < n ∨ ∃ j ∈ P, w = n + j.val)
    (color : ℕ → Bool) (c d : Bool) (hSmixed : HasBoth color S) (hTmixed : HasBoth color T)
    (hcost : pairCost S T ≤ K.card - P.card) :
    let pre := (permute n C (sortPerm (blockKey P K))).gates.take P.card
    ∃ (hs : List Gate) (wS wT : ℕ),
      IsAO2 n ⟨pre ++ hs, wS⟩ ∧ IsAO2 n ⟨pre ++ hs, wT⟩ ∧
      (∀ g ∈ hs, g.op = GateOp.or) ∧ hs.length < K.card - P.card ∧
      wS < n + (pre ++ hs).length ∧ wT < n + (pre ++ hs).length ∧
      ∀ x : Fin n → Bool,
        wireVal n ⟨pre ++ hs, 0⟩ wS x = sourceOr C.gates (List.ofFn x) (projectColor color c S) ∧
        wireVal n ⟨pre ++ hs, 0⟩ wT x = sourceOr C.gates (List.ofFn x) (projectColor color d T) := by
  dsimp only
  let p := sortPerm (blockKey P K)
  let D := permute n C p
  let pre := D.gates.take P.card
  let f := wireMap n C.gates.length p
  have hD := (two_closed_hoist_semantics C hAO P K hP hK).1
  have hprefix : IsAO2 n ⟨pre, 0⟩ := take_isAO2 D hD P.card 0
  have hcard : P.card ≤ C.gates.length := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ P
  have hprefixlen : pre.length = P.card := by
    simp only [pre, D, permute, List.length_take, List.length_ofFn, Nat.min_eq_left hcard]
  have hSvalid : ∀ w ∈ S, w < n + C.gates.length := by
    intro w hw; rcases hS w hw with hh | ⟨j, hj, rfl⟩ <;> omega
  have hTvalid : ∀ w ∈ T, w < n + C.gates.length := by
    intro w hw; rcases hT w hw with hh | ⟨j, hj, rfl⟩ <;> omega
  have hSimage : ∀ w ∈ S.image f, w < n + pre.length := by
    intro w hw; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [hprefixlen]
    exact (wireMap_two_closed_small_iff P K v (hSvalid v hv)).mpr (hS v hv)
  have hTimage : ∀ w ∈ T.image f, w < n + pre.length := by
    intro w hw; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [hprefixlen]
    exact (wireMap_two_closed_small_iff P K v (hTvalid v hv)).mpr (hT v hv)
  obtain ⟨hs, wS, wT, hAO1, hAO2, hops, hlen, hwS, hwT, heval⟩ :=
    two_color_projection_circuits_valid n ⟨pre, 0⟩ hprefix
      (movedColor (n := n) p color) c d (S.image f) (T.image f) hSimage hTimage
      (hasBoth_image p color S hSvalid hSmixed) (hasBoth_image p color T hTvalid hTmixed)
  have hshort : hs.length < K.card - P.card := by
    have heq := pairCost_image p S T hSvalid hTvalid
    change pairCost (S.image f) (T.image f) = pairCost S T at heq
    rw [heq] at hlen
    omega
  refine ⟨hs, wS, wT, hAO1, hAO2, hops, hshort, hwS, hwT, ?_⟩
  intro x
  obtain ⟨hsval, htval⟩ := heval x
  exact ⟨hsval.trans (hoist_projected_sourceOr C hAO P K hP hK S hS color c x),
    htval.trans (hoist_projected_sourceOr C hAO P K hP hK T hT color d x)⟩


lemma hoist_large_prefix_wireVal {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (P K : Finset (Fin C.gates.length)) (hPK : P ⊆ K)
    (hP : PredecessorClosed n C P) (hK : PredecessorClosed n C K)
    (w : ℕ) (hw : w < n ∨ ∃ j ∈ K, w = n + j.val) (x : Fin n → Bool) :
    wireVal n ⟨(permute n C (sortPerm (blockKey P K))).gates.take K.card, 0⟩
      (wireMap n C.gates.length (sortPerm (blockKey P K)) w) x = wireVal n C w x := by
  have hvalid : w < n + C.gates.length := by
    rcases hw with h | ⟨j, hj, rfl⟩ <;> omega
  have hsmall := (wireMap_two_closed_large_iff P K hPK w hvalid).mpr hw
  have hcard : K.card ≤ C.gates.length := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ K
  rw [take_wireVal _ K.card 0 x _ (by
    simpa only [permute, List.length_ofFn, Fintype.card_fin, Nat.min_eq_left hcard] using hsmall)]
  exact (two_closed_hoist_semantics C hAO P K hP hK).2.2.2 x w

lemma hoist_new_prefix_wireVal {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (P K : Finset (Fin C.gates.length))
    (hP : PredecessorClosed n C P) (hK : PredecessorClosed n C K)
    (hs : List Gate) (w : ℕ) (hw : w < n ∨ ∃ j ∈ P, w = n + j.val) (x : Fin n → Bool) :
    wireVal n ⟨(permute n C (sortPerm (blockKey P K))).gates.take P.card ++ hs, 0⟩
      (wireMap n C.gates.length (sortPerm (blockKey P K)) w) x = wireVal n C w x := by
  have hvalid : w < n + C.gates.length := by
    rcases hw with h | ⟨j, hj, rfl⟩ <;> omega
  have hsmall := (wireMap_two_closed_small_iff P K w hvalid).mpr hw
  have hcard : P.card ≤ C.gates.length := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ P
  have hkeep := TwoOrBuild.run_prefix
    ((permute n C (sortPerm (blockKey P K))).gates.take P.card) hs
    (List.ofFn x) (wireMap n C.gates.length (sortPerm (blockKey P K)) w)
    (by simpa only [List.length_ofFn, List.length_take, permute, List.length_ofFn,
      Nat.min_eq_left hcard] using hsmall)
  exact hkeep.trans (hoist_prefix_wireVal C hAO P K hP hK w hw x)

end CompleteMixedCase

namespace RegionProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5012.Region
open PEqualNP.Outside.L_meta_5012.ColorProjection

lemma and_projection_prefix_simulation {n : ℕ} (pOld pNew : List Gate)
    (g : Gate) (f : ℕ → ℕ) (a b : ℕ) (A B : Finset (Fin n))
    (s : Fin n → Bool) (c : Bool)
    (hop : g.op = GateOp.and) (hin : g.inputs = [a, b] ∨ g.inputs = [b, a])
    (hpure : ∀ v ∈ A, s v = c) (hdis : Disjoint A B)
    (hOldA : ∀ x : Fin n → Bool, (run pOld (List.ofFn x)).getD a false = setOr A x)
    (hOldB : ∀ x : Fin n → Bool, (run pOld (List.ofFn x)).getD b false = setOr B x)
    (hNewA : ∀ x : Fin n → Bool, (run pNew (List.ofFn x)).getD (f a) false = setOr A x)
    (hNewB : ∀ x : Fin n → Bool,
      (run pNew (List.ofFn x)).getD (f b) false = setOr (project B s (!c)) x) :
    (∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun w => (run pNew (List.ofFn x)).getD (f w) false) = true →
      g.op.eval (g.inputs.map fun w => (run pOld (List.ofFn x)).getD w false) = true) ∧
    (∀ u v : Fin n, s u ≠ s v →
      g.op.eval (g.inputs.map fun w =>
        (run pOld (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD w false) = true →
      g.op.eval (g.inputs.map fun w =>
        (run pNew (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD (f w) false) = true) := by
  have hOld : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun w => (run pOld (List.ofFn x)).getD w false) =
        (setOr A x && setOr B x) := by
    intro x
    have ha := hOldA x
    have hb := hOldB x
    simp only [List.getD_eq_getElem?_getD] at ha hb
    rcases hin with heq | heq <;> simp [hop, heq, GateOp.eval, ha, hb, Bool.and_comm]
  have hNew : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun w => (run pNew (List.ofFn x)).getD (f w) false) =
        (setOr A x && setOr (project B s (!c)) x) := by
    intro x
    have ha := hNewA x
    have hb := hNewB x
    simp only [List.getD_eq_getElem?_getD] at ha hb
    rcases hin with heq | heq <;> simp [hop, heq, GateOp.eval, ha, hb, Bool.and_comm]
  constructor
  · intro x hx
    rw [hNew, Bool.and_eq_true] at hx
    rw [hOld, Bool.and_eq_true]
    exact ⟨hx.1, project_le B s (!c) x hx.2⟩
  · intro u v huv hx
    rw [hOld] at hx
    rw [hNew, product_project_pair A B s c hpure hdis u v huv]
    exact hx

end RegionProjection

namespace Reorder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma permute_gateAt_original (n : ℕ) (C : Circuit)
    (π : Equiv.Perm (Fin C.gates.length)) (j : Fin C.gates.length) :
    gateAt (permute n C π) (π j).val = mappedGate n C.gates.length π (gateAt C j.val) := by
  rw [permute_gateAt, gateAt_get]
  simp only [π.symm_apply_apply]

lemma hoisted_target_gate_inputs {n : ℕ} (C : Circuit)
    (π : Equiv.Perm (Fin C.gates.length)) (K : Finset (Fin C.gates.length))
    (hK : ∀ i : Fin C.gates.length, (π i).val < K.card ↔ i ∈ K)
    (j : Fin C.gates.length)
    (hinputs : ∀ w ∈ (gateAt C j.val).inputs,
      w < n ∨ ∃ i ∈ K, w = n + i.val) :
    ∀ w ∈ (gateAt (permute n C π) (π j).val).inputs, w < n + K.card := by
  rw [permute_gateAt_original]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  rcases hinputs v hv with hn | ⟨i, hi, rfl⟩
  · rw [wireMap_input π v hn]; omega
  · rw [wireMap_gate]
    have := (hK i).mpr hi
    omega

lemma hoisted_ordinary_gate_inputs {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (π : Equiv.Perm (Fin C.gates.length)) (P K J : Finset (Fin C.gates.length))
    (hP : ∀ i : Fin C.gates.length, (π i).val < P.card ↔ i ∈ P)
    (hK : ∀ i : Fin C.gates.length, (π i).val < K.card ↔ i ∈ K)
    (hexternal : ∀ i ∈ K, i ∉ P → ∀ j : Fin C.gates.length,
      j ∉ K → n + i.val ∈ (gateAt C j.val).inputs → j ∈ J)
    (j : Fin C.gates.length) (hjK : j ∉ K) (hj : j ∉ J) :
    ∀ w ∈ (gateAt (permute n C π) (π j).val).inputs,
      w < n + P.card ∨ n + K.card ≤ w := by
  rw [permute_gateAt_original]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  by_cases hp : wireMap n C.gates.length π v < n + P.card
  · exact Or.inl hp
  right
  by_contra hk
  have hvalid : v < n + C.gates.length := by
    have := hC.2.1 j.val j.isLt v hv
    have := j.isLt
    omega
  obtain hn | ⟨i, hi, heq⟩ :=
    (wireMap_prefix_iff π K hK v hvalid).mp (by omega)
  · rw [wireMap_input π v hn] at hp
    omega
  · subst v
    have hiP : i ∉ P := by
      intro hiP
      rw [wireMap_gate] at hp
      have := (hP i).mpr hiP
      omega
    exact hj (hexternal i hi hiP j hjK hv)

lemma hoisted_target_position {N : ℕ} (π : Equiv.Perm (Fin N))
    (K J : Finset (Fin N))
    (hK : ∀ i : Fin N, (π i).val < K.card ↔ i ∈ K)
    (hJK : Disjoint J K) (j : Fin N) (hj : j ∈ J) :
    K.card ≤ (π j).val := by
  by_contra h
  exact (Finset.disjoint_left.mp hJK hj) ((hK j).mp (by omega))

def suffixTargets {N : ℕ} (π : Equiv.Perm (Fin N)) (K J : Finset (Fin N)) : Finset ℕ :=
  J.image (fun j => (π j).val - K.card)

lemma suffixTargets_mem_iff {N : ℕ} (π : Equiv.Perm (Fin N))
    (K J : Finset (Fin N))
    (hK : ∀ i : Fin N, (π i).val < K.card ↔ i ∈ K)
    (hJK : Disjoint J K) (k : ℕ) (hk : K.card + k < N) :
    k ∈ suffixTargets π K J ↔ π.symm ⟨K.card + k, hk⟩ ∈ J := by
  constructor
  · intro hkT
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hkT
    have hpos := hoisted_target_position π K J hK hJK j hj
    have hpj : π j = ⟨K.card + k, hk⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
    rwa [← hpj, π.symm_apply_apply]
  · intro hj
    apply Finset.mem_image.mpr
    refine ⟨π.symm ⟨K.card + k, hk⟩, hj, ?_⟩
    rw [π.apply_symm_apply]
    simp

lemma suffixTargets_lt {N : ℕ} (π : Equiv.Perm (Fin N))
    (K J : Finset (Fin N))
    (hK : ∀ i : Fin N, (π i).val < K.card ↔ i ∈ K)
    (hJK : Disjoint J K) : ∀ k ∈ suffixTargets π K J, k < N - K.card := by
  intro k hk
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
  have := hoisted_target_position π K J hK hJK j hj
  have := (π j).isLt
  omega

end Reorder

namespace Reorder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma suffix_gate_eq (D : Circuit) (p s : List Gate) (heq : D.gates = p ++ s)
    (k : ℕ) (hk : k < s.length) : s[k] = gateAt D (p.length + k) := by
  unfold gateAt
  rw [heq, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
  simp

lemma hoisted_suffix_metadata {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (π : Equiv.Perm (Fin C.gates.length)) (P K J : Finset (Fin C.gates.length))
    (hP : ∀ i : Fin C.gates.length, (π i).val < P.card ↔ i ∈ P)
    (hK : ∀ i : Fin C.gates.length, (π i).val < K.card ↔ i ∈ K)
    (hJK : Disjoint J K)
    (hexternal : ∀ i ∈ K, i ∉ P → ∀ j : Fin C.gates.length,
      j ∉ K → n + i.val ∈ (gateAt C j.val).inputs → j ∈ J)
    (htarget : ∀ j ∈ J, ∀ w ∈ (gateAt C j.val).inputs,
      w < n ∨ ∃ i ∈ K, w = n + i.val)
    (p q s : List Gate) (heq : (permute n C π).gates = (p ++ q) ++ s)
    (hp : p.length = P.card) (hpq : (p ++ q).length = K.card) :
    (∀ k (hk : k < s.length), k ∉ suffixTargets π K J → ∀ w ∈ s[k].inputs,
      w < n + p.length ∨ n + (p ++ q).length ≤ w) ∧
    (∀ k (hk : k < s.length), k ∈ suffixTargets π K J → ∀ w ∈ s[k].inputs,
      w < n + (p ++ q).length) := by
  have hlen : K.card + s.length = C.gates.length := by
    have := congrArg List.length heq
    rw [permute_length, List.length_append, hpq] at this
    omega
  have hgate : ∀ k (hk : k < s.length),
      s[k] = gateAt (permute n C π) (K.card + k) := by
    intro k hk
    simpa only [hpq] using suffix_gate_eq (permute n C π) (p ++ q) s heq k hk
  constructor
  · intro k hk hnot w hw
    let f : Fin C.gates.length := ⟨K.card + k, by omega⟩
    let j := π.symm f
    have hj : j ∉ J := by
      intro hj
      exact hnot ((suffixTargets_mem_iff π K J hK hJK k f.isLt).mpr hj)
    have hmap : (π j).val = K.card + k := by dsimp [j, f]; simp
    have hg : s[k] = gateAt (permute n C π) (π j).val := by rw [hmap]; exact hgate k hk
    rw [hg] at hw
    have hjK : j ∉ K := by
      intro hjK
      have := (hK j).mpr hjK
      omega
    have h := hoisted_ordinary_gate_inputs C hC π P K J hP hK hexternal j hjK hj w hw
    simpa only [hp, hpq] using h
  · intro k hk hyes w hw
    let f : Fin C.gates.length := ⟨K.card + k, by omega⟩
    let j := π.symm f
    have hj : j ∈ J := (suffixTargets_mem_iff π K J hK hJK k f.isLt).mp hyes
    have hmap : (π j).val = K.card + k := by dsimp [j, f]; simp
    have hg : s[k] = gateAt (permute n C π) (π j).val := by rw [hmap]; exact hgate k hk
    rw [hg] at hw
    have h := hoisted_target_gate_inputs C π K hK j (htarget j hj) w hw
    simpa only [hpq] using h

end Reorder

namespace Reorder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma take_drop_block (gs : List Gate) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ gs.length) :
    gs = (gs.take a ++ (gs.drop a).take (b-a)) ++ gs.drop b ∧
    (gs.take a).length = a ∧
    (gs.take a ++ (gs.drop a).take (b-a)).length = b ∧
    ((gs.drop a).take (b-a)).length = b-a ∧
    (gs.drop b).length = gs.length-b := by
  have ha : a ≤ gs.length := by omega
  have hdrop : b-a ≤ (gs.drop a).length := by rw [List.length_drop]; omega
  have heq : gs = (gs.take a ++ (gs.drop a).take (b-a)) ++ gs.drop b := by
    calc
      gs = gs.take a ++ gs.drop a := (List.take_append_drop a gs).symm
      _ = gs.take a ++ ((gs.drop a).take (b-a) ++ (gs.drop a).drop (b-a)) := by
        simp only [List.take_append_drop]
      _ = (gs.take a ++ (gs.drop a).take (b-a)) ++ gs.drop b := by
        rw [← List.append_assoc, List.drop_drop]
        have : a + (b-a) = b := by omega
        rw [this]
  refine ⟨heq, List.length_take_of_le ha, ?_, List.length_take_of_le hdrop, List.length_drop⟩
  rw [List.length_append, List.length_take_of_le ha, List.length_take_of_le hdrop]
  omega

lemma hoisted_suffix_gate_data {n : ℕ} (C : Circuit)
    (π : Equiv.Perm (Fin C.gates.length)) (K : Finset (Fin C.gates.length))
    (p q s : List Gate) (heq : (permute n C π).gates = (p ++ q) ++ s)
    (hpq : (p ++ q).length = K.card) (k : ℕ) (hk : k < s.length) :
    ∃ j : Fin C.gates.length, (π j).val = K.card + k ∧
      s[k].op = (gateAt C j.val).op ∧
      s[k].inputs = (gateAt C j.val).inputs.map (wireMap n C.gates.length π) := by
  have hlen : K.card + s.length = C.gates.length := by
    have := congrArg List.length heq
    rw [permute_length, List.length_append, hpq] at this
    omega
  let f : Fin C.gates.length := ⟨K.card + k, by omega⟩
  let j := π.symm f
  have hmap : (π j).val = K.card + k := by dsimp [j, f]; simp
  have hg : s[k] = mappedGate n C.gates.length π (gateAt C j.val) := by
    rw [← permute_gateAt_original, hmap]
    simpa only [hpq] using suffix_gate_eq (permute n C π) (p ++ q) s heq k hk
  refine ⟨j, hmap, ?_, ?_⟩
  · simpa only [mappedGate] using congrArg Gate.op hg
  · simpa only [mappedGate] using congrArg Gate.inputs hg

end Reorder

namespace Reorder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma mapped_factor_locations {n N : ℕ} (π : Equiv.Perm (Fin N)) (P K : Finset (Fin N))
    (hP : ∀ i : Fin N, (π i).val < P.card ↔ i ∈ P)
    (hK : ∀ i : Fin N, (π i).val < K.card ↔ i ∈ K)
    (a b : ℕ) (hA : a < n ∨ ∃ i ∈ P, a = n + i.val)
    (hB : ∃ i ∈ K, i ∉ P ∧ b = n + i.val) :
    wireMap n N π a < n + P.card ∧
    n + P.card ≤ wireMap n N π b ∧ wireMap n N π b < n + K.card := by
  constructor
  · rcases hA with ha | ⟨i, hi, rfl⟩
    · rw [wireMap_input π a ha]; omega
    · rw [wireMap_gate]
      have := (hP i).mpr hi
      omega
  · obtain ⟨i, hiK, hiP, rfl⟩ := hB
    rw [wireMap_gate]
    have hlo : P.card ≤ (π i).val := by
      by_contra h
      exact hiP ((hP i).mp (by omega))
    have hhi := (hK i).mpr hiK
    omega

lemma mappedGate_and_pair {n N : ℕ} (π : Equiv.Perm (Fin N)) (g : Gate)
    (a b : ℕ) (hop : g.op = GateOp.and) (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) :
    (mappedGate n N π g).op = GateOp.and ∧
    ((mappedGate n N π g).inputs = [wireMap n N π a, wireMap n N π b] ∨
      (mappedGate n N π g).inputs = [wireMap n N π b, wireMap n N π a]) := by
  refine ⟨hop, ?_⟩
  rcases hin with hin | hin
  · left; simp [mappedGate, hin]
  · right; simp [mappedGate, hin]

end Reorder

namespace ActualReplacement
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open Reorder HoistTransport TwoOrBuild MixedFrontier MixedCut

lemma actual_smaller_prefix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∃ c : Bool, ∀ i ∈ side (n := n) C g (1 - bg), s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1 - bh), s i = c)
    (hmixg : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c)
    (c d : Bool) :
    let P := boundedSet C.gates.length (pureRegion n C s g h)
    let K := boundedSet C.gates.length (region n C g h)
    let pre := (permute n C (sortPerm (blockKey P K))).gates.take P.card
    ∃ (hs : List Gate) (wS wT : ℕ),
      IsAO2 n ⟨pre ++ hs, wS⟩ ∧ IsAO2 n ⟨pre ++ hs, wT⟩ ∧
      (∀ j ∈ hs, j.op = GateOp.or) ∧ hs.length < (mixedRegion n C s g h).card ∧
      wS < n + (pre ++ hs).length ∧ wT < n + (pre ++ hs).length ∧
      ∀ x : Fin n → Bool,
        wireVal n ⟨pre ++ hs, 0⟩ wS x =
          ColorProjection.setOr (ColorProjection.project (side (n := n) C g bg) s c) x ∧
        wireVal n ⟨pre ++ hs, 0⟩ wT x =
          ColorProjection.setOr (ColorProjection.project (side (n := n) C h bh) s d) x := by
  dsimp only
  let P := boundedSet C.gates.length (pureRegion n C s g h)
  let K := boundedSet C.gates.length (region n C g h)
  let B := ActualCut.boundary n C s g h
  let J := ActualCut.wires n C s g h
  let S := BoundarySources.sources n C B J (opnd C g bg)
  let T := BoundarySources.sources n C B J (opnd C h bh)
  let color := BoundaryColors.color (orIn n C) s
  have hP := pureRegion_fin_closed G C s hL.1 hT g h hpair hgh hhg
  have hK := region_fin_closed G C hL.1 hT g h hpair hgh hhg
  have hgJ : g ∈ junk G C := by rw [hpair]; simp
  have hhJ : h ∈ junk G C := by rw [hpair]; simp
  have hrootg := ActualCut.mixed_operand_mem G C s hbip hL hT hJ g h hpair g hgJ bg hmixg
  have hrooth := ActualCut.mixed_operand_mem G C s hbip hL hT hJ g h hpair h hhJ bh hmixh
  have hS : ∀ w ∈ S, w < n ∨ ∃ j ∈ P, w = n + j.val := by
    intro w hw
    exact raw_or_pure_fin C s g h w
      (ActualBoundary.source_boundary_data G C s hL.1 hT g h hpair hgh hhg _ w hw).1
  have hT' : ∀ w ∈ T, w < n ∨ ∃ j ∈ P, w = n + j.val := by
    intro w hw
    exact raw_or_pure_fin C s g h w
      (ActualBoundary.source_boundary_data G C s hL.1 hT g h hpair hgh hhg _ w hw).1
  have hSmix : HasBoth color S :=
    ActualBoundary.sources_hasBoth G C s hL.1 hT g h hpair hgh hhg _ hrootg
  have hTmix : HasBoth color T :=
    ActualBoundary.sources_hasBoth G C s hL.1 hT g h hpair hgh hhg _ hrooth
  have hcost : pairCost S T ≤ K.card - P.card := by
    rw [← mixedRegion_card_sub C s g h]
    exact ActualCut.pairCost_le_mixedRegion G C s hbip hL hT hJ g h bg bh hpair
      hgh hhg hpureg hpureh hmixg hmixh
  obtain ⟨hs, wS, wT, hAO1, hAO2, hops, hlen, hwS, hwT, heval⟩ :=
    CompleteMixedCase.smaller_projection_prefix C hL.1 P K hP hK S T hS hT'
      color c d hSmix hTmix hcost
  refine ⟨hs, wS, wT, hAO1, hAO2, hops, ?_, hwS, hwT, ?_⟩
  · rwa [mixedRegion_card_sub C s g h]
  · intro x
    exact ⟨(heval x).1.trans
      (ActualBoundary.source_projection_semantics G C s hL.1 hT g h hpair hgh hhg _ hrootg c x),
      (heval x).2.trans
      (ActualBoundary.source_projection_semantics G C s hL.1 hT g h hpair hgh hhg _ hrooth d x)⟩

end ActualReplacement

namespace ActualStructure
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open Reorder HoistTransport MixedFrontier MixedCut

lemma junk_fin_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g,h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g) :
    Disjoint (boundedSet C.gates.length (junk G C))
      (boundedSet C.gates.length (region n C g h)) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  exact junk_not_mem_region G C hAO hT g h hpair hgh hhg j.val
    ((boundedSet_mem _ _ _).mp hj) ((boundedSet_mem _ _ _).mp hk)

lemma external_reader_fin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g,h})
    (i j : Fin C.gates.length)
    (hi : i ∈ boundedSet C.gates.length (region n C g h))
    (hnot : i ∉ boundedSet C.gates.length (pureRegion n C s g h))
    (hj : j ∉ boundedSet C.gates.length (region n C g h))
    (hread : n + i.val ∈ (gateAt C j.val).inputs) :
    j ∈ boundedSet C.gates.length (junk G C) := by
  apply (boundedSet_mem _ _ _).mpr
  apply mixedRegion_external_reader_junk G C s hbip hL hT hJ g h hpair i.val
    (Finset.mem_sdiff.mpr ⟨(boundedSet_mem _ _ _).mp hi,
      fun he => hnot ((boundedSet_mem _ _ _).mpr he)⟩) j.val j.isLt ?_ hread
  intro he
  exact hj ((boundedSet_mem _ _ _).mpr (Finset.mem_sdiff.mp he).1)

lemma target_inputs_fin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (g h : ℕ) (hpair : junk G C = {g,h})
    (j : Fin C.gates.length) (hj : j ∈ boundedSet C.gates.length (junk G C))
    (w : ℕ) (hw : w ∈ (gateAt C j.val).inputs) :
    w < n ∨ ∃ i ∈ boundedSet C.gates.length (region n C g h), w = n + i.val := by
  by_cases hraw : w < n
  · exact Or.inl hraw
  let k := w - n
  have hback := hAO.2.1 j.val j.isLt w hw
  have hklt : k < C.gates.length := by dsimp [k]; omega
  have heq : w = n + k := by dsimp [k]; omega
  have haj : j.val ∈ ({g,h} : Finset ℕ) := by
    rw [← hpair]; exact (boundedSet_mem _ _ _).mp hj
  have hbin := hAO.2.2 (gateAt C j.val) (gateAt_mem' C j.val j.isLt)
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hbin
  have hslot : ∃ d : Fin 2, w = opnd C j.val d := by
    rw [hab] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simp [opnd, hab]⟩
    · exact ⟨1, by simp [opnd, hab]⟩
  obtain ⟨d, hd⟩ := hslot
  refine Or.inr ⟨⟨k,hklt⟩, (boundedSet_mem _ _ _).mpr ?_, heq⟩
  apply (region_mem C g h k).mpr
  refine ⟨hklt, j.val, haj, d, ?_⟩
  rw [← hd, heq]
  exact orReach_self n C k hklt

lemma pure_operand_fin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (g h a : ℕ)
    (hpair : junk G C = {g,h}) (ha : a ∈ junk G C) (b : Fin 2)
    (hpure : ∃ c : Bool, ∀ i ∈ side (n := n) C a b, s i = c) :
    opnd C a b < n ∨ ∃ i ∈ boundedSet C.gates.length (pureRegion n C s g h),
      opnd C a b = n + i.val := by
  have hamem : a ∈ ({g,h} : Finset ℕ) := by rwa [← hpair]
  rcases JunkActivity.operand_raw_or_region C hAO g h a hamem (junk_data G C a ha).1 b with
    hraw | ⟨k,hk,heq⟩
  · exact Or.inl hraw
  · have hklt := ((region_mem C g h k).mp hk).1
    refine Or.inr ⟨⟨k,hklt⟩, (boundedSet_mem _ _ _).mpr ?_, heq⟩
    exact Finset.mem_filter.mpr ⟨hk, by simpa only [side, heq] using hpure⟩

lemma mixed_operand_fin {n : ℕ} (C : Circuit) (s : Fin n → Bool) (g h w : ℕ)
    (hw : w ∈ ActualCut.wires n C s g h) :
    ∃ i ∈ boundedSet C.gates.length (region n C g h),
      i ∉ boundedSet C.gates.length (pureRegion n C s g h) ∧ w = n + i.val := by
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hkK,hkP⟩ := Finset.mem_sdiff.mp hk
  exact ⟨⟨k, ((region_mem C g h k).mp hkK).1⟩, (boundedSet_mem _ _ _).mpr hkK,
    fun he => hkP ((boundedSet_mem _ _ _).mp he), rfl⟩

lemma operand_pair {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (a : ℕ)
    (ha : a < C.gates.length) (b : Fin 2) :
    (gateAt C a).inputs = [opnd C a (1-b), opnd C a b] ∨
      (gateAt C a).inputs = [opnd C a b, opnd C a (1-b)] := by
  obtain ⟨u,v,huv⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C a ha))
  fin_cases b <;> simp [opnd, huv]

end ActualStructure

namespace RegionProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5012.Region
open PEqualNP.Outside.L_meta_5012.RegionLocal
open PEqualNP.Outside.L_meta_5012.ColorProjection

lemma projected_block_target_simulation {n : ℕ} (p q r : List Gate)
    (g : Gate) (targetWire : ℕ → ℕ) (k a b : ℕ)
    (A B : Finset (Fin n)) (color : Fin n → Bool) (c : Bool)
    (hop : g.op = GateOp.and) (hin : g.inputs = [a, b] ∨ g.inputs = [b, a])
    (ha : a < n + p.length) (hblo : n + p.length ≤ b) (hbhi : b < n + (p ++ q).length)
    (hpure : ∀ v ∈ A, color v = c) (hdis : Disjoint A B)
    (hOldA : ∀ x : Fin n → Bool, (run (p ++ q) (List.ofFn x)).getD a false = setOr A x)
    (hOldB : ∀ x : Fin n → Bool, (run (p ++ q) (List.ofFn x)).getD b false = setOr B x)
    (hNewB : ∀ x : Fin n → Bool,
      (run (p ++ r) (List.ofFn x)).getD (targetWire k) false =
        setOr (project B color (!c)) x) :
    (∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun w => (run (p ++ r) (List.ofFn x)).getD
        (blockMap n p q r targetWire k w) false) = true →
      g.op.eval (g.inputs.map fun w => (run (p ++ q) (List.ofFn x)).getD w false) = true) ∧
    (∀ u v : Fin n, color u ≠ color v →
      g.op.eval (g.inputs.map fun w =>
        (run (p ++ q) (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD w false) = true →
      g.op.eval (g.inputs.map fun w =>
        (run (p ++ r) (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD
          (blockMap n p q r targetWire k w) false) = true) := by
  apply and_projection_prefix_simulation (p ++ q) (p ++ r) g
    (blockMap n p q r targetWire k) a b A B color c hop hin hpure hdis hOldA hOldB
  · intro x
    rw [blockMap_keep n p q r targetWire k a ha]
    rw [run_prefix p r (List.ofFn x) a (by simpa only [List.length_ofFn] using ha)]
    rw [← run_prefix p q (List.ofFn x) a (by simpa only [List.length_ofFn] using ha)]
    exact hOldA x
  · intro x
    rw [blockMap_region n p q r targetWire k b hblo hbhi]
    exact hNewB x

lemma least_projected_block_contradiction (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (p q r s : List Gate) (targetWire : ℕ → ℕ) (targets : Finset ℕ)
    (j : ℕ) (hj : j < s.length)
    (hL : TopForm.IsLeastAO G ⟨(p ++ q) ++ s, n + (p ++ q).length + j⟩)
    (hprefix : TopForm.IsAO2 n ⟨p ++ r, 0⟩)
    (hshort : r.length < q.length)
    (hroot : ∀ k ∈ targets, targetWire k < n + (p ++ r).length)
    (hordinary : ∀ k (hk : k < s.length), k ∉ targets → ∀ w ∈ s[k].inputs,
      w < n + p.length ∨ n + (p ++ q).length ≤ w)
    (hdata : ∀ k (hk : k < s.length), k ∈ targets →
      ∃ a b : ℕ, ∃ A B : Finset (Fin n), ∃ c : Bool,
        s[k].op = GateOp.and ∧ (s[k].inputs = [a, b] ∨ s[k].inputs = [b, a]) ∧
        a < n + p.length ∧ n + p.length ≤ b ∧ b < n + (p ++ q).length ∧
        (∀ v ∈ A, color v = c) ∧ Disjoint A B ∧
        (∀ x : Fin n → Bool, (run (p ++ q) (List.ofFn x)).getD a false = setOr A x) ∧
        (∀ x : Fin n → Bool, (run (p ++ q) (List.ofFn x)).getD b false = setOr B x) ∧
        (∀ x : Fin n → Bool, (run (p ++ r) (List.ofFn x)).getD (targetWire k) false =
          setOr (project B color (!c)) x)) : False := by
  have htOld : ∀ k (hk : k < s.length), k ∈ targets → ∀ w ∈ s[k].inputs,
      w < n + (p ++ q).length := by
    intro k hk hkt w hw
    obtain ⟨a, b, A, B, c, hop, hin, ha, hblo, hbhi, hpure, hdis, hOldA, hOldB, hNewB⟩ :=
      hdata k hk hkt
    rcases hin with hin | hin <;> rw [hin] at hw <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    · rcases hw with rfl | rfl
      · simp only [List.length_append]; omega
      · exact hbhi
    · rcases hw with rfl | rfl
      · exact hbhi
      · simp only [List.length_append]; omega
  apply least_block_with_targets n G p q r s targetWire targets j hj hL hprefix hshort
    hroot hordinary htOld
  · intro x hx k hk hkt
    obtain ⟨a, b, A, B, c, hop, hin, ha, hblo, hbhi, hpure, hdis, hOldA, hOldB, hNewB⟩ :=
      hdata k hk hkt
    exact (projected_block_target_simulation p q r s[k] targetWire k a b A B color c
      hop hin ha hblo hbhi hpure hdis hOldA hOldB hNewB).1 x
  · intro u v huv k hk hkt
    obtain ⟨a, b, A, B, c, hop, hin, ha, hblo, hbhi, hpure, hdis, hOldA, hOldB, hNewB⟩ :=
      hdata k hk hkt
    exact (projected_block_target_simulation p q r s[k] targetWire k a b A B color c
      hop hin ha hblo hbhi hpure hdis hOldA hOldB hNewB).2 u v (hbip u v huv)

end RegionProjection

namespace RegionProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_5012.Reorder
open PEqualNP.Outside.L_meta_5012.ColorProjection

lemma projected_target_hoist_contradiction {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (π : Equiv.Perm (Fin C.gates.length)) (hdep : DependencyOrder n C π)
    (P K J : Finset (Fin C.gates.length)) (hPK : P ⊆ K)
    (hP : ∀ i : Fin C.gates.length, (π i).val < P.card ↔ i ∈ P)
    (hK : ∀ i : Fin C.gates.length, (π i).val < K.card ↔ i ∈ K)
    (hJK : Disjoint J K)
    (hexternal : ∀ i ∈ K, i ∉ P → ∀ j : Fin C.gates.length,
      j ∉ K → n + i.val ∈ (gateAt C j.val).inputs → j ∈ J)
    (hout : ∃ j < C.gates.length - K.card,
      (permute n C π).output = n + K.card + j)
    (r : List Gate) (targetWire : ℕ → ℕ)
    (hprefix : IsAO2 n ⟨(permute n C π).gates.take P.card ++ r, 0⟩)
    (hshort : r.length < K.card - P.card)
    (hroot : ∀ j ∈ J, targetWire ((π j).val - K.card) <
      n + ((permute n C π).gates.take P.card ++ r).length)
    (hfactors : ∀ j ∈ J, ∃ a b : ℕ, ∃ A B : Finset (Fin n), ∃ c : Bool,
      (gateAt C j.val).op = GateOp.and ∧
      ((gateAt C j.val).inputs = [a,b] ∨ (gateAt C j.val).inputs = [b,a]) ∧
      (a < n ∨ ∃ i ∈ P, a = n + i.val) ∧
      (∃ i ∈ K, i ∉ P ∧ b = n + i.val) ∧
      (∀ v ∈ A, color v = c) ∧ Disjoint A B ∧
      (∀ x : Fin n → Bool, wireVal n C a x = setOr A x) ∧
      (∀ x : Fin n → Bool, wireVal n C b x = setOr B x) ∧
      (∀ x : Fin n → Bool,
        (Region.run ((permute n C π).gates.take P.card ++ r) (List.ofFn x)).getD
          (targetWire ((π j).val - K.card)) false = setOr (project B color (!c)) x)) : False := by
  let D := permute n C π
  let p := D.gates.take P.card
  let q := (D.gates.drop P.card).take (K.card - P.card)
  let s := D.gates.drop K.card
  have hcard : K.card ≤ D.gates.length := by
    rw [permute_length]
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ K
  have hcards : P.card ≤ K.card := Finset.card_le_card hPK
  obtain ⟨hsplit, hplen, hpqlen, hqlen, hslen⟩ := take_drop_block D.gates P.card K.card hcards hcard
  change D.gates = (p ++ q) ++ s at hsplit
  change p.length = P.card at hplen
  change (p ++ q).length = K.card at hpqlen
  change q.length = K.card - P.card at hqlen
  change s.length = D.gates.length - K.card at hslen
  obtain ⟨jo, hjo, hout⟩ := hout
  change D.output = n + K.card + jo at hout
  have hjo' : jo < s.length := by rw [hslen, permute_length]; exact hjo
  have heqD : D = ⟨(p ++ q) ++ s, n + (p ++ q).length + jo⟩ := by
    cases hD : D with
    | mk gs out =>
      have hg : gs = (p ++ q) ++ s := by simpa only [hD] using hsplit
      have ho : out = n + (p ++ q).length + jo := by
        simpa only [← hpqlen, hD] using hout
      simp only [hg, ho]
  have hleast := permute_isLeastAO G C hL π hdep
  change IsLeastAO G D at hleast
  rw [heqD] at hleast
  have htarget : ∀ j ∈ J, ∀ w ∈ (gateAt C j.val).inputs,
      w < n ∨ ∃ i ∈ K, w = n + i.val := by
    intro j hj w hw
    obtain ⟨a,b,A,B,c,hop,hin,ha,hb,hpure,hdis,hOldA,hOldB,hNew⟩ := hfactors j hj
    have haK : a < n ∨ ∃ i ∈ K, a = n + i.val := by
      rcases ha with h | ⟨i,hi,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨i,hPK hi,he⟩
    have hbK : b < n ∨ ∃ i ∈ K, b = n + i.val := by
      obtain ⟨i,hi,_,he⟩ := hb
      exact Or.inr ⟨i,hi,he⟩
    rcases hin with hin | hin <;> rw [hin] at hw <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    · rcases hw with rfl | rfl <;> assumption
    · rcases hw with rfl | rfl <;> assumption
  have hmeta := hoisted_suffix_metadata C hL.1 π P K J hP hK hJK hexternal htarget
    p q s hsplit hplen hpqlen
  have hwire : ∀ w, wireMap n C.gates.length π w < n + K.card → ∀ x : Fin n → Bool,
      (Region.run (p ++ q) (List.ofFn x)).getD (wireMap n C.gates.length π w) false =
        wireVal n C w x := by
    intro w hw x
    have hpres := (permute_semantics C hL.1 π hdep).2.2.2 x w
    calc
      _ = (Region.run D.gates (List.ofFn x)).getD (wireMap n C.gates.length π w) false := by
        rw [hsplit]
        symm
        apply Region.run_prefix
        simpa only [List.length_ofFn, hpqlen] using hw
      _ = wireVal n C w x := hpres
  apply least_projected_block_contradiction n G color hbip p q r s targetWire
    (suffixTargets π K J) jo hjo' hleast hprefix (by rwa [hqlen])
  · intro k hk
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hk
    subst k
    exact hroot j hj
  · exact hmeta.1
  · intro k hk hkt
    obtain ⟨j, hjmap, hjop, hjin⟩ := hoisted_suffix_gate_data C π K p q s hsplit hpqlen k hk
    have hj : j ∈ J := by
      have hkN : K.card + k < C.gates.length := by rw [← hjmap]; exact (π j).isLt
      have hfin : (π j) = ⟨K.card+k,hkN⟩ := Fin.ext hjmap
      have := (suffixTargets_mem_iff π K J hK hJK k hkN).mp hkt
      simpa only [← hfin, π.symm_apply_apply] using this
    obtain ⟨a,b,A,B,c,hop,hin,ha,hb,hpure,hdis,hOldA,hOldB,hNew⟩ := hfactors j hj
    have hloc := mapped_factor_locations π P K hP hK a b ha hb
    have hkmap : (π j).val - K.card = k := by omega
    refine ⟨wireMap n C.gates.length π a, wireMap n C.gates.length π b,
      A,B,c, hjop.trans hop, ?_, ?_, ?_, ?_, hpure,hdis, ?_, ?_, ?_⟩
    · rw [hjin]
      rcases hin with hin | hin
      · left; simp [hin]
      · right; simp [hin]
    · simpa only [hplen] using hloc.1
    · simpa only [hplen] using hloc.2.1
    · simpa only [hpqlen] using hloc.2.2
    · intro x
      rw [hwire a (by have := hloc.1; omega)]
      exact hOldA x
    · intro x
      rw [hwire b hloc.2.2]
      exact hOldB x
    · intro x
      simpa only [hkmap] using hNew x

end RegionProjection

namespace CompleteRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open Reorder HoistTransport MixedFrontier MixedCut

lemma independent_semimixed_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g,h}) (hne : g ≠ h)
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∃ c : Bool, ∀ i ∈ side (n := n) C g (1-bg), s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1-bh), s i = c)
    (hmixg : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c)
    (hdisg : Disjoint (side (n := n) C g (1-bg)) (side (n := n) C g bg))
    (hdish : Disjoint (side (n := n) C h (1-bh)) (side (n := n) C h bh)) : False := by
  have hJ := JunkActivity.two_mixed_active G C s hL.1 hT g h bg bh hpair hgh hhg hmixg hmixh
  obtain ⟨cg,hcg⟩ := hpureg
  obtain ⟨ch,hch⟩ := hpureh
  let P := boundedSet C.gates.length (pureRegion n C s g h)
  let K := boundedSet C.gates.length (region n C g h)
  let J := boundedSet C.gates.length (junk G C)
  let π := sortPerm (blockKey P K)
  have hPK : P ⊆ K := pureRegion_fin_subset C s g h
  have hPc : PredecessorClosed n C P := pureRegion_fin_closed G C s hL.1 hT g h hpair hgh hhg
  have hKc : PredecessorClosed n C K := region_fin_closed G C hL.1 hT g h hpair hgh hhg
  have hdep : DependencyOrder n C π := two_closed_hoist_dependency C hL.1 P K hPc hKc
  have hP : ∀ i, (π i).val < P.card ↔ i ∈ P := two_closed_hoist_prefix_small P K
  have hK : ∀ i, (π i).val < K.card ↔ i ∈ K := two_closed_hoist_prefix_large P K hPK
  have hJK : Disjoint J K := ActualStructure.junk_fin_disjoint G C hL.1 hT g h hpair hgh hhg
  have hgJ : g ∈ junk G C := by rw [hpair]; simp
  have hhJ : h ∈ junk G C := by rw [hpair]; simp
  let gf : Fin C.gates.length := ⟨g,(junk_data G C g hgJ).1⟩
  let hf : Fin C.gates.length := ⟨h,(junk_data G C h hhJ).1⟩
  have hgf : gf ∈ J := (boundedSet_mem _ _ _).mpr hgJ
  have hhf : hf ∈ J := (boundedSet_mem _ _ _).mpr hhJ
  have hposg := hoisted_target_position π K J hK hJK gf hgf
  have hposh := hoisted_target_position π K J hK hJK hf hhf
  have hposne : (π hf).val - K.card ≠ (π gf).val - K.card := by
    intro heq
    have heq' : π hf = π gf := Fin.ext (by omega)
    have hhg' : h = g := congrArg Fin.val (π.injective heq')
    exact hne hhg'.symm
  obtain ⟨hs,wS,wT,hAO1,hAO2,hops,hlen,hwS,hwT,heval⟩ :=
    ActualReplacement.actual_smaller_prefix G C s hbip hL hT hJ g h bg bh hpair hgh hhg
      ⟨cg,hcg⟩ ⟨ch,hch⟩ hmixg hmixh (!cg) (!ch)
  let targetWire : ℕ → ℕ := fun k => if k = (π gf).val - K.card then wS else wT
  have htargg : targetWire ((π gf).val - K.card) = wS := by simp [targetWire]
  have htargh : targetWire ((π hf).val - K.card) = wT := by simp [targetWire,hposne]
  have houtLo := OutputSupport.output_not_raw G C hL.2.1
  have houtHi := CriticalEdge.output_lt G C hL.2.1
    (CriticalEdge.least_nonempty_of_gate G C hL g gf.isLt)
  have hout := two_closed_hoist_output_suffix C P K hPK houtLo houtHi (by
    intro j hj
    exact OutputSupport.region_not_output G C hL.1 hL.2.1 hT g h hpair hgh hhg
      j.val ((boundedSet_mem _ _ _).mp hj))
  have hrootg := ActualCut.mixed_operand_mem G C s hbip hL hT hJ g h hpair g hgJ bg hmixg
  have hrooth := ActualCut.mixed_operand_mem G C s hbip hL hT hJ g h hpair h hhJ bh hmixh
  have hraw : ∀ a ∈ junk G C, ∀ b : Fin 2, ∀ x : Fin n → Bool,
      wireVal n C (opnd C a b) x = ColorProjection.setOr (side (n := n) C a b) x := by
    intro a ha b x
    have hapair : a ∈ ({g,h} : Finset ℕ) := by rwa [← hpair]
    exact raw_or_region_wire_semantics G C hL.1 hT g h hpair hgh hhg _
      (JunkActivity.operand_raw_or_region C hL.1 g h a hapair (junk_data G C a ha).1 b) x
  apply RegionProjection.projected_target_hoist_contradiction G C hL s hbip π hdep
    P K J hPK hP hK hJK ?_ hout hs targetWire hAO1 ?_ ?_ ?_
  · intro i hi hip j hj hread
    exact ActualStructure.external_reader_fin G C s hbip hL hT hJ g h hpair i j hi hip hj hread
  · rwa [mixedRegion_card_sub C s g h] at hlen
  · intro j hj
    dsimp [targetWire]
    split <;> assumption
  · intro j hj
    have hjJ : j.val ∈ junk G C := (boundedSet_mem _ _ _).mp hj
    rw [hpair] at hjJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjJ
    rcases hjJ with hjg | hjh
    · have heq : j = gf := Fin.ext hjg
      subst j
      refine ⟨opnd C g (1-bg),opnd C g bg,side C g (1-bg),side C g bg,cg,
        (junk_data G C g hgJ).2, ActualStructure.operand_pair C hL.1 g gf.isLt bg,
        ActualStructure.pure_operand_fin G C s hL.1 g h g hpair hgJ (1-bg) ⟨cg,hcg⟩,
        ActualStructure.mixed_operand_fin C s g h _ hrootg,hcg,hdisg,
        hraw g hgJ (1-bg),hraw g hgJ bg,?_⟩
      intro x
      rw [htargg]
      exact (heval x).1
    · have heq : j = hf := Fin.ext hjh
      subst j
      refine ⟨opnd C h (1-bh),opnd C h bh,side C h (1-bh),side C h bh,ch,
        (junk_data G C h hhJ).2, ActualStructure.operand_pair C hL.1 h hf.isLt bh,
        ActualStructure.pure_operand_fin G C s hL.1 g h h hpair hhJ (1-bh) ⟨ch,hch⟩,
        ActualStructure.mixed_operand_fin C s g h _ hrooth,hch,hdish,
        hraw h hhJ (1-bh),hraw h hhJ bh,?_⟩
      intro x
      rw [htargh]
      exact (heval x).2

end CompleteRestricted

namespace BothMono

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open CriticalEdge MixedFrontier MixedReach MixedCut

lemma both_mono_not_or_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hfun : circuitFun n C = graphFun G ∅) (j : ℕ)
    (hboth : ∀ c : Bool, gateVal n C j (mono s c) = true) :
    ¬ OrReaches n C C.output j := by
  intro hr
  have hv := reach_up n C (mono s false) C.output j hr (hboth false)
  change circuitFun n C (mono s false) = true at hv
  rw [hfun, graphFun_mono_false G s hbip false] at hv
  cases hv

lemma both_mono_frontier_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (j : ℕ) (hboth : ∀ c : Bool, gateVal n C j (mono s c) = true)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (hr : OrReaches n C (opnd C a b) j) : a ∈ junk G C := by
  obtain ⟨c, hc⟩ := operand_mono_activity G C s hAO hT hJ a ha hop (1 - b)
  have hb := reach_up n C (mono s c) _ j hr (hboth c)
  have hv : W n C (mono s c) (n + a) = true := by
    apply W_and n C (mono s c) a ha hop
    intro z hz
    obtain ⟨_, hin, h0, h1, _⟩ := gate2 hAO ha
    rw [hin] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    have hall : ∀ d : Fin 2, W n C (mono s c) (opnd C a d) = true := by
      intro d
      have hd : d = b ∨ d = 1 - b := by fin_cases b <;> fin_cases d <;> simp
      rcases hd with rfl | rfl <;> assumption
    rcases hz with rfl | rfl
    · exact ⟨h0, hall 0⟩
    · exact ⟨h1, hall 1⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hop, ha, mono s c, hv,
    graphFun_mono_false G s hbip c⟩

lemma junk_empty_of_all_both_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hboth : ∀ j ∈ junk G C, ∀ c : Bool, gateVal n C j (mono s c) = true) :
    junk G C = ∅ := by
  classical
  by_contra hne
  have hne := Finset.nonempty_iff_ne_empty.mpr hne
  let j := (junk G C).max' hne
  have hj : j ∈ junk G C := Finset.max'_mem _ hne
  have hjlt := (junk_data G C j hj).1
  have hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true :=
    fun k hk => ⟨false, hboth k hk false⟩
  obtain ⟨a, ha, hop, b, hr⟩ := and_frontier_of_live C hL.1
    (fun k hk hn => least_has_reader G C hL k hk hn) j hjlt
    (both_mono_not_or_output G C s hbip hL.2.1 j (hboth j hj))
  have haj := both_mono_frontier_junk G C s hbip hL.1 hT hJ j (hboth j hj) a ha hop b hr
  have hread := operand_mem C hL.1 a ha b
  have hcone := reach_cone n C a ha _ hread (hL.1.2.1 a ha _ hread) j hr
  have hlt := inCone_lt n C a j hcone
  have hmax := Finset.le_max' (junk G C) a haj
  change a ≤ j at hmax
  omega

lemma and_both_mono_of_mixed_sides {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hmix : ∀ b : Fin 2, ∀ c : Bool, ∃ i ∈ side (n := n) C j b, s i = c) :
    ∀ c : Bool, gateVal n C j (mono s c) = true := by
  intro c
  have hv : ∀ b : Fin 2, W n C (mono s c) (opnd C j b) = true := by
    intro b
    obtain ⟨i, hi, hc⟩ := hmix b c
    exact side_val n C (mono s c) j b i hi (by simp [mono, hc])
  apply W_and n C (mono s c) j hj hop
  intro z hz
  obtain ⟨_, hin, h0, h1, _⟩ := gate2 hAO hj
  rw [hin] at hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact ⟨h0, hv 0⟩
  · exact ⟨h1, hv 1⟩

lemma junk_empty_of_all_mixed_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hmix : ∀ j ∈ junk G C, ∀ b : Fin 2, ∀ c : Bool,
      ∃ i ∈ side (n := n) C j b, s i = c) : junk G C = ∅ := by
  apply junk_empty_of_all_both_mono G C s hbip hL hT
  intro j hj
  obtain ⟨hjlt, hop⟩ := junk_data G C j hj
  exact and_both_mono_of_mixed_sides C s hL.1 j hjlt hop (hmix j hj)

lemma exists_junk_monochromatic_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hne : (junk G C).Nonempty) :
    ∃ j ∈ junk G C, ∃ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C j b, s i = c := by
  classical
  by_contra hnone
  have hempty := junk_empty_of_all_mixed_sides G C s hbip hL hT (by
    intro j hj b
    apply not_monochromatic_mixed s _
    intro hmono
    exact hnone ⟨j, hj, b, hmono⟩)
  rw [hempty] at hne
  exact Finset.not_nonempty_empty hne

lemma both_mono_reaches_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (j : ℕ) (hj : j < C.gates.length)
    (hboth : ∀ c : Bool, gateVal n C j (mono s c) = true) :
    ∃ a ∈ junk G C, InCone n C j a := by
  obtain ⟨a, ha, hop, b, hr⟩ := and_frontier_of_live C hL.1
    (fun k hk hn => least_has_reader G C hL k hk hn) j hj
    (both_mono_not_or_output G C s hbip hL.2.1 j hboth)
  have haj := both_mono_frontier_junk G C s hbip hL.1 hT hJ j hboth a ha hop b hr
  have hread := operand_mem C hL.1 a ha b
  exact ⟨a, haj, reach_cone n C a ha _ hread (hL.1.2.1 a ha _ hread) j hr⟩

lemma two_junk_both_mono_forces_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hboth : ∀ c : Bool, gateVal n C g (mono s c) = true) : InCone n C g h := by
  have hgj : g ∈ junk G C := by rw [hpair]; simp
  obtain ⟨a, haj, hcone⟩ := both_mono_reaches_junk G C s hbip hL hT hJ g
    (junk_data G C g hgj).1 hboth
  rw [hpair] at haj
  simp only [Finset.mem_insert, Finset.mem_singleton] at haj
  rcases haj with rfl | rfl
  · have := inCone_lt n C _ _ hcone
    omega
  · exact hcone

lemma independent_junk_not_both_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h)
    (hboth : ∀ c : Bool, gateVal n C g (mono s c) = true) : False := by
  exact hgh (two_junk_both_mono_forces_cone G C s hbip hL hT hJ g h hpair hboth)

end BothMono

namespace CompleteRestricted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open MixedFrontier MixedCut

lemma opposite_pure_of_mixed_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bg : Fin 2) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h)
    (hmix : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c) :
    ∃ c : Bool, ∀ i ∈ side (n := n) C g (1-bg), s i = c := by
  by_contra hpure
  have hother := not_monochromatic_mixed s _ hpure
  have hgj : g ∈ junk G C := by rw [hpair]; simp
  obtain ⟨hglt, hgop⟩ := junk_data G C g hgj
  apply BothMono.independent_junk_not_both_mono G C s hbip hL hT hJ g h hpair hgh
  apply BothMono.and_both_mono_of_mixed_sides C s hL.1 g hglt hgop
  intro b
  have hb : b = bg ∨ b = 1-bg := by fin_cases b <;> fin_cases bg <;> simp
  rcases hb with rfl | rfl
  · exact hmix
  · exact hother

lemma independent_mixed_sides_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g,h}) (hne : g ≠ h)
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hmixg : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c)
    (hdisg : Disjoint (side (n := n) C g (1-bg)) (side (n := n) C g bg))
    (hdish : Disjoint (side (n := n) C h (1-bh)) (side (n := n) C h bh)) : False := by
  have hJ := JunkActivity.two_mixed_active G C s hL.1 hT g h bg bh hpair hgh hhg hmixg hmixh
  have hpair' : junk G C = {h,g} := by simpa [Finset.pair_comm] using hpair
  exact independent_semimixed_impossible G C s hbip hL hT g h bg bh hpair hne hgh hhg
    (opposite_pure_of_mixed_side G C s hbip hL hT hJ g h bg hpair hgh hmixg)
    (opposite_pure_of_mixed_side G C s hbip hL hT hJ h g bh hpair' hhg hmixh)
    hmixg hmixh hdisg hdish

end CompleteRestricted

namespace SingleMixedRoot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open MixedCut MixedReach MixedFrontier ActualCut

lemma pure_mixed_activity {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (cg : Bool) (hpureg : ∀ b : Fin 2, ∀ i ∈ side (n := n) C g b, s i = cg)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c) :
    ∀ a ∈ junk G C, ∃ c : Bool, gateVal n C a (mono s c) = true := by
  intro a ha
  have hamem : a ∈ ({g, h} : Finset ℕ) := by rwa [← hpair]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hamem
  rcases hamem with hag | hah
  · subst a
    obtain ⟨u, hu⟩ := JunkActivity.independent_side_nonempty G C hAO hT g h hpair hgh hhg g ha 0
    obtain ⟨v, hv⟩ := JunkActivity.independent_side_nonempty G C hAO hT g h hpair hgh hhg g ha 1
    apply product_active_mono_of_common_color C s g _ _
      (JunkActivity.independent_product G C hAO hT g h hpair hgh hhg g ha 0) u v hu hv
    exact (hpureg 0 u hu).trans (hpureg 1 v hv).symm
  · subst a
    exact JunkActivity.independent_mixed_active G C s hAO hT g h hpair hgh hhg h ha bh hmixh

lemma least_mixed_one_operand_coverage {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g, h})
    (hpureg : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1 - bh), s i = c)
    (j : ℕ) (hj : j < C.gates.length)
    (hmixed : ∀ c : Bool, ∃ i ∈ orIn n C (n + j), s i = c) :
    OrReaches n C (opnd C h bh) j := by
  obtain ⟨a, ha, b, hr, hm⟩ := least_mixed_reaches_mixed_junk_operand G C s hbip hL hT hJ
    j hj hmixed
  rw [hpair] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with hag | hah
  · subst a
    exact (mixed_not_monochromatic s _ hm (hpureg b)).elim
  · subst a
    have he := mixed_slot_unique C s h b bh hpureh hm
    exact he ▸ hr

lemma wires_one_root {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g, h})
    (hpureg : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1 - bh), s i = c) :
    ∀ w ∈ wires n C s g h,
      Relation.ReflTransGen (CountCut.cutOrStep n C (wires n C s g h)) w (opnd C h bh) := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  have hmem : n + k ∈ wires n C s g h := Finset.mem_image.mpr ⟨k, hk, rfl⟩
  obtain ⟨hkK, hmix⟩ := (mixedRegion_mem C s g h k).mp hk
  have hklt := ((region_mem C g h k).mp hkK).1
  have hr := least_mixed_one_operand_coverage G C s hbip hL hT hJ g h bh hpair hpureg hpureh
    k hklt hmix
  exact (CountCut.closed_path_is_cutPath n C _
    (wires_forward_closed G C s hbip hL hT hJ g h hpair) hmem
    (CountCut.orReaches_path n C _ k hr)).2

lemma sources_eq_boundary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1 - bh), s i = c) :
    BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C h bh) =
      boundary n C s g h := by
  have hroot := wires_one_root G C s hbip hL hT hJ g h bh hpair hpureg hpureh
  have hu := BoundarySources.two_sources_union n C (boundary n C s g h) (wires n C s g h)
    (opnd C h bh) (opnd C h bh)
    (boundary_used G C s hL.1 hT g h hpair hgh hhg)
    (fun j hj => Or.inl (hroot j hj))
  simpa only [Finset.union_self] using hu

lemma same_root_pairCost_le_mixedRegion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1 - bh), s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c) :
    TwoOrBuild.pairCost
      (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C h bh))
      (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C h bh)) ≤
      (mixedRegion n C s g h).card := by
  have hhj : h ∈ junk G C := by rw [hpair]; simp
  have hrh := mixed_operand_mem G C s hbip hL hT hJ g h hpair h hhj bh hmixh
  have hroot := wires_one_root G C s hbip hL hT hJ g h bh hpair hpureg hpureh
  have hbound := BoundarySources.pairCost_le_gates n C hL.1
    (boundary n C s g h) (wires n C s g h) (boundary_disjoint C s g h)
    (opnd C h bh) (opnd C h bh) hrh hrh
    (boundary_parents C s hL.1 g h)
    (boundary_used G C s hL.1 hT g h hpair hgh hhg)
    (fun j hj => Or.inl (hroot j hj))
    (sources_nonempty G C s hL.1 hT g h hpair hgh hhg _ hrh)
    (sources_nonempty G C s hL.1 hT g h hpair hgh hhg _ hrh)
  simpa only [wires_card] using hbound

lemma pure_junk_operand_raw_or_pure {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (hAO : IsAO2 n C) (g h : ℕ) (hg : g < C.gates.length)
    (hpureg : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c) (b : Fin 2) :
    opnd C g b < n ∨ ∃ k ∈ pureRegion n C s g h, opnd C g b = n + k := by
  rcases JunkActivity.operand_raw_or_region C hAO g h g (by simp) hg b with hraw | ⟨k, hk, heq⟩
  · exact Or.inl hraw
  · obtain ⟨c, hc⟩ := hpureg b
    have hc' : ∀ i ∈ orIn n C (n + k), s i = c := by
      rw [← heq]
      exact hc
    exact Or.inr ⟨k, Finset.mem_filter.mpr ⟨hk, c, hc'⟩, heq⟩

end SingleMixedRoot

namespace CompleteSingleMixed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open Reorder HoistTransport MixedFrontier MixedCut TwoOrBuild

lemma independent_pure_semimixed_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (cg : Bool) (hpureg : ∀ b : Fin 2, ∀ i ∈ side (n := n) C g b, s i = cg)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1-bh), s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c)
    (hdish : Disjoint (side (n := n) C h (1-bh)) (side (n := n) C h bh)) : False := by
  have hJ := SingleMixedRoot.pure_mixed_activity G C s hL.1 hT g h bh hpair hgh hhg cg hpureg hmixh
  obtain ⟨ch,hch⟩ := hpureh
  have hpureg' : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c :=
    fun b => ⟨cg,hpureg b⟩
  let P := boundedSet C.gates.length (pureRegion n C s g h)
  let K := boundedSet C.gates.length (region n C g h)
  let π := sortPerm (blockKey P K)
  have hPK : P ⊆ K := pureRegion_fin_subset C s g h
  have hPc : PredecessorClosed n C P := pureRegion_fin_closed G C s hL.1 hT g h hpair hgh hhg
  have hKc : PredecessorClosed n C K := region_fin_closed G C hL.1 hT g h hpair hgh hhg
  have hdep : DependencyOrder n C π := two_closed_hoist_dependency C hL.1 P K hPc hKc
  have hP : ∀ i, (π i).val < P.card ↔ i ∈ P := two_closed_hoist_prefix_small P K
  have hK : ∀ i, (π i).val < K.card ↔ i ∈ K := two_closed_hoist_prefix_large P K hPK
  have hgJ : g ∈ junk G C := by rw [hpair]; simp
  have hhJ : h ∈ junk G C := by rw [hpair]; simp
  let hf : Fin C.gates.length := ⟨h,(junk_data G C h hhJ).1⟩
  let J : Finset (Fin C.gates.length) := {hf}
  have hJK : Disjoint J K := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have heq : j = hf := Finset.mem_singleton.mp hj
    subst j
    exact junk_not_mem_region G C hL.1 hT g h hpair hgh hhg h hhJ
      ((boundedSet_mem _ _ _).mp hk)
  have hroot := ActualCut.mixed_operand_mem G C s hbip hL hT hJ g h hpair h hhJ bh hmixh
  let S := BoundarySources.sources n C (ActualCut.boundary n C s g h)
    (ActualCut.wires n C s g h) (opnd C h bh)
  let color := BoundaryColors.color (orIn n C) s
  have hS : ∀ w ∈ S, w < n ∨ ∃ j ∈ P, w = n + j.val := by
    intro w hw
    exact raw_or_pure_fin C s g h w
      (ActualBoundary.source_boundary_data G C s hL.1 hT g h hpair hgh hhg _ w hw).1
  have hSmix : HasBoth color S :=
    ActualBoundary.sources_hasBoth G C s hL.1 hT g h hpair hgh hhg _ hroot
  have hcost : pairCost S S ≤ K.card - P.card := by
    rw [← mixedRegion_card_sub C s g h]
    exact SingleMixedRoot.same_root_pairCost_le_mixedRegion G C s hbip hL hT hJ
      g h bh hpair hgh hhg hpureg' ⟨ch,hch⟩ hmixh
  obtain ⟨hs,wS,wT,hAO1,hAO2,hops,hlen,hwS,hwT,heval⟩ :=
    CompleteMixedCase.smaller_projection_prefix C hL.1 P K hPc hKc S S hS hS
      color (!ch) (!ch) hSmix hSmix hcost
  let targetWire : ℕ → ℕ := fun _ => wS
  have houtLo := OutputSupport.output_not_raw G C hL.2.1
  have houtHi := CriticalEdge.output_lt G C hL.2.1
    (CriticalEdge.least_nonempty_of_gate G C hL h hf.isLt)
  have hout := two_closed_hoist_output_suffix C P K hPK houtLo houtHi (by
    intro j hj
    exact OutputSupport.region_not_output G C hL.1 hL.2.1 hT g h hpair hgh hhg
      j.val ((boundedSet_mem _ _ _).mp hj))
  have hraw : ∀ b : Fin 2, ∀ x : Fin n → Bool,
      wireVal n C (opnd C h b) x = ColorProjection.setOr (side (n := n) C h b) x := by
    intro b x
    exact raw_or_region_wire_semantics G C hL.1 hT g h hpair hgh hhg _
      (JunkActivity.operand_raw_or_region C hL.1 g h h (by simp) hf.isLt b) x
  apply RegionProjection.projected_target_hoist_contradiction G C hL s hbip π hdep
    P K J hPK hP hK hJK ?_ hout hs targetWire hAO1 hlen (fun _ _ => hwS) ?_
  · intro i hi hip j hj hread
    have hjjunk := ActualStructure.external_reader_fin G C s hbip hL hT hJ g h hpair i j hi hip hj hread
    have hjpair : j.val ∈ ({g,h} : Finset ℕ) := by
      rw [← hpair]; exact (boundedSet_mem _ _ _).mp hjjunk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hjpair
    rcases hjpair with hjg | hjh
    · have hnotread : ∀ b : Fin 2, n + i.val ≠ opnd C g b := by
        intro b heq
        rcases SingleMixedRoot.pure_junk_operand_raw_or_pure C s hL.1 g h
          (junk_data G C g hgJ).1 hpureg' b with hraw | ⟨k,hk,hkval⟩
        · omega
        · have hki : k = i.val := by omega
          apply hip
          exact (boundedSet_mem _ _ _).mpr (hki ▸ hk)
      rw [hjg] at hread
      rcases ActualStructure.operand_pair C hL.1 g (junk_data G C g hgJ).1 0 with hin | hin
      · rw [hin] at hread
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hread
        exact (hread.elim (hnotread (1-0)) (hnotread 0)).elim
      · rw [hin] at hread
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hread
        exact (hread.elim (hnotread 0) (hnotread (1-0))).elim
    · exact Finset.mem_singleton.mpr (Fin.ext hjh)
  · intro j hj
    have heq : j = hf := Finset.mem_singleton.mp hj
    subst j
    refine ⟨opnd C h (1-bh),opnd C h bh,side C h (1-bh),side C h bh,ch,
      (junk_data G C h hhJ).2, ActualStructure.operand_pair C hL.1 h hf.isLt bh,
      ActualStructure.pure_operand_fin G C s hL.1 g h h hpair hhJ (1-bh) ⟨ch,hch⟩,
      ActualStructure.mixed_operand_fin C s g h _ hroot,hch,hdish,hraw (1-bh),hraw bh,?_⟩
    intro x
    exact (heval x).1.trans
      (ActualBoundary.source_projection_semantics G C s hL.1 hT g h hpair hgh hhg _ hroot (!ch) x)

end CompleteSingleMixed

namespace CompleteSingleMixed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open MixedFrontier MixedCut

lemma independent_pure_mixed_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (cg : Bool) (hpureg : ∀ b : Fin 2, ∀ i ∈ side (n := n) C g b, s i = cg)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c)
    (hdish : Disjoint (side (n := n) C h (1-bh)) (side (n := n) C h bh)) : False := by
  have hJ := SingleMixedRoot.pure_mixed_activity G C s hL.1 hT g h bh hpair hgh hhg cg hpureg hmixh
  have hpair' : junk G C = {h,g} := by simpa only [Finset.pair_comm] using hpair
  have hpureh := CompleteRestricted.opposite_pure_of_mixed_side G C s hbip hL hT hJ
    h g bh hpair' hhg hmixh
  exact independent_pure_semimixed_impossible G C s hbip hL hT g h bh hpair hgh hhg
    cg hpureg hpureh hmixh hdish

end CompleteSingleMixed

namespace DisjointColorCases
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open MixedFrontier MixedCut

lemma side_pair_disjoint {n : ℕ} (C : Circuit) (g : ℕ)
    (hdis : Disjoint (side (n := n) C g 0) (side (n := n) C g 1)) (b : Fin 2) :
    Disjoint (side (n := n) C g (1-b)) (side (n := n) C g b) := by
  fin_cases b
  · exact hdis.symm
  · exact hdis

lemma mixed_side_forces_other_opposite_pure {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (bg : Fin 2) (hpair : junk G C = {g,h}) (hne : g ≠ h)
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hmixg : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c)
    (hdisg : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (hdish : Disjoint (side (n := n) C h 0) (side (n := n) C h 1)) :
    ∃ c : Bool, (∀ i ∈ side (n := n) C h 0, s i = c) ∧
      (∀ i ∈ side (n := n) C h 1, s i = !c) := by
  have hallpure : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C h b, s i = c := by
    intro b
    by_contra hpure
    have hmixh := not_monochromatic_mixed s _ hpure
    exact CompleteRestricted.independent_mixed_sides_impossible G C s hbip hL hT g h bg b
      hpair hne hgh hhg hmixg hmixh (side_pair_disjoint C g hdisg bg) (side_pair_disjoint C h hdish b)
  obtain ⟨c0,hc0⟩ := hallpure 0
  obtain ⟨c1,hc1⟩ := hallpure 1
  have hnecolor : c0 ≠ c1 := by
    intro heq
    have hpure : ∀ b : Fin 2, ∀ i ∈ side (n := n) C h b, s i = c0 := by
      intro b
      fin_cases b
      · exact hc0
      · intro i hi
        exact (hc1 i hi).trans heq.symm
    have hpair' : junk G C = {h,g} := by simpa only [Finset.pair_comm] using hpair
    exact CompleteSingleMixed.independent_pure_mixed_impossible G C s hbip hL hT h g bg
      hpair' hhg hgh c0 hpure hmixg (side_pair_disjoint C g hdisg bg)
  have hc1eq : c1 = !c0 := by cases c0 <;> cases c1 <;> simp_all
  exact ⟨c0,hc0,fun i hi => (hc1 i hi).trans hc1eq⟩


lemma independent_disjoint_color_cases {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g,h}) (hne : g ≠ h)
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hdisg : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (hdish : Disjoint (side (n := n) C h 0) (side (n := n) C h 1)) :
    (∀ a ∈ junk G C, ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C a b, s i = c) ∨
    ((∃ bg : Fin 2, ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c) ∧
      ∃ c : Bool, (∀ i ∈ side (n := n) C h 0, s i = c) ∧
        (∀ i ∈ side (n := n) C h 1, s i = !c)) ∨
    ((∃ bh : Fin 2, ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c) ∧
      ∃ c : Bool, (∀ i ∈ side (n := n) C g 0, s i = c) ∧
        (∀ i ∈ side (n := n) C g 1, s i = !c)) := by
  by_cases hgmix : ∃ bg : Fin 2, ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c
  · obtain ⟨bg,hmix⟩ := hgmix
    exact Or.inr (Or.inl ⟨⟨bg,hmix⟩, mixed_side_forces_other_opposite_pure G C s hbip hL hT
      g h bg hpair hne hgh hhg hmix hdisg hdish⟩)
  by_cases hhmix : ∃ bh : Fin 2, ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c
  · obtain ⟨bh,hmix⟩ := hhmix
    have hpair' : junk G C = {h,g} := by simpa only [Finset.pair_comm] using hpair
    exact Or.inr (Or.inr ⟨⟨bh,hmix⟩, mixed_side_forces_other_opposite_pure G C s hbip hL hT
      h g bh hpair' (Ne.symm hne) hhg hgh hmix hdish hdisg⟩)
  apply Or.inl
  intro a ha b
  rw [hpair] at ha
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · by_contra hpure
    exact hgmix ⟨b,not_monochromatic_mixed s _ hpure⟩
  · by_contra hpure
    exact hhmix ⟨b,not_monochromatic_mixed s _ hpure⟩

end DisjointColorCases

namespace BothMono

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open MixedFrontier MixedCut

lemma both_mono_other_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h}) (hgh : ¬ InCone n C g h)
    (hboth : ∀ c : Bool, gateVal n C g (mono s c) = true) :
    ∀ c : Bool, gateVal n C h (mono s c) = false := by
  intro c
  apply Bool.eq_false_iff.mpr
  intro hc
  apply independent_junk_not_both_mono G C s hbip hL hT ?_ g h hpair hgh hboth
  intro a ha
  rw [hpair] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨false, hboth false⟩
  · exact ⟨c, hc⟩

lemma product_opposite_pure_of_mono_false {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (j : ℕ) (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (heval : ∀ x : Fin n → Bool, gateVal n C j x =
      (ColorProjection.setOr A x && ColorProjection.setOr B x))
    (hfalse : ∀ c : Bool, gateVal n C j (mono s c) = false) :
    ∃ c : Bool, (∀ a ∈ A, s a = c) ∧ ∀ b ∈ B, s b = !c := by
  have hsep : ∀ a ∈ A, ∀ b ∈ B, s a ≠ s b := by
    intro a ha b hb hab
    obtain ⟨c, hc⟩ := product_active_mono_of_common_color C s j A B heval a b ha hb hab
    rw [hfalse c] at hc
    cases hc
  have hbool : ∀ a b : Bool, a ≠ b → a = !b := by decide
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hbcol : s b = !(s a) := hbool _ _ (Ne.symm (hsep a ha b hb))
  refine ⟨s a, ?_, ?_⟩
  · intro u hu
    have hu := hbool _ _ (hsep u hu b hb)
    simpa only [hbcol, Bool.not_not] using hu
  · intro v hv
    exact hbool _ _ (Ne.symm (hsep a ha v hv))

lemma both_mono_other_opposite_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hboth : ∀ c : Bool, gateVal n C g (mono s c) = true) :
    ∃ c : Bool, (∀ i ∈ side (n := n) C h 0, s i = c) ∧
      ∀ i ∈ side (n := n) C h 1, s i = !c := by
  have hhj : h ∈ junk G C := by rw [hpair]; simp
  apply product_opposite_pure_of_mono_false C s h _ _
    (JunkActivity.independent_side_nonempty G C hL.1 hT g h hpair hgh hhg h hhj 0)
    (JunkActivity.independent_side_nonempty G C hL.1 hT g h hpair hgh hhg h hhj 1)
  · exact JunkActivity.independent_product G C hL.1 hT g h hpair hgh hhg h hhj 0
  · exact both_mono_other_false G C s hbip hL hT g h hpair hgh hboth

lemma mixed_sides_other_opposite_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hmix : ∀ b : Fin 2, ∀ c : Bool, ∃ i ∈ side (n := n) C g b, s i = c) :
    ∃ c : Bool, (∀ i ∈ side (n := n) C h 0, s i = c) ∧
      ∀ i ∈ side (n := n) C h 1, s i = !c := by
  apply both_mono_other_opposite_pure G C s hbip hL hT g h hpair hgh hhg
  have hgj : g ∈ junk G C := by rw [hpair]; simp
  obtain ⟨hglt, hgop⟩ := junk_data G C g hgj
  exact and_both_mono_of_mixed_sides C s hL.1 g hglt hgop hmix

end BothMono

namespace JunkAntichain
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open MixedFrontier MixedCut

lemma setOr_and_eq_left_of_subset {n : ℕ} (A B : Finset (Fin n))
    (hsub : A ⊆ B) (x : Fin n → Bool) :
    (ColorProjection.setOr A x && ColorProjection.setOr B x) = ColorProjection.setOr A x := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, ColorProjection.setOr, decide_eq_true_eq]
  constructor
  · exact fun h => h.1
  · rintro ⟨i,hi,hx⟩
    exact ⟨⟨i,hi,hx⟩,⟨i,hsub hi,hx⟩⟩

lemma independent_side_not_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g,h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2) :
    ¬ side (n := n) C a b ⊆ side (n := n) C a (1-b) := by
  intro hsub
  have halt := (junk_data G C a ha).1
  have hb := hL.1.2.1 a halt _ (operand_mem C hL.1 a halt b)
  have hapair : a ∈ ({g,h} : Finset ℕ) := by rwa [← hpair]
  have heq : ∀ x : Fin n → Bool, wireVal n C (opnd C a b) x = gateVal n C a x := by
    intro x
    rw [JunkActivity.independent_product G C hL.1 hT g h hpair hgh hhg a ha b x,
      setOr_and_eq_left_of_subset _ _ hsub x]
    exact raw_or_region_wire_semantics G C hL.1 hT g h hpair hgh hhg _
      (JunkActivity.operand_raw_or_region C hL.1 g h a hapair halt b) x
  apply CriticalEdge.least_no_edge_equivalent_earlier_wire G C hL a (opnd C a b) hb halt
  · intro x hx
    rwa [heq x] at hx
  · intro u v _
    exact heq (pairInput u v)

lemma independent_singleton_side_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g,h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2)
    (hcard : (side (n := n) C a b).card = 1) :
    Disjoint (side (n := n) C a b) (side (n := n) C a (1-b)) := by
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hcard
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  apply independent_side_not_subset G C hL hT g h hpair hgh hhg a ha b
  intro j hj
  have hiv : i = v := by simpa only [hv,Finset.mem_singleton] using hi
  have hjv : j = v := by simpa only [hv,Finset.mem_singleton] using hj
  simpa only [hiv,hjv] using hi'

lemma independent_either_singleton_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g,h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C)
    (hcard : (side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) := by
  rcases hcard with hc | hc
  · exact independent_singleton_side_disjoint G C hL hT g h hpair hgh hhg a ha 0 hc
  · exact (independent_singleton_side_disjoint G C hL hT g h hpair hgh hhg a ha 1 hc).symm

end JunkAntichain

namespace SingletonCases
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open MixedFrontier MixedCut

lemma independent_has_singleton_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hpair : junk G C = {g,h}) (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C)
    (hsingle : ∃ b : Fin 2, (side (n := n) C a b).card = 1) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) := by
  apply JunkAntichain.independent_either_singleton_disjoint G C hL hT g h hpair hgh hhg a ha
  obtain ⟨b,hb⟩ := hsingle
  fin_cases b
  · exact Or.inl hb
  · exact Or.inr hb

lemma independent_mixed_sides_singleton_impossible {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g,h}) (hne : g ≠ h)
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hmixg : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c)
    (hsingleg : ∃ b : Fin 2, (side (n := n) C g b).card = 1)
    (hsingleh : ∃ b : Fin 2, (side (n := n) C h b).card = 1) : False := by
  have hgJ : g ∈ junk G C := by rw [hpair]; simp
  have hhJ : h ∈ junk G C := by rw [hpair]; simp
  have hdisg := independent_has_singleton_disjoint G C hL hT g h hpair hgh hhg g hgJ hsingleg
  have hdish := independent_has_singleton_disjoint G C hL hT g h hpair hgh hhg h hhJ hsingleh
  exact CompleteRestricted.independent_mixed_sides_impossible G C s hbip hL hT g h bg bh
    hpair hne hgh hhg hmixg hmixh (DisjointColorCases.side_pair_disjoint C g hdisg bg)
    (DisjointColorCases.side_pair_disjoint C h hdish bh)

lemma independent_pure_mixed_singleton_impossible {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (cg : Bool) (hpureg : ∀ b : Fin 2, ∀ i ∈ side (n := n) C g b, s i = cg)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c)
    (hsingleh : ∃ b : Fin 2, (side (n := n) C h b).card = 1) : False := by
  have hhJ : h ∈ junk G C := by rw [hpair]; simp
  have hdish := independent_has_singleton_disjoint G C hL hT g h hpair hgh hhg h hhJ hsingleh
  exact CompleteSingleMixed.independent_pure_mixed_impossible G C s hbip hL hT g h bh
    hpair hgh hhg cg hpureg hmixh (DisjointColorCases.side_pair_disjoint C h hdish bh)

end SingletonCases

namespace PureOpposite
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open MixedFrontier MixedCut ColorProjection

lemma same_color_product_pair_overlap {n : ℕ} (A B : Finset (Fin n))
    (s : Fin n → Bool) (c : Bool)
    (hA : ∀ i ∈ A, s i = c) (hB : ∀ i ∈ B, s i = c)
    (p q : Fin n) (hpq : s p ≠ s q)
    (htrue : (setOr A (pairInput p q) && setOr B (pairInput p q)) = true) :
    (A ∩ B).Nonempty := by
  have hboth : setOr A (pairInput p q) = true ∧ setOr B (pairInput p q) = true := by
    simpa only [Bool.and_eq_true] using htrue
  obtain ⟨hleft,hright⟩ := hboth
  obtain ⟨u,hu,hupair⟩ := of_decide_eq_true hleft
  obtain ⟨v,hv,hvpair⟩ := of_decide_eq_true hright
  have huPQ : u = p ∨ u = q := by simpa only [pairInput,decide_eq_true_eq] using hupair
  have hvPQ : v = p ∨ v = q := by simpa only [pairInput,decide_eq_true_eq] using hvpair
  have huv : u = v := by
    rcases huPQ with rfl | rfl <;> rcases hvPQ with rfl | rfl
    · rfl
    · exact (hpq ((hA _ hu).trans (hB _ hv).symm)).elim
    · exact (hpq ((hB _ hv).trans (hA _ hu).symm)).elim
    · rfl
  exact ⟨u,Finset.mem_inter.mpr ⟨hu,huv.symm ▸ hv⟩⟩

lemma independent_same_color_intersection {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C) (c : Bool)
    (hpure : ∀ b : Fin 2, ∀ i ∈ side (n := n) C a b, s i = c) :
    (side (n := n) C a 0 ∩ side (n := n) C a 1).Nonempty := by
  obtain ⟨p,q,hpq,hgate,_⟩ := CriticalEdge.least_gate_critical_edge_of_least G C hL a
    (junk_data G C a ha).1
  rw [JunkActivity.independent_product G C hL.1 hT g h hpair hgh hhg a ha 0] at hgate
  exact same_color_product_pair_overlap _ _ s c (hpure 0) (hpure 1) p q (hbip p q hpq) hgate

lemma independent_disjoint_pure_opposite {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C)
    (hdis : Disjoint (side (n := n) C a 0) (side (n := n) C a 1))
    (hpure : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C a b, s i = c) :
    ∃ c : Bool, (∀ i ∈ side (n := n) C a 0, s i = c) ∧
      (∀ i ∈ side (n := n) C a 1, s i = !c) := by
  obtain ⟨c0,hc0⟩ := hpure 0
  obtain ⟨c1,hc1⟩ := hpure 1
  have hne : c0 ≠ c1 := by
    intro heq
    have hsame : ∀ b : Fin 2, ∀ i ∈ side (n := n) C a b, s i = c0 := by
      intro b
      fin_cases b
      · exact hc0
      · intro i hi
        exact (hc1 i hi).trans heq.symm
    obtain ⟨i,hi⟩ := independent_same_color_intersection G C s hbip hL hT g h hpair hgh hhg a ha c0 hsame
    exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hi).2
  have hc1eq : c1 = !c0 := by cases c0 <;> cases c1 <;> simp_all
  exact ⟨c0,hc0,fun i hi => (hc1 i hi).trans hc1eq⟩

lemma independent_disjoint_opposite_color_cases {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g,h}) (hne : g ≠ h)
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hdisg : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (hdish : Disjoint (side (n := n) C h 0) (side (n := n) C h 1)) :
    (∀ a ∈ junk G C, ∃ c : Bool, (∀ i ∈ side (n := n) C a 0, s i = c) ∧
      (∀ i ∈ side (n := n) C a 1, s i = !c)) ∨
    ((∃ bg : Fin 2, ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c) ∧
      ∃ c : Bool, (∀ i ∈ side (n := n) C h 0, s i = c) ∧
        (∀ i ∈ side (n := n) C h 1, s i = !c)) ∨
    ((∃ bh : Fin 2, ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c) ∧
      ∃ c : Bool, (∀ i ∈ side (n := n) C g 0, s i = c) ∧
        (∀ i ∈ side (n := n) C g 1, s i = !c)) := by
  rcases DisjointColorCases.independent_disjoint_color_cases G C s hbip hL hT g h hpair hne
      hgh hhg hdisg hdish with hallpure | hmixed
  · apply Or.inl
    intro a ha
    have hdis : Disjoint (side (n := n) C a 0) (side (n := n) C a 1) := by
      have hapair := ha
      rw [hpair] at hapair
      simp only [Finset.mem_insert,Finset.mem_singleton] at hapair
      rcases hapair with rfl | rfl
      · exact hdisg
      · exact hdish
    exact independent_disjoint_pure_opposite G C s hbip hL hT g h hpair hgh hhg a ha hdis (hallpure a ha)
  · exact Or.inr hmixed

end PureOpposite

namespace GuardProjection

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open ColorProjection

lemma dirty_guard_excludes_center_filter {n : ℕ}
    (F f : (Fin n → Bool) → Bool) (u : Fin n) (E : Finset (Fin n))
    (hdirty : ∃ x, f x = true ∧ F x = false)
    (hguard : ∀ x, f x = true → x u = true)
    (hclean : ∀ x, f x = true → setOr E x = true → F x = true) : u ∉ E := by
  intro hu
  obtain ⟨x, hfx, hFx⟩ := hdirty
  have he : setOr E x = true := decide_eq_true ⟨u, hu, hguard x hfx⟩
  have hf := hclean x hfx he
  rw [hFx] at hf
  contradiction

lemma project_preserves_center_edges {n : ℕ} (s : Fin n → Bool) (u : Fin n)
    (E : Finset (Fin n)) (hu : u ∉ E) (v : Fin n) (huv : s u ≠ s v) :
    setOr (project E s (!(s u))) (pairInput u v) = setOr E (pairInput u v) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact project_le E s (!(s u)) _
  · intro he
    obtain ⟨w, hw, hx⟩ := of_decide_eq_true he
    have hwpair : w = u ∨ w = v := by simpa [pairInput] using hx
    have hwv : w = v := hwpair.resolve_left (fun heq => hu (heq ▸ hw))
    subst w
    have hvc : s v = !(s u) := by cases hsu : s u <;> cases hsv : s v <;> simp_all
    exact decide_eq_true ⟨v, Finset.mem_filter.mpr ⟨hw, hvc⟩, hx⟩

lemma clean_filter_projection_preserves_guard_edges {n : ℕ}
    (F f : (Fin n → Bool) → Bool) (s : Fin n → Bool) (u : Fin n)
    (E : Finset (Fin n)) (hdirty : ∃ x, f x = true ∧ F x = false)
    (hguard : ∀ x, f x = true → x u = true)
    (hclean : ∀ x, f x = true → setOr E x = true → F x = true)
    (v : Fin n) (huv : s u ≠ s v) :
    setOr (project E s (!(s u))) (pairInput u v) = setOr E (pairInput u v) := by
  exact project_preserves_center_edges s u E
    (dirty_guard_excludes_center_filter F f u E hdirty hguard hclean) v huv

end GuardProjection

namespace TwoOrBuild

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma all_subsets_two_build (n : ℕ) (C : Circuit) (hC : TopForm.IsAO2 n C)
    (R : Finset ℕ) (hR : ∀ w ∈ R, w < n + C.gates.length) (hcard : R.card ≤ 2) :
    ∃ (hs : List Gate) (o : Finset ℕ → Option ℕ),
      TopForm.IsAO2 n ⟨C.gates ++ hs, 0⟩ ∧
      hs.length = R.card - 1 ∧ hs.length ≤ 1 ∧
      (∀ g ∈ hs, g.op = GateOp.or) ∧
      ∀ S : Finset ℕ, S ⊆ R →
        (o S = none ↔ S = ∅) ∧
        (∀ w : ℕ, S = {w} → o S = some w) ∧
        (∀ w : ℕ, o S = some w → w < n + (C.gates ++ hs).length) ∧
        ∀ x : List Bool, x.length = n →
          ov (C.gates ++ hs) x (o S) = sourceOr C.gates x S := by
  classical
  obtain ⟨hs, full, hok, hlen, hops, hnone, hvalid, hval⟩ :=
    or_list_build n C.gates (ao_ok C hC) R.toList (by
      intro w hw
      exact hR w (Finset.mem_toList.mp hw))
  have hlen' : hs.length = R.card - 1 := by simpa using hlen
  have heach : ∀ S : Finset ℕ, ∃ out : Option ℕ, S ⊆ R →
      (out = none ↔ S = ∅) ∧
      (∀ w : ℕ, S = {w} → out = some w) ∧
      (∀ w : ℕ, out = some w → w < n + (C.gates ++ hs).length) ∧
      ∀ x : List Bool, x.length = n →
        ov (C.gates ++ hs) x out = sourceOr C.gates x S := by
    intro S
    by_cases hS : S ⊆ R
    · by_cases hzero : S = ∅
      · subst S
        refine ⟨none, fun _ => ⟨by simp, ?_, ?_, ?_⟩⟩
        · intro w hw
          simp at hw
        · intro w hw
          cases hw
        · intro x hx
          simp [ov, sourceOr]
      · by_cases hone : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hone
          have hwR : w ∈ R := hS (by simp)
          have hw := hR w hwR
          refine ⟨some w, fun _ => ⟨by simp, ?_, ?_, ?_⟩⟩
          · intro v hv
            exact congrArg some (Finset.singleton_injective hv)
          · intro v hv
            cases hv
            simp only [List.length_append]
            omega
          · intro x hx
            change (run (C.gates ++ hs) x).getD w false = _
            rw [run_prefix C.gates hs x w (by simpa only [hx] using hw)]
            simp [sourceOr]
        · have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
          have hle := Finset.card_le_card hS
          have heq : S = R := Finset.eq_of_subset_of_card_le hS (by omega)
          subst S
          refine ⟨full, fun _ => ⟨?_, ?_, hvalid, ?_⟩⟩
          · simpa only [Finset.toList_eq_nil] using hnone
          · intro w hw
            have hc : R.card = 1 := by rw [hw]; simp
            exact (hone hc).elim
          · intro x hx
            rw [sourceOr_list]
            exact hval x hx
    · exact ⟨none, fun hs => (hS hs).elim⟩
  choose o ho using heach
  exact ⟨hs, o, ok_ao hok, hlen', by omega, hops, ho⟩

end TwoOrBuild

namespace TwoOrBuild

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma retained_color_and_centers_build (n : ℕ) (C : Circuit) (hC : TopForm.IsAO2 n C)
    (color : ℕ → Bool) (c : Bool) (S R : Finset ℕ)
    (hS : ∀ w ∈ S, w < n + C.gates.length)
    (hR : ∀ w ∈ R, w < n + C.gates.length)
    (hBoth : HasBoth color S) (hcard : R.card ≤ 2) :
    ∃ (hs : List Gate) (good : ℕ) (o : Finset ℕ → Option ℕ),
      TopForm.IsAO2 n ⟨C.gates ++ hs, 0⟩ ∧
      (∀ g ∈ hs, g.op = GateOp.or) ∧ hs.length ≤ S.card - 1 ∧
      good < n + (C.gates ++ hs).length ∧
      (∀ x : List Bool, x.length = n →
        ov (C.gates ++ hs) x (some good) = sourceOr C.gates x (projectColor color c S)) ∧
      ∀ T : Finset ℕ, T ⊆ R →
        (o T = none ↔ T = ∅) ∧
        (∀ w : ℕ, T = {w} → o T = some w) ∧
        (∀ w : ℕ, o T = some w → w < n + (C.gates ++ hs).length) ∧
        ∀ x : List Bool, x.length = n →
          ov (C.gates ++ hs) x (o T) = sourceOr C.gates x T := by
  classical
  let G := projectColor color c S
  have hgood : G.Nonempty := project_nonempty color c S hBoth
  have hGsrc : ∀ w ∈ G, w < n + C.gates.length :=
    fun w hw => hS w (project_subset color c S hw)
  obtain ⟨hg, out, hok, hlen, hops, hnone, hvalid, hval⟩ :=
    or_list_build n C.gates (ao_ok C hC) G.toList (by
      intro w hw
      exact hGsrc w (Finset.mem_toList.mp hw))
  have hlenG : hg.length = G.card - 1 := by simpa using hlen
  cases out with
  | none =>
    have hempty : G = ∅ := by simpa only [Finset.toList_eq_nil] using hnone.mp rfl
    exact (hgood.ne_empty hempty).elim
  | some good =>
    have hgoodBound := hvalid good rfl
    have hgoodSem : ∀ x : List Bool, x.length = n →
        ov (C.gates ++ hg) x (some good) = sourceOr C.gates x G := by
      intro x hx
      rw [sourceOr_list]
      exact hval x hx
    obtain ⟨hr, o, hAO, hlenR, hshortR, hopsR, hmap⟩ :=
      all_subsets_two_build n ⟨C.gates ++ hg, 0⟩ (ok_ao hok) R (by
        intro w hw
        have := hR w hw
        simp only [List.length_append]
        omega) hcard
    refine ⟨hg ++ hr, good, o, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.append_assoc] using hAO
    · intro g hgmem
      rcases List.mem_append.mp hgmem with hh | hh
      · exact hops g hh
      · exact hopsR g hh
    · have hpos := Finset.card_pos.mpr hgood
      have hlt : G.card < S.card := project_card_lt color c S hBoth
      simp only [List.length_append]
      omega
    · simp only [List.length_append] at hgoodBound ⊢
      omega
    · intro x hx
      rw [← List.append_assoc]
      rw [ov_ext (C.gates ++ hg) hr x (some good) (by
        intro w hw
        cases hw
        simpa only [hx] using hgoodBound)]
      exact hgoodSem x hx
    · intro T hT
      obtain ⟨hnoneT, hsingleT, hboundT, hsemT⟩ := hmap T hT
      refine ⟨hnoneT, hsingleT, ?_, ?_⟩
      · intro w hw
        simpa only [List.append_assoc] using hboundT w hw
      · intro x hx
        rw [← List.append_assoc, hsemT x hx]
        exact sourceOr_prefix C.gates hg x T (by
          intro w hw
          simpa only [hx] using hR w (hT hw))

end TwoOrBuild

namespace StructuralCut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open MixedFrontier MixedReach MixedCut ActualCut CountCut

lemma orPath_nondecreasing {n : ℕ} (C : Circuit) {u v : ℕ}
    (hp : Relation.ReflTransGen (orWireStep n C) u v) : u ≤ v := by
  induction hp with
  | refl => exact le_rfl
  | tail _ hs ih =>
    obtain ⟨j,hj,rfl,hop,hread,hlt⟩ := hs
    omega

lemma orIn_subset_orPath {n : ℕ} (C : Circuit) {u v : ℕ}
    (hp : Relation.ReflTransGen (orWireStep n C) u v) : orIn n C u ⊆ orIn n C v := by
  induction hp with
  | refl => exact Finset.Subset.refl _
  | tail _ hs ih =>
    obtain ⟨j,hj,rfl,hop,hread,hlt⟩ := hs
    exact Finset.Subset.trans ih (orIn_or_step C j hj hop _ hread hlt)

lemma region_path_is_cutPath {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    {u v : ℕ} (hu : n ≤ u) (hmix : ∀ c : Bool, ∃ i ∈ orIn n C u, s i = c)
    (hp : Relation.ReflTransGen (orWireStep n C) u v)
    (hv : ∃ k ∈ region n C g h, v = n + k) :
    Relation.ReflTransGen (cutOrStep n C (wires n C s g h)) u v := by
  revert hv
  induction hp with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail w v hp hs ih =>
    intro hv
    obtain ⟨j,hj,rfl,hop,hread,hlt⟩ := hs
    obtain ⟨k,hk,hkj⟩ := hv
    have heq : k = j := by omega
    subst k
    have hwn : n ≤ w := le_trans hu (orPath_nondecreasing C hp)
    have hweq : w = n + (w-n) := by omega
    have hwK : w-n ∈ region n C g h :=
      region_predecessor_closed G C hAO hT g h hpair hgh hhg j hk (w-n) (by rwa [← hweq])
    have hprev := ih ⟨w-n,hwK,hweq⟩
    have hsub := orIn_subset_orPath C (hp.tail ⟨j,hj,rfl,hop,hread,hlt⟩)
    have hmixj : ∀ c : Bool, ∃ i ∈ orIn n C (n+j), s i = c := by
      intro c
      obtain ⟨i,hi,hc⟩ := hmix c
      exact ⟨i,hsub hi,hc⟩
    have hjQ : j ∈ mixedRegion n C s g h := (mixedRegion_mem C s g h j).mpr ⟨hk,hmixj⟩
    exact hprev.tail ⟨⟨j,hj,rfl,hop,hread,hlt⟩,Finset.mem_image.mpr ⟨j,hjQ,rfl⟩⟩


lemma mixed_operand_mem_wires {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C)
    (g h : ℕ) (hpair : junk G C = {g,h}) (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2)
    (hmix : ∀ c : Bool, ∃ i ∈ side (n := n) C a b, s i = c) :
    opnd C a b ∈ wires n C s g h := by
  have hapair : a ∈ ({g,h} : Finset ℕ) := by rwa [← hpair]
  rcases JunkActivity.operand_raw_or_region C hAO g h a hapair (junk_data G C a ha).1 b with
    hraw | ⟨k,hk,heq⟩
  · exact (mixed_not_monochromatic s _ hmix
      (raw_or_pure_support_monochromatic C s g h _ (Or.inl hraw))).elim
  · refine Finset.mem_image.mpr ⟨k,(mixedRegion_mem C s g h k).mpr ⟨hk,?_⟩,heq.symm⟩
    simpa only [side,heq] using hmix

lemma operand_reaches_mixed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C)
    (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2) (k : ℕ)
    (hmix : ∀ c : Bool, ∃ i ∈ orIn n C (n+k), s i = c)
    (hr : OrReaches n C (opnd C a b) k) :
    ∀ c : Bool, ∃ i ∈ side (n := n) C a b, s i = c := by
  have halt := (junk_data G C a ha).1
  have hbound := hAO.2.1 a halt _ (operand_mem C hAO a halt b)
  have hsub := orIn_subset_of_orReaches C _ k (by omega) hr
  intro c
  obtain ⟨i,hi,hc⟩ := hmix c
  exact ⟨i,hsub hi,hc⟩

lemma operand_reaches_cutPath {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (a : ℕ) (ha : a ∈ junk G C) (b : Fin 2) (k : ℕ)
    (hmix : ∀ c : Bool, ∃ i ∈ orIn n C (n+k), s i = c)
    (hr : OrReaches n C (opnd C a b) k) :
    Relation.ReflTransGen (cutOrStep n C (wires n C s g h)) (n+k) (opnd C a b) := by
  have hapair : a ∈ ({g,h} : Finset ℕ) := by rwa [← hpair]
  have hroot := JunkActivity.operand_raw_or_region C hAO g h a hapair (junk_data G C a ha).1 b
  rcases hroot with hraw | hK
  · have := hr.1
    omega
  · exact region_path_is_cutPath G C s hAO hT g h hpair hgh hhg (by omega) hmix
      (orReaches_path n C _ k hr) hK

lemma wires_two_roots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∃ c : Bool, ∀ i ∈ side (n := n) C g (1-bg), s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1-bh), s i = c) :
    ∀ w ∈ wires n C s g h,
      Relation.ReflTransGen (cutOrStep n C (wires n C s g h)) w (opnd C g bg) ∨
      Relation.ReflTransGen (cutOrStep n C (wires n C s g h)) w (opnd C h bh) := by
  intro w hw
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hkK,hmix⟩ := (mixedRegion_mem C s g h k).mp hk
  obtain ⟨hklt,a,hapair,b,hr⟩ := (region_mem C g h k).mp hkK
  have ha : a ∈ junk G C := by rwa [hpair]
  have hmroot := operand_reaches_mixed G C s hAO a ha b k hmix hr
  have hp := operand_reaches_cutPath G C s hAO hT g h hpair hgh hhg a ha b k hmix hr
  simp only [Finset.mem_insert,Finset.mem_singleton] at hapair
  rcases hapair with hag | hah
  · subst a
    have hb := mixed_slot_unique C s g b bg hpureg hmroot
    exact Or.inl (hb ▸ hp)
  · subst a
    have hb := mixed_slot_unique C s h b bh hpureh hmroot
    exact Or.inr (hb ▸ hp)

lemma wires_one_root {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1-bh), s i = c) :
    ∀ w ∈ wires n C s g h,
      Relation.ReflTransGen (cutOrStep n C (wires n C s g h)) w (opnd C h bh) := by
  intro w hw
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hkK,hmix⟩ := (mixedRegion_mem C s g h k).mp hk
  obtain ⟨hklt,a,hapair,b,hr⟩ := (region_mem C g h k).mp hkK
  have ha : a ∈ junk G C := by rwa [hpair]
  have hmroot := operand_reaches_mixed G C s hAO a ha b k hmix hr
  have hp := operand_reaches_cutPath G C s hAO hT g h hpair hgh hhg a ha b k hmix hr
  simp only [Finset.mem_insert,Finset.mem_singleton] at hapair
  rcases hapair with hag | hah
  · subst a
    exact (mixed_not_monochromatic s _ hmroot (hpureg b)).elim
  · subst a
    have hb := mixed_slot_unique C s h b bh hpureh hmroot
    exact hb ▸ hp


lemma pairCost_le_mixedRegion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∃ c : Bool, ∀ i ∈ side (n := n) C g (1-bg), s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1-bh), s i = c)
    (hmixg : ∀ c : Bool, ∃ i ∈ side (n := n) C g bg, s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c) :
    TwoOrBuild.pairCost
      (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C g bg))
      (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C h bh)) ≤
      (mixedRegion n C s g h).card := by
  have hgJ : g ∈ junk G C := by rw [hpair]; simp
  have hhJ : h ∈ junk G C := by rw [hpair]; simp
  have hrg := mixed_operand_mem_wires G C s hAO g h hpair g hgJ bg hmixg
  have hrh := mixed_operand_mem_wires G C s hAO g h hpair h hhJ bh hmixh
  have hbound := BoundarySources.pairCost_le_gates n C hAO
    (boundary n C s g h) (wires n C s g h) (boundary_disjoint C s g h)
    (opnd C g bg) (opnd C h bh) hrg hrh
    (boundary_parents C s hAO g h)
    (boundary_used G C s hAO hT g h hpair hgh hhg)
    (StructuralCut.wires_two_roots G C s hAO hT g h bg bh hpair hgh hhg hpureg hpureh)
    (sources_nonempty G C s hAO hT g h hpair hgh hhg _ hrg)
    (sources_nonempty G C s hAO hT g h hpair hgh hhg _ hrh)
  simpa only [wires_card] using hbound

lemma one_root_sources_eq_boundary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1-bh), s i = c) :
    BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C h bh) =
      boundary n C s g h := by
  have hr := StructuralCut.wires_one_root G C s hAO hT g h bh hpair hgh hhg hpureg hpureh
  have heq := BoundarySources.two_sources_union n C (boundary n C s g h) (wires n C s g h)
    (opnd C h bh) (opnd C h bh) (boundary_used G C s hAO hT g h hpair hgh hhg)
    (fun w hw => Or.inl (hr w hw))
  simpa only [Finset.union_self] using heq

lemma same_root_pairCost_le_mixedRegion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (bh : Fin 2) (hpair : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hpureg : ∀ b : Fin 2, ∃ c : Bool, ∀ i ∈ side (n := n) C g b, s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1-bh), s i = c)
    (hmixh : ∀ c : Bool, ∃ i ∈ side (n := n) C h bh, s i = c) :
    TwoOrBuild.pairCost
      (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C h bh))
      (BoundarySources.sources n C (boundary n C s g h) (wires n C s g h) (opnd C h bh)) ≤
      (mixedRegion n C s g h).card := by
  have hhJ : h ∈ junk G C := by rw [hpair]; simp
  have hrh := mixed_operand_mem_wires G C s hAO g h hpair h hhJ bh hmixh
  have hr := StructuralCut.wires_one_root G C s hAO hT g h bh hpair hgh hhg hpureg hpureh
  have hbound := BoundarySources.pairCost_le_gates n C hAO
    (boundary n C s g h) (wires n C s g h) (boundary_disjoint C s g h)
    (opnd C h bh) (opnd C h bh) hrh hrh
    (boundary_parents C s hAO g h)
    (boundary_used G C s hAO hT g h hpair hgh hhg)
    (fun w hw => Or.inl (hr w hw))
    (sources_nonempty G C s hAO hT g h hpair hgh hhg _ hrh)
    (sources_nonempty G C s hAO hT g h hpair hgh hhg _ hrh)
  simpa only [wires_card] using hbound

end StructuralCut

namespace OriginTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma inCone_trans (n : ℕ) (C : Circuit) (a b c : ℕ)
    (hab : InCone n C a b) (hbc : InCone n C b c) : InCone n C a c := by
  revert hbc
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hbc
    obtain ⟨hc, k, hkc, hread, hbk⟩ := (MixedFrontier.inCone_iff n C b c).mp hbc
    apply (MixedFrontier.inCone_iff n C a c).mpr
    refine ⟨hc, k, hkc, hread, Or.inr ?_⟩
    rcases hbk with rfl | hbk
    · exact hab
    · exact ih k hkc hbk

end OriginTransport

namespace OriginTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open MixedFrontier

def LocalEdges (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ) : Prop :=
  ∀ i < D.gates.length, ∀ j < D.gates.length, ∀ a : ℕ,
    origin i = some a → n + i ∈ (gateAt D j).inputs →
      ∃ b : ℕ, origin j = some b ∧ InCone n C a b

lemma cone_transport (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : LocalEdges n C D origin) (i j : ℕ)
    (hi : i < D.gates.length) (hj : j < D.gates.length)
    (a : ℕ) (horigin : origin i = some a) (hcone : InCone n D i j) :
    ∃ b : ℕ, origin j = some b ∧ InCone n C a b := by
  have go : ∀ k, k < D.gates.length → InCone n D i k →
      ∃ b : ℕ, origin k = some b ∧ InCone n C a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hcone
      obtain ⟨_, r, hr, hread, hstep⟩ := (inCone_iff n D i k).mp hcone
      have hrD : r < D.gates.length := by omega
      rcases hstep with heq | hsub
      · subst r
        exact hedge i hi k hk a horigin hread
      · obtain ⟨b, hb, hab⟩ := ih r hr hrD hsub
        obtain ⟨c, hc, hbc⟩ := hedge r hrD k hk b hb hread
        exact ⟨c, hc, inCone_trans n C a b c hab hbc⟩
  exact go j hj hcone

lemma cone_transport_mapped (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : LocalEdges n C D origin) (i j : ℕ)
    (hi : i < D.gates.length) (hj : j < D.gates.length)
    (a b : ℕ) (hia : origin i = some a) (hjb : origin j = some b)
    (hcone : InCone n D i j) : InCone n C a b := by
  obtain ⟨c, hc, hac⟩ := cone_transport n C D origin hedge i j hi hj a hia hcone
  have hcb : c = b := Option.some.inj (hc.symm.trans hjb)
  exact hcb ▸ hac

lemma not_inCone_of_origins (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : LocalEdges n C D origin) (i j : ℕ)
    (hi : i < D.gates.length) (hj : j < D.gates.length)
    (a b : ℕ) (hia : origin i = some a) (hjb : origin j = some b)
    (hnot : ¬ InCone n C a b) : ¬ InCone n D i j := by
  intro hcone
  exact hnot (cone_transport_mapped n C D origin hedge i j hi hj a b hia hjb hcone)

lemma independent_of_origins (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : LocalEdges n C D origin) (i j : ℕ)
    (hi : i < D.gates.length) (hj : j < D.gates.length)
    (a b : ℕ) (hia : origin i = some a) (hjb : origin j = some b)
    (hab : ¬ InCone n C a b) (hba : ¬ InCone n C b a) :
    ¬ InCone n D i j ∧ ¬ InCone n D j i := by
  exact ⟨not_inCone_of_origins n C D origin hedge i j hi hj a b hia hjb hab,
    not_inCone_of_origins n C D origin hedge j i hj hi b a hjb hia hba⟩

lemma topForm_of_localEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (origin : ℕ → Option ℕ) (hT : TopForm G C)
    (hedge : LocalEdges n C D origin)
    (hAND : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
      ∃ a < C.gates.length, origin i = some a ∧ (gateAt C a).op = GateOp.and)
    (hclean : ∀ i < D.gates.length, ∀ a : ℕ, origin i = some a →
      (gateAt D i).op = GateOp.and → BelowF G D i → BelowF G C a) :
    TopForm G D := by
  intro i hi j hj hiAND hiClean hjAND hcone
  obtain ⟨a, ha, hia, haAND⟩ := hAND i hi hiAND
  obtain ⟨b, hb, hjb, hbAND⟩ := hAND j hj hjAND
  exact hT a ha b hb haAND (hclean i hi a hia hiAND hiClean) hbAND
    (cone_transport_mapped n C D origin hedge i j hi hj a b hia hjb hcone)

end OriginTransport

namespace OriginTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open MixedFrontier

def ReflLocalEdges (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ) : Prop :=
  ∀ i < D.gates.length, ∀ j < D.gates.length, ∀ a : ℕ,
    origin i = some a → n + i ∈ (gateAt D j).inputs →
      ∃ b : ℕ, origin j = some b ∧ (a = b ∨ InCone n C a b)

def AndOriginInjective (D : Circuit) (origin : ℕ → Option ℕ) : Prop :=
  ∀ i < D.gates.length, ∀ j < D.gates.length,
    (gateAt D i).op = GateOp.and → (gateAt D j).op = GateOp.and →
      ∀ a : ℕ, origin i = some a → origin j = some a → i = j

lemma reflCone_trans (n : ℕ) (C : Circuit) (a b c : ℕ)
    (hab : a = b ∨ InCone n C a b) (hbc : b = c ∨ InCone n C b c) :
    a = c ∨ InCone n C a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (inCone_trans n C a b c hab hbc)

lemma cone_transport_refl (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : ReflLocalEdges n C D origin) (i j : ℕ)
    (hi : i < D.gates.length) (hj : j < D.gates.length)
    (a : ℕ) (horigin : origin i = some a) (hcone : InCone n D i j) :
    ∃ b : ℕ, origin j = some b ∧ (a = b ∨ InCone n C a b) := by
  have go : ∀ k, k < D.gates.length → InCone n D i k →
      ∃ b : ℕ, origin k = some b ∧ (a = b ∨ InCone n C a b) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hcone
      obtain ⟨_, r, hr, hread, hstep⟩ := (inCone_iff n D i k).mp hcone
      have hrD : r < D.gates.length := by omega
      rcases hstep with heq | hsub
      · subst r
        exact hedge i hi k hk a horigin hread
      · obtain ⟨b, hb, hab⟩ := ih r hr hrD hsub
        obtain ⟨c, hc, hbc⟩ := hedge r hrD k hk b hb hread
        exact ⟨c, hc, reflCone_trans n C a b c hab hbc⟩
  exact go j hj hcone

lemma cone_transport_refl_mapped (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : ReflLocalEdges n C D origin) (i j : ℕ)
    (hi : i < D.gates.length) (hj : j < D.gates.length)
    (a b : ℕ) (hia : origin i = some a) (hjb : origin j = some b)
    (hcone : InCone n D i j) : a = b ∨ InCone n C a b := by
  obtain ⟨c, hc, hac⟩ := cone_transport_refl n C D origin hedge i j hi hj a hia hcone
  have hcb : c = b := Option.some.inj (hc.symm.trans hjb)
  exact hcb ▸ hac

lemma and_cone_transport (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : ReflLocalEdges n C D origin) (hinj : AndOriginInjective D origin)
    (i j : ℕ) (hi : i < D.gates.length) (hj : j < D.gates.length)
    (hiAND : (gateAt D i).op = GateOp.and) (hjAND : (gateAt D j).op = GateOp.and)
    (a b : ℕ) (hia : origin i = some a) (hjb : origin j = some b)
    (hcone : InCone n D i j) : InCone n C a b := by
  rcases cone_transport_refl_mapped n C D origin hedge i j hi hj a b hia hjb hcone with heq | hstrict
  · subst b
    have hij := hinj i hi j hj hiAND hjAND a hia hjb
    have hlt := inCone_lt n D j i hcone
    omega
  · exact hstrict

lemma and_not_inCone_of_refl_origins (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : ReflLocalEdges n C D origin) (hinj : AndOriginInjective D origin)
    (i j : ℕ) (hi : i < D.gates.length) (hj : j < D.gates.length)
    (hiAND : (gateAt D i).op = GateOp.and) (hjAND : (gateAt D j).op = GateOp.and)
    (a b : ℕ) (hia : origin i = some a) (hjb : origin j = some b)
    (hnot : ¬ InCone n C a b) : ¬ InCone n D i j := by
  intro hcone
  exact hnot (and_cone_transport n C D origin hedge hinj i j hi hj hiAND hjAND a b hia hjb hcone)

lemma independent_and_of_refl_origins (n : ℕ) (C D : Circuit) (origin : ℕ → Option ℕ)
    (hedge : ReflLocalEdges n C D origin) (hinj : AndOriginInjective D origin)
    (i j : ℕ) (hi : i < D.gates.length) (hj : j < D.gates.length)
    (hiAND : (gateAt D i).op = GateOp.and) (hjAND : (gateAt D j).op = GateOp.and)
    (a b : ℕ) (hia : origin i = some a) (hjb : origin j = some b)
    (hab : ¬ InCone n C a b) (hba : ¬ InCone n C b a) :
    ¬ InCone n D i j ∧ ¬ InCone n D j i := by
  exact ⟨and_not_inCone_of_refl_origins n C D origin hedge hinj i j hi hj hiAND hjAND a b hia hjb hab,
    and_not_inCone_of_refl_origins n C D origin hedge hinj j i hj hi hjAND hiAND b a hjb hia hba⟩

lemma topForm_of_reflLocalEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (origin : ℕ → Option ℕ) (hT : TopForm G C)
    (hedge : ReflLocalEdges n C D origin) (hinj : AndOriginInjective D origin)
    (hAND : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
      ∃ a < C.gates.length, origin i = some a ∧ (gateAt C a).op = GateOp.and)
    (hclean : ∀ i < D.gates.length, ∀ a : ℕ, origin i = some a →
      (gateAt D i).op = GateOp.and → BelowF G D i → BelowF G C a) :
    TopForm G D := by
  intro i hi j hj hiAND hiClean hjAND hcone
  obtain ⟨a, ha, hia, haAND⟩ := hAND i hi hiAND
  obtain ⟨b, hb, hjb, hbAND⟩ := hAND j hj hjAND
  exact hT a ha b hb haAND (hclean i hi a hia hiAND hiClean) hbAND
    (and_cone_transport n C D origin hedge hinj i j hi hj hiAND hjAND a b hia hjb hcone)

end OriginTransport

namespace OriginTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma belowF_of_junk_forward {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (i a : ℕ) (ha : a < C.gates.length)
    (haAND : (gateAt C a).op = GateOp.and)
    (hforward : a ∈ junk G C → i ∈ junk G D) (hclean : BelowF G D i) :
    BelowF G C a := by
  classical
  by_contra hnot
  have hex : ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
    by_contra hnone
    apply hnot
    intro x hx
    by_contra hf
    exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  obtain ⟨x, hx, hf⟩ := hex
  have haj : a ∈ junk G C :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, haAND, ha, x, hx, hf⟩
  obtain ⟨_, _, y, hy, hfy⟩ := (Finset.mem_filter.mp (hforward haj)).2
  have he := hclean y hy
  rw [hfy] at he
  cases he

lemma cleanBackward_of_junk_origins {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (origin : ℕ → Option ℕ)
    (hAND : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
      ∃ a < C.gates.length, origin i = some a ∧ (gateAt C a).op = GateOp.and)
    (hjunk : ∀ i < D.gates.length, ∀ a : ℕ, origin i = some a →
      (gateAt D i).op = GateOp.and → a ∈ junk G C → i ∈ junk G D) :
    ∀ i < D.gates.length, ∀ a : ℕ, origin i = some a →
      (gateAt D i).op = GateOp.and → BelowF G D i → BelowF G C a := by
  intro i hi a hia hiAND hiClean
  obtain ⟨b, hb, hib, hbAND⟩ := hAND i hi hiAND
  have hab : a = b := Option.some.inj (hia.symm.trans hib)
  subst b
  exact belowF_of_junk_forward G C D i a hb hbAND (hjunk i hi a hia hiAND) hiClean

end OriginTransport

namespace TagTraceTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open MixedFrontier

def LocalTraceMonotone (n : ℕ) (D : Circuit) (trace : ℕ → Finset ℕ) : Prop :=
  ∀ j < D.gates.length, ∀ w ∈ (gateAt D j).inputs, trace w ⊆ trace (n + j)

def AndTagInjective (D : Circuit) (tag : ℕ → ℕ) : Prop :=
  ∀ i < D.gates.length, ∀ j < D.gates.length,
    (gateAt D i).op = GateOp.and → (gateAt D j).op = GateOp.and →
      tag i = tag j → i = j

lemma tag_injective_of_self_map (n : ℕ) (D : Circuit) (tag : ℕ → ℕ) (m : ℕ → Option ℕ)
    (hself : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
      m (n + tag i) = some (n + i)) : AndTagInjective D tag := by
  intro i hi j hj hiAND hjAND htag
  have hmi := hself i hi hiAND
  have hmj := hself j hj hjAND
  rw [htag] at hmi
  exact Nat.add_left_cancel (Option.some.inj (hmi.symm.trans hmj))

lemma cone_trace_subset (n : ℕ) (D : Circuit) (trace : ℕ → Finset ℕ)
    (hlocal : LocalTraceMonotone n D trace) (i j : ℕ) (hcone : InCone n D i j) :
    trace (n + i) ⊆ trace (n + j) := by
  have go : ∀ k, InCone n D i k → trace (n + i) ⊆ trace (n + k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hcone
      obtain ⟨hk, r, hr, hread, hstep⟩ := (inCone_iff n D i k).mp hcone
      rcases hstep with heq | hsub
      · subst r
        exact hlocal k hk (n + i) hread
      · exact (ih r hr hsub).trans (hlocal k hk (n + r) hread)
  exact go j hcone

lemma ancestor_tag_mem (n : ℕ) (D : Circuit) (trace : ℕ → Finset ℕ) (tag : ℕ → ℕ)
    (hlocal : LocalTraceMonotone n D trace)
    (hseed : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → tag i ∈ trace (n + i))
    (i j : ℕ) (hi : i < D.gates.length) (hiAND : (gateAt D i).op = GateOp.and)
    (hcone : InCone n D i j) : tag i ∈ trace (n + j) := by
  exact cone_trace_subset n D trace hlocal i j hcone (hseed i hi hiAND)

lemma and_cone_transport (n : ℕ) (C D : Circuit) (trace : ℕ → Finset ℕ) (tag : ℕ → ℕ)
    (hlocal : LocalTraceMonotone n D trace)
    (hseed : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → tag i ∈ trace (n + i))
    (hcover : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∀ a ∈ trace (n + j), a = tag j ∨ InCone n C a (tag j))
    (hinj : AndTagInjective D tag)
    (i j : ℕ) (hi : i < D.gates.length) (hj : j < D.gates.length)
    (hiAND : (gateAt D i).op = GateOp.and) (hjAND : (gateAt D j).op = GateOp.and)
    (hcone : InCone n D i j) : InCone n C (tag i) (tag j) := by
  have hmem := ancestor_tag_mem n D trace tag hlocal hseed i j hi hiAND hcone
  rcases hcover j hj hjAND (tag i) hmem with heq | hstrict
  · have hij := hinj i hi j hj hiAND hjAND heq
    have hlt := inCone_lt n D j i hcone
    omega
  · exact hstrict

lemma independent_and_of_traces (n : ℕ) (C D : Circuit) (trace : ℕ → Finset ℕ) (tag : ℕ → ℕ)
    (hlocal : LocalTraceMonotone n D trace)
    (hseed : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → tag i ∈ trace (n + i))
    (hcover : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∀ a ∈ trace (n + j), a = tag j ∨ InCone n C a (tag j))
    (hinj : AndTagInjective D tag)
    (i j : ℕ) (hi : i < D.gates.length) (hj : j < D.gates.length)
    (hiAND : (gateAt D i).op = GateOp.and) (hjAND : (gateAt D j).op = GateOp.and)
    (hab : ¬ InCone n C (tag i) (tag j)) (hba : ¬ InCone n C (tag j) (tag i)) :
    ¬ InCone n D i j ∧ ¬ InCone n D j i := by
  exact ⟨fun hcone => hab (and_cone_transport n C D trace tag hlocal hseed hcover hinj
      i j hi hj hiAND hjAND hcone),
    fun hcone => hba (and_cone_transport n C D trace tag hlocal hseed hcover hinj
      j i hj hi hjAND hiAND hcone)⟩

lemma topForm_of_localTrace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (trace : ℕ → Finset ℕ) (tag : ℕ → ℕ) (hT : TopForm G C)
    (hlocal : LocalTraceMonotone n D trace)
    (hseed : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → tag i ∈ trace (n + i))
    (hcover : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∀ a ∈ trace (n + j), a = tag j ∨ InCone n C a (tag j))
    (hinj : AndTagInjective D tag)
    (hAND : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
      tag i < C.gates.length ∧ (gateAt C (tag i)).op = GateOp.and)
    (hclean : ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
      BelowF G D i → BelowF G C (tag i)) : TopForm G D := by
  intro i hi j hj hiAND hiClean hjAND hcone
  obtain ⟨ha, haAND⟩ := hAND i hi hiAND
  obtain ⟨hb, hbAND⟩ := hAND j hj hjAND
  exact hT (tag i) ha (tag j) hb haAND (hclean i hi hiAND hiClean) hbAND
    (and_cone_transport n C D trace tag hlocal hseed hcover hinj i j hi hj hiAND hjAND hcone)

end TagTraceTransport

end PEqualNP.Outside.L_meta_5012
