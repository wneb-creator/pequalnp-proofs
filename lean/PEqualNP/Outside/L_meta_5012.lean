import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

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


lemma ao_ok {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) : Ok n C.gates := by
  intro j hj
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 (h.2.2 _ hm)
  refine ⟨(gateAt C j).op, s, t, ?_, h.1 _ hm, ?_, ?_⟩
  · rw [← e]
    cases hg : gateAt C j
    simpa [hg] using hst
  · exact h.2.1 j hj s (by rw [hst]; simp)
  · exact h.2.1 j hj t (by rw [hst]; simp)

lemma restrict_build (n : ℕ) (z : Fin n) (gs : List Gate) (hok : Ok n gs) :
    ∃ (hs : List Gate) (m : ℕ → Option ℕ), Ok n hs ∧ hs.length ≤ gs.length ∧
      (hs.length = gs.length → ∀ g ∈ gs, z.val ∉ g.inputs) ∧ m z.val = none ∧
      ∀ w < n + gs.length,
        (∀ w', m w = some w' → w' < n + hs.length) ∧
        ∀ x : Fin n → Bool, ov hs (List.ofFn x) (m w) =
          (run gs (List.ofFn (Function.update x z false))).getD w false := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], (fun w => if w = z.val then none else some w), ?_, by simp, by simp,
      by simp, ?_⟩
    · intro j hj; simp at hj
    · intro w hw
      have hw' : w < n := by simpa using hw
      by_cases hz : w = z.val
      · subst w
        simp [ov, run]
      · refine ⟨?_, ?_⟩
        · intro w' he
          simp only [if_neg hz, Option.some.injEq] at he
          subst w'; simpa using hw'
        · intro x
          simp [ov, run, hz, List.getD_eq_getElem?_getD, hw',
            show (⟨w, hw'⟩ : Fin n) ≠ z from fun h => hz (congrArg Fin.val h)]
  | append_singleton gs g ih =>
    have hpre : Ok n gs := by
      intro j hj
      have h := hok j (by simp; omega)
      simpa only [List.getElem_append_left hj] using h
    obtain ⟨o, s, t, hg, ho, hs, ht⟩ := hok gs.length (by simp)
    have hgg : g = ⟨o, [s, t]⟩ := by simpa using hg
    subst g
    obtain ⟨ks, m, hk, hlen, heq, hz, hm⟩ := ih hpre
    obtain ⟨hms, hvs⟩ := hm s hs
    obtain ⟨hmt, hvt⟩ := hm t ht
    suffices hstep : ∃ (ls : List Gate) (v : Option ℕ), Ok n (ks ++ ls) ∧
        ls.length ≤ 1 ∧ (ls.length = 1 → s ≠ z.val ∧ t ≠ z.val) ∧
        (∀ w, v = some w → w < n + (ks ++ ls).length) ∧
        ∀ x : Fin n → Bool, ov (ks ++ ls) (List.ofFn x) v =
          o.eval [(run gs (List.ofFn (Function.update x z false))).getD s false,
            (run gs (List.ofFn (Function.update x z false))).getD t false] by
      obtain ⟨ls, v, hkl, hll, hnz, hv, hval⟩ := hstep
      refine ⟨ks ++ ls, Function.update m (n + gs.length) v, hkl, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · intro he g hmem
        have hklen : ks.length = gs.length := by
          simp only [List.length_append, List.length_singleton] at he
          omega
        have hls : ls.length = 1 := by
          simp only [List.length_append, List.length_singleton] at he
          omega
        rcases List.mem_append.1 hmem with hmem | hmem
        · exact heq hklen g hmem
        · simp only [List.mem_singleton] at hmem
          subst g
          simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or, ne_eq, eq_comm] using hnz hls
      · rw [Function.update_of_ne (by omega), hz]
      · intro w hw
        by_cases hwnew : w = n + gs.length
        · subst w
          rw [Function.update_self]
          refine ⟨hv, fun x => ?_⟩
          rw [hval x, run_snoc]
          have hl : (run gs (List.ofFn (Function.update x z false))).length = n + gs.length :=
            by rw [run_length, List.length_ofFn]
          rw [← hl, getD_at]
          rfl
        · rw [Function.update_of_ne hwnew]
          obtain ⟨hb, he⟩ := hm w (by simp only [List.length_append, List.length_singleton] at hw; omega)
          refine ⟨fun w' hw' => by have := hb w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext ks ls _ _ (by simpa using hb), he x, run_snoc,
            getD_lt _ _ _ (by
              rw [run_length, List.length_ofFn]
              simp only [List.length_append, List.length_singleton] at hw
              omega)]
    cases hso : m s with
    | none =>
      cases ho with
      | inl hoa =>
        subst o
        refine ⟨[], none, by simpa using hk, by simp, by simp, by simp, fun x => ?_⟩
        rw [← hvs x, ← hvt x, hso]
        simp [ov, GateOp.eval]
      | inr hoa =>
        subst o
        refine ⟨[], m t, by simpa using hk, by simp, by simp, by simpa using hmt, fun x => ?_⟩
        rw [← hvs x, ← hvt x, hso]
        simp [ov, GateOp.eval]
    | some a =>
      cases hto : m t with
      | none =>
        cases ho with
        | inl hoa =>
          subst o
          refine ⟨[], none, by simpa using hk, by simp, by simp, by simp, fun x => ?_⟩
          rw [← hvs x, ← hvt x, hto]
          simp [ov, GateOp.eval]
        | inr hoa =>
          subst o
          refine ⟨[], m s, by simpa using hk, by simp, by simp, by simpa using hms, fun x => ?_⟩
          rw [← hvs x, ← hvt x, hto]
          simp [ov, GateOp.eval]
      | some b =>
        have ha := hms a hso
        have hb := hmt b hto
        refine ⟨[⟨o, [a, b]⟩], some (n + ks.length), ok_snoc hk ho ha hb,
          by simp, ?_, ?_, fun x => ?_⟩
        · intro _
          constructor
          · intro he; rw [he, hz] at hso; contradiction
          · intro he; rw [he, hz] at hto; contradiction
        · intro w hw; cases hw; simp
        · rw [ov_new ks n _ (by simp) _ _ _ ha hb, ← hvs x, ← hvt x, hso, hto]
          rfl

lemma restrict_circuit (n : ℕ) (C : Circuit) (z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
      (D.size = C.size → ∀ g ∈ C.gates, z.val ∉ g.inputs) ∧
      ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (Function.update x z false) := by
  classical
  obtain ⟨gs, m, hok, hlen, heq, _, hm⟩ := restrict_build n z C.gates (ao_ok hAO)
  let v := if C.output < n + C.gates.length then m C.output else none
  let w := v.getD (n + gs.length)
  refine ⟨⟨gs, w⟩, ok_ao hok, hlen, heq, fun x => ?_⟩
  change (run gs (List.ofFn x)).getD w false =
    (run C.gates (List.ofFn (Function.update x z false))).getD C.output false
  have hw : (run gs (List.ofFn x)).getD w false = ov gs (List.ofFn x) v := by
    cases hv : v with
    | none => simp [w, hv, ov, List.getD_eq_default, run_length]
    | some a => simp [w, hv, ov]
  rw [hw]
  by_cases ho : C.output < n + C.gates.length
  · simpa [v, ho] using (hm C.output ho).2 x
  · simp [v, ho, ov, List.getD_eq_default, run_length,
      show n + C.gates.length ≤ C.output by omega]

lemma graphFun_isolated_update {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (hz : ∀ v, ¬ G.Adj z v) (x : Fin n → Bool) :
    graphFun G ∅ (Function.update x z false) = graphFun G ∅ x := by
  have he : ∀ u v, G.Adj u v → u ≠ z ∧ v ≠ z := by
    intro u v huv
    constructor
    · intro he; subst u; exact hz v huv
    · intro he; subst v; exact hz u (huv.symm)
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  congr 1
  apply propext
  constructor <;> rintro ⟨u, v, huv, hu, hv⟩
  · exact ⟨u, v, huv, by simpa [Function.update_of_ne (he u v huv).1] using hu,
      by simpa [Function.update_of_ne (he u v huv).2] using hv⟩
  · exact ⟨u, v, huv, by simpa [Function.update_of_ne (he u v huv).1] using hu,
      by simpa [Function.update_of_ne (he u v huv).2] using hv⟩

lemma least_no_isolated_reads {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : PEqualNP.TopForm.IsLeastAO G C) (z : Fin n)
    (hz : ∀ v, ¬ G.Adj z v) : ∀ g ∈ C.gates, z.val ∉ g.inputs := by
  obtain ⟨D, hAO, hle, heq, hval⟩ := restrict_circuit n C z hL.1
  apply heq
  apply Nat.le_antisymm hle
  apply hL.2.2 D hAO
  funext x
  rw [hval x, hL.2.1, graphFun_isolated_update G z hz x]

end PEqualNP.Outside.L_meta_5012
