import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire (cut replacement i : ℕ) : ℕ :=
  if i < cut then i else if i = cut then replacement else i - 1

def gate (cut replacement : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire cut replacement)⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def erased (n : ℕ) (pre post : List Gate) (out replacement : ℕ) : Circuit :=
  ⟨pre ++ post.map (gate (n + pre.length) replacement), wire (n + pre.length) replacement out⟩

lemma run_append (pre post : List Gate) (w : List Bool) :
    run (pre ++ post) w = run post (run pre w) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma append_get (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (by omega)]
  · subst i
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), ite_eq_right (by omega),
      List.getD_eq_default _ _ (by omega)]

lemma initial (w : List Bool) (replacement i : ℕ) :
    w.getD (wire w.length replacement i) false =
      (w ++ [w.getD replacement false]).getD i false := by
  by_cases hi : i < w.length
  · rw [wire, ite_eq_left hi, List.getD_append _ _ _ _ hi]
  · by_cases he : i = w.length
    · subst i
      simp [wire]
    · have hi' : w.length + 1 ≤ i := by omega
      simp only [wire, ite_eq_right hi, ite_eq_right he]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

lemma wire_at (cut replacement i m : ℕ) (hc : cut ≤ m) (hr : replacement ≠ m) :
    wire cut replacement i = m ↔ i = m + 1 := by
  by_cases hi : i < cut
  · simp only [wire, ite_eq_left hi]
    omega
  · by_cases he : i = cut
    · simp only [wire, ite_eq_right hi, ite_eq_left he]
      omega
    · simp only [wire, ite_eq_right hi, ite_eq_right he]
      omega

lemma fold (cut replacement : ℕ) (gs : List Gate) :
    ∀ old new : List Bool, cut < old.length → old.length = new.length + 1 →
      (replacement < cut ∨ new.length + gs.length ≤ replacement) →
      (∀ i, new.getD (wire cut replacement i) false = old.getD i false) →
      ∀ i, (run (gs.map (gate cut replacement)) new).getD (wire cut replacement i) false =
        (run gs old).getD i false := by
  induction gs with
  | nil => intro old new hc hl hr hv; exact hv
  | cons g gs ih =>
    intro old new hc hl hr hv
    let b := g.op.eval (g.inputs.map fun i => old.getD i false)
    have hb : (gate cut replacement g).op.eval
        ((gate cut replacement g).inputs.map fun i => new.getD i false) = b := by
      simp only [gate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hv i
    have hr' : replacement ≠ new.length := by
      rcases hr with hr | hr
      · omega
      · simp only [List.length_cons] at hr
        omega
    have hc' : cut ≤ new.length := by omega
    have step : ∀ i, (new ++ [b]).getD (wire cut replacement i) false =
        (old ++ [b]).getD i false := by
      intro i
      rw [append_get, append_get, hl]
      simp only [wire_at cut replacement i new.length hc' hr', hv i]
    have hr'' : replacement < cut ∨ (new ++ [b]).length + gs.length ≤ replacement := by
      rcases hr with hr | hr
      · exact Or.inl hr
      · right
        simp only [List.length_append, List.length_cons, List.length_nil] at *
        omega
    have h := ih (old ++ [b]) (new ++ [b]) (by simp; omega) (by simp [hl]) hr'' step
    simpa only [run, List.map_cons, List.foldl_cons, hb] using h

lemma eval (n : ℕ) (pre post : List Gate) (g : Gate) (out replacement : ℕ)
    (safe : replacement < n + pre.length ∨ n + pre.length + post.length ≤ replacement)
    (x : List Bool) (hx : x.length = n)
    (aliases : g.op.eval (g.inputs.map fun i => (run pre x).getD i false) =
      (run pre x).getD replacement false) :
    (erased n pre post out replacement).eval x = (Circuit.mk (pre ++ g :: post) out).eval x := by
  let w := run pre x
  have hw : w.length = n + pre.length := by simp [w, run_length, hx]
  change (run (pre ++ post.map (gate (n + pre.length) replacement)) x).getD
      (wire (n + pre.length) replacement out) false = (run (pre ++ g :: post) x).getD out false
  rw [run_append, run_append]
  change (run (post.map (gate (n + pre.length) replacement)) w).getD
      (wire (n + pre.length) replacement out) false =
    (run post (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD out false
  rw [aliases]
  apply fold (n + pre.length) replacement post (w ++ [w.getD replacement false]) w
  · simp [hw]
  · simp
  · simpa only [hw] using safe
  · intro i
    simpa only [hw] using initial w replacement i

lemma size (n : ℕ) (pre post : List Gate) (g : Gate) (out replacement : ℕ) :
    (erased n pre post out replacement).size + 1 = (Circuit.mk (pre ++ g :: post) out).size := by
  simp [erased, Circuit.size]
  omega

lemma monotone (n : ℕ) (pre post : List Gate) (g : Gate) (out replacement : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ g :: post) out)) :
    Monotone2 (erased n pre post out replacement) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h a (List.mem_append_left _ ha)
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have h' := h b (List.mem_append_right _ (List.mem_cons_of_mem g hb))
    exact ⟨h'.1, by simpa [gate] using h'.2⟩

lemma delete_zero (n : ℕ) (pre post : List Gate) (out : ℕ) (x : List Bool) (hx : x.length = n) :
    (erased n pre post out (n + pre.length + post.length)).eval x =
      (Circuit.mk (pre ++ ⟨GateOp.or, []⟩ :: post) out).eval x := by
  apply eval n pre post ⟨GateOp.or, []⟩ out (n + pre.length + post.length) (Or.inr le_rfl) x hx
  simp only [GateOp.eval, List.map_nil, List.any_nil]
  symm
  apply List.getD_eq_default
  rw [run_length, hx]
  omega

end PEqualNP.Outside.L_meta_2732_aux.EraseWire

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def normalizedRef (cut limit i : ℕ) : ℕ := if i < cut then i else limit

lemma normalized_safe (cut limit i : ℕ) :
    normalizedRef cut limit i < cut ∨ limit ≤ normalizedRef cut limit i := by
  by_cases hi : i < cut <;> simp [normalizedRef, hi]

lemma normalized_get (cut limit i : ℕ) (hl : cut ≤ limit) (w : List Bool)
    (hw : w.length = cut) : w.getD (normalizedRef cut limit i) false = w.getD i false := by
  by_cases hi : i < cut
  · simp [normalizedRef, hi]
  · rw [normalizedRef, ite_eq_right hi,
      List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma alias_invalid (cut limit z : ℕ) (g : Gate) (hl : cut ≤ limit)
    (ho : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hz : z ∈ g.inputs) (hcut : cut ≤ z) :
    ∃ replacement, (replacement < cut ∨ limit ≤ replacement) ∧
      ∀ w : List Bool, w.length = cut →
        g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD replacement false := by
  rcases g with ⟨op, ins⟩
  rcases ho with rfl | rfl
  · refine ⟨limit, Or.inr le_rfl, ?_⟩
    intro w hw
    rw [List.getD_eq_default _ _ (by omega)]
    change (ins.map fun i => w.getD i false).all id = false
    apply List.all_eq_false.mpr
    refine ⟨w.getD z false, List.mem_map_of_mem hz, ?_⟩
    have hzero : w.getD z false = false := List.getD_eq_default _ _ (by omega)
    rw [hzero]
    decide
  · cases ins with
    | nil => simp at hz
    | cons a ins =>
      cases ins with
      | nil =>
        refine ⟨normalizedRef cut limit a, normalized_safe cut limit a, ?_⟩
        intro w hw
        rw [normalized_get cut limit a hl w hw]
        simp [GateOp.eval]
      | cons b ins =>
        have ht : ins = [] := by
          have ht : ins.length = 0 := by
            simp only [List.length_cons] at hlen
            omega
          simpa using ht
        subst ins
        have hz' : z = a ∨ z = b := by simpa using hz
        rcases hz' with hz' | hz'
        · refine ⟨normalizedRef cut limit b, normalized_safe cut limit b, ?_⟩
          intro w hw
          rw [normalized_get cut limit b hl w hw]
          have ha : w.getD a false = false := List.getD_eq_default _ _ (by omega)
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
          change (w.getD a false || (w.getD b false || false)) = w.getD b false
          rw [ha]
          simp
        · refine ⟨normalizedRef cut limit a, normalized_safe cut limit a, ?_⟩
          intro w hw
          rw [normalized_get cut limit a hl w hw]
          have hb : w.getD b false = false := List.getD_eq_default _ _ (by omega)
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
          change (w.getD a false || (w.getD b false || false)) = w.getD a false
          rw [hb]
          simp

lemma delete_invalid_input (n : ℕ) (pre post : List Gate) (g : Gate) (out z : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ g :: post) out))
    (hz : z ∈ g.inputs) (hcut : n + pre.length ≤ z) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = (Circuit.mk (pre ++ g :: post) out).size ∧
      ∀ x : List Bool, x.length = n → D.eval x = (Circuit.mk (pre ++ g :: post) out).eval x := by
  have hg := h g (List.mem_append_right _ List.mem_cons_self)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
  obtain ⟨replacement, safe, halias⟩ := alias_invalid (n + pre.length)
    (n + pre.length + post.length) z g (by omega) hop hg.2 hz hcut
  refine ⟨erased n pre post out replacement, monotone n pre post g out replacement h,
    size n pre post g out replacement, ?_⟩
  intro x hx
  apply eval n pre post g out replacement safe x hx
  exact halias (run pre x) (by simp [run_length, hx])

lemma delete_zero_consumer (n : ℕ) (pre between after : List Gate) (dead consumer : Gate) (out : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ dead :: (between ++ consumer :: after)) out))
    (uses : n + pre.length ∈ consumer.inputs) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 2 = (Circuit.mk (pre ++ dead :: (between ++ consumer :: after)) out).size ∧
      ∀ x : List Bool, x.length = n →
        D.eval x = (Circuit.mk (pre ++ ⟨GateOp.or, []⟩ :: (between ++ consumer :: after)) out).eval x := by
  let post := between ++ consumer :: after
  let cut := n + pre.length
  let limit := n + pre.length + post.length
  let E := erased n pre post out limit
  let pre' := pre ++ between.map (gate cut limit)
  let consumer' := gate cut limit consumer
  let after' := after.map (gate cut limit)
  have he : E = Circuit.mk (pre' ++ consumer' :: after') (wire cut limit out) := by
    simp [E, erased, pre', consumer', after', post, cut, List.map_append, List.append_assoc]
  have hE : Monotone2 E := monotone n pre post dead out limit h
  have hE' : Monotone2 (Circuit.mk (pre' ++ consumer' :: after') (wire cut limit out)) := by
    rw [← he]
    exact hE
  have huses : limit ∈ consumer'.inputs := by
    change limit ∈ consumer.inputs.map (wire cut limit)
    have hw : wire cut limit cut = limit := by simp [wire]
    have hm := List.mem_map_of_mem (f := wire cut limit) uses
    change wire cut limit cut ∈ consumer.inputs.map (wire cut limit) at hm
    simpa only [hw] using hm
  have hinvalid : n + pre'.length ≤ limit := by
    simp [pre', limit, post]
    omega
  obtain ⟨D, hD, hs, hv⟩ := delete_invalid_input n pre' after' consumer'
    (wire cut limit out) limit hE' huses hinvalid
  have hsE : E.size + 1 = (Circuit.mk (pre ++ dead :: post) out).size :=
    size n pre post dead out limit
  rw [← he] at hs
  refine ⟨D, hD, ?_, ?_⟩
  · change D.size + 2 = (Circuit.mk (pre ++ dead :: post) out).size
    omega
  intro x hx
  have hv' : D.eval x = E.eval x := by simpa only [← he] using hv x hx
  exact hv'.trans (delete_zero n pre post out x hx)

end PEqualNP.Outside.L_meta_2732_aux.EraseWire
