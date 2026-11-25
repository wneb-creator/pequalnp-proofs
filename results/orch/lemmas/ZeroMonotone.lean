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

lemma gate_true_mono (g : Gate) (ho : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ → Bool) (hab : ∀ i, a i = true → b i = true)
    (ha : g.op.eval (g.inputs.map a) = true) : g.op.eval (g.inputs.map b) = true := by
  rcases ho with ho | ho
  · rw [ho] at ha ⊢
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hab i (List.all_eq_true.mp ha _ (List.mem_map_of_mem hi))
  · rw [ho] at ha ⊢
    obtain ⟨v, hv, hvt⟩ := List.any_eq_true.mp ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact List.any_eq_true.mpr ⟨b i, List.mem_map_of_mem hi, hab i hvt⟩

lemma run_true_mono (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hl : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (run gs a).getD i false = true → (run gs b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    let av := g.op.eval (g.inputs.map fun i => a.getD i false)
    let bv := g.op.eval (g.inputs.map fun i => b.getD i false)
    have hv : av = true → bv = true := gate_true_mono g (ops g List.mem_cons_self) _ _ hab
    have next : ∀ i, (a ++ [av]).getD i false = true →
        (b ++ [bv]).getD i false = true := by
      intro i
      rw [append_get, append_get, hl]
      by_cases hi : i = b.length
      · simpa only [hi, ite_true] using hv
      · simpa only [hi, ite_false] using hab i
    exact ih (fun g hg => ops g (List.mem_cons_of_mem _ hg))
      (a ++ [av]) (b ++ [bv]) (by simp [hl]) next

lemma zero_forcing (pre post : List Gate) (g : Gate) (out : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ g :: post) out)) (x : List Bool) :
    ∀ i, (run (pre ++ ⟨GateOp.or, []⟩ :: post) x).getD i false = true →
      (run (pre ++ g :: post) x).getD i false = true := by
  rw [run_append, run_append]
  let w := run pre x
  change ∀ i, (run post (w ++ [false])).getD i false = true →
    (run post (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = true
  apply run_true_mono post
  · intro a ha
    have hop := (h a (List.mem_append_right _ (List.mem_cons_of_mem g ha))).1
    simpa using hop
  · simp
  · intro i
    rw [append_get, append_get]
    by_cases hi : i = w.length
    · simp only [hi, ite_true, Bool.false_eq_true, false_implies]
    · simp only [hi, ite_false]
      exact id

end PEqualNP.Outside.L_meta_2732_aux.EraseWire
