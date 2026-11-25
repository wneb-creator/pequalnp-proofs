import PEqualNP.Defs
-- Compositional builder adapted from EdgeUpper and EdgeUpperMono (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3754.Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def Ready (m : Nat) (gs : List Gate) : Prop :=
  ∀ i (hi : i<gs.length),
    ((gs[i]).op=GateOp.and ∨ (gs[i]).op=GateOp.or) ∧
    (gs[i]).inputs.length=2 ∧ ∀ v∈(gs[i]).inputs,v<m+i

lemma ready_append {m : Nat} {xs ys : List Gate}
    (hx : Ready m xs) (hy : Ready (m+xs.length) ys) : Ready m (xs++ys) := by
  intro i hi
  by_cases hix : i<xs.length
  · simpa only [List.getElem_append_left hix] using hx i hix
  · have hiy : i-xs.length<ys.length := by simp only [List.length_append] at hi;omega
    have h := hy (i-xs.length) hiy
    have hil : xs.length ≤ i := by omega
    simp only [List.getElem_append_right hil]
    refine ⟨h.1,h.2.1,?_⟩
    intro v hv
    have hh:=h.2.2 v hv
    omega

lemma ready_single (op : GateOp) (hop : op=GateOp.and ∨ op=GateOp.or)
    {m a b : Nat} (ha : a<m) (hb : b<m) : Ready m [⟨op,[a,b]⟩] := by
  intro i hi
  have he : i=0 := by simpa using hi
  subst i
  refine ⟨hop,rfl,?_⟩
  intro v hv
  simp only [List.getElem_cons_zero,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl
  · simpa using ha
  · simpa using hb

lemma ready_isAO2 {m : Nat} {gs : List Gate} (h : Ready m gs) {out : Nat} :
    PEqualNP.TopForm.IsAO2 m ⟨gs,out⟩ := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    exact (h i hi).1
  · intro i hi v hv
    have he : gateAt ⟨gs,out⟩ i=gs[i] := by
      simp [gateAt,List.getD_eq_getElem?_getD,hi]
    rw [he] at hv
    exact (h i hi).2.2 v hv
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    exact (h i hi).2.1

def step (w : List Bool) (g : Gate) : List Bool :=
  w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
lemma wiresFrom_append (xs ys : List Gate) (w : List Bool) :
    wiresFrom (xs++ys) w=wiresFrom ys (wiresFrom xs w) := by simp [wiresFrom,List.foldl_append]
lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (step w g)).length=_
    rw [ih]
    simp [step]
    omega
lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : Nat) (hi : i<w.length) :
    (wiresFrom gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (step w g)).getD i false=_
    rw [ih (step w g) (by simp [step];omega)]
    simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma getD_snoc_eq (w : List Bool) (v d : Bool) : (w++[v]).getD w.length d=v := by simp

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), Ready m gs ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by intro j hj; simp at hj, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · apply ready_append (ready_append ok1 ok2)
    apply ready_single op hop
    · simp only [List.length_append]
      omega
    · simp only [List.length_append]
      omega
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_circuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ}
    (h : Bld n F s) : ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D=F ∧ D.size≤s := by
  obtain ⟨gs,out,ok,len,_,ev⟩ := h n le_rfl
  refine ⟨⟨gs,out⟩,ready_isAO2 ok,?_,len⟩
  funext x
  have h := ev (List.ofFn x) (by simp)
  change (wiresFrom gs (List.ofFn x)).getD out false = F x
  rw [h]
  congr 1
  funext i
  simp

/-- The OR of the inputs in a nonempty list. -/
theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

/-- The OR of the inputs in a nonempty finset `S`, with `|S| - 1` gates. -/
theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp


lemma double_star_upper {n : Nat} (U V : Finset (Fin n)) (e h : Fin n)
    (he : e∈U) (hU : 2≤U.card) (hV : V.Nonempty) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D=(fun x=>
        (x e && decide (∃ v∈V,x v=true)) ||
        (x h && decide (∃ u∈U.erase e,x u=true))) ∧ D.size≤U.card+V.card := by
  have hc : (U.erase e).card=U.card-1 := Finset.card_erase_of_mem he
  have hE : (U.erase e).Nonempty := Finset.card_pos.mp (by omega)
  have hVc : 1≤V.card := Finset.card_pos.mpr hV
  have b1 := bld_and (bld_var e) (bld_anyFinset V hV)
  have b2 := bld_and (bld_var h) (bld_anyFinset (U.erase e) hE)
  apply bld_circuit
  exact bld_mono (bld_or b1 b2) (by omega)

end PEqualNP.Outside.L_meta_3754.Upper
