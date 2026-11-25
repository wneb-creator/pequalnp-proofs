import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.Normalization.Semantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

lemma circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

lemma W_nil (w : List Bool) : W [] w = w := rfl

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

lemma W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

lemma W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

lemma W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

lemma getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

lemma W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

lemma W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

lemma W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

lemma W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

lemma val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

lemma circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

lemma and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

lemma or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

end PEqualNP.Outside.L_meta_4970_aux.Normalization.Semantics

namespace PEqualNP.Outside.L_meta_4970_aux.Normalization

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev Test (n : ℕ) := (Fin n → Bool) → Prop
abbrev Term (n : ℕ) := Test n × Test n

def binary (b : Bool) (u v : ℕ) : Gate :=
  ⟨if b then .and else .or, [u, v]⟩

def combine {n} (b : Bool) (p q : Test n) : Test n :=
  fun x => if b then p x ∧ q x else p x ∨ q x

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (n : ℕ) (gs : List Gate) (i : ℕ) : Test n :=
  fun x => ((gs.foldl step (List.ofFn x)).getD i false) = true

lemma length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, step]; omega

lemma old_wire {n gs i} (hi : i < n + gs.length) (g : Gate) :
    W n (gs ++ [g]) i = W n gs i := by
  funext x
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp [W, List.foldl_append, step, List.getD, List.getElem?_append_left (hl ▸ hi : i < (gs.foldl step (List.ofFn x)).length)]

lemma new_wire (n) (gs : List Gate) (b u v) :
    W n (gs ++ [binary b u v]) (n + gs.length) =
      combine b (W n gs u) (W n gs v) := by
  funext x
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  cases b <;> simp [W, List.foldl_append, step, binary, GateOp.eval, combine,
    ← hl, List.getD]

def Layout (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), ∃ b u v, gs[i] = binary b u v ∧ u < n+i ∧ v < n+i

lemma layout_of {n} {C : Circuit} (h : IsAO2 n C) : Layout n C.gates := by
  intro i hi
  have hm := List.getElem_mem (l := C.gates) hi
  obtain ⟨u,v, huv⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  have hat : gateAt C i = C.gates[i] := by simp [gateAt, List.getD, hi]
  have hr := h.2.1 i hi
  rw [hat, huv] at hr
  obtain ho | ho := h.1 _ hm
  · exact ⟨true,u,v, by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp), hr v (by simp)⟩
  · exact ⟨false,u,v, by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp), hr v (by simp)⟩

lemma layout_ao {n gs} (h : Layout n gs) : IsAO2 n ⟨gs,0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    obtain ⟨b,u,v,he,-,-⟩ := h i hi
    rw [he]
    cases b <;> simp [binary]
  · intro i hi w hw
    change i < gs.length at hi
    obtain ⟨b,u,v,he,hu,hv⟩ := h i hi
    simp [gateAt, List.getD, hi, he, binary] at hw
    rcases hw with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    obtain ⟨b,u,v,he,-,-⟩ := h i hi
    simp [he,binary]

def Dirty {n} (F p : Test n) : Prop := ∃ x, p x ∧ ¬ F x

def Clean {n} (F : Test n) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), gs[i].op = .and → Dirty F (W n gs (n+i))

end PEqualNP.Outside.L_meta_4970_aux.Normalization

namespace PEqualNP.Outside.L_meta_4970_aux.TaggedModel

abbrev Test (n : ℕ) := (Fin n → Bool) → Prop
abbrev Signal (n : ℕ) := Test n × Finset (Fin n)
abbrev Term (n : ℕ) := Signal n × Signal n

def combine {n : ℕ} (b : Bool) (f g : Test n) : Test n :=
  fun x => if b then f x ∧ g x else f x ∨ g x

def taggedCombine {n : ℕ} (b : Bool) (f g : Signal n) : Signal n :=
  (combine b f.1 g.1, if b then ∅ else f.2 ∪ g.2)

def Dirty {n : ℕ} (F f : Test n) : Prop := ∃ x, f x ∧ ¬ F x

def Good {n : ℕ} (colour : Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, colour a = colour b

lemma good_subset {n : ℕ} (colour : Fin n → Bool) {S T : Finset (Fin n)}
    (h : S ⊆ T) (hT : Good colour T) : Good colour S := by
  intro a ha b hb
  exact hT a (h ha) b (h hb)

lemma taggedCombine_subset {n : ℕ} (b : Bool) {p q f g : Signal n}
    (hp : p.2 ⊆ f.2) (hq : q.2 ⊆ g.2) :
    (taggedCombine b p q).2 ⊆ (taggedCombine b f g).2 := by
  cases b
  · exact Finset.union_subset_union hp hq
  · exact Finset.Subset.refl ∅

lemma taggedCombine_comm {n : ℕ} (b : Bool) (f g : Signal n) :
    taggedCombine b f g = taggedCombine b g f := by
  apply Prod.ext
  · funext x
    cases b <;> simp [taggedCombine,combine,and_comm,or_comm]
  · cases b <;> simp [taggedCombine,Finset.union_comm]

def Hit {n : ℕ} (T : Finset (Term n)) (x : Fin n → Bool) : Prop :=
  ∃ t ∈ T, t.1.1 x ∧ t.2.1 x

def Covers {n : ℕ} (T : Finset (Term n)) (f p : Test n) : Prop :=
  ∀ x, f x → Hit T x ∨ p x

def Repr {n : ℕ} (R : Set (Signal n)) (P T : Finset (Term n)) (f : Signal n) : Prop :=
  (∃ p ∈ R, p.2 ⊆ f.2 ∧ (∀ x, p.1 x → f.1 x) ∧ Covers T f.1 p.1) ∨
  ∃ t ∈ P, Covers T f.1 (fun x => t.1.1 x ∧ t.2.1 x)

def Sound {n : ℕ} (F : Test n) (R : Set (Signal n)) (P : Finset (Term n)) : Prop :=
  ∀ t ∈ P, t.1 ∈ R ∧ t.2 ∈ R ∧ ∀ x, t.1.1 x → t.2.1 x → F x

def Model {n : ℕ} (F : Test n) (Pool : Set (Signal n) → ℕ → Prop)
    (S : Set (Signal n)) (k : ℕ) : Prop :=
  ∃ R P T c, Pool R c ∧ Sound F R P ∧ T ⊆ P ∧
    c + P.card + T.card ≤ k ∧ ∀ f ∈ S, Repr R P T f

lemma hit_mono {n : ℕ} {T U : Finset (Term n)} (h : T ⊆ U) {x} :
    Hit T x → Hit U x := fun ⟨t,ht,ha⟩ => ⟨t,h ht,ha⟩

lemma repr_mono {n : ℕ} {R R' : Set (Signal n)} {P P' T T' : Finset (Term n)} {f}
    (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T') (h : Repr R P T f) :
    Repr R' P' T' f := by
  have liftCov {a : Test n} (hc : Covers T f.1 a) : Covers T' f.1 a :=
    fun x hx => (hc x hx).imp (hit_mono ht) id
  rcases h with ⟨p,hm,hbound,hl,hc⟩ | ⟨t,hm,hc⟩
  · exact Or.inl ⟨p,hr hm,hbound,hl,liftCov hc⟩
  · exact Or.inr ⟨t,hp hm,liftCov hc⟩

lemma cov_combine {n : ℕ} {T : Finset (Term n)} {f g p q : Test n} (b : Bool)
    (hp : Covers T f p) (hq : Covers T g q) :
    Covers T (combine b f g) (combine b p q) := by
  intro x hx
  by_cases hh : Hit T x
  · exact Or.inl hh
  · right
    have ha := fun h => (hp x h).resolve_left hh
    have hb := fun h => (hq x h).resolve_left hh
    cases b
    · exact hx.elim (fun h => Or.inl (ha h)) (fun h => Or.inr (hb h))
    · exact ⟨ha hx.1,hb hx.2⟩

lemma model_add {n : ℕ} (F : Test n) (colour : Fin n → Bool)
    (Pool : Set (Signal n) → ℕ → Prop)
    (pool_dirty : ∀ R c, Pool R c → ∀ p ∈ R, Dirty F p.1)
    (pool_append : ∀ R c, Pool R c → ∀ p ∈ R, ∀ q ∈ R, ∀ b : Bool,
      Dirty F (combine b p.1 q.1) → Good colour (taggedCombine b p q).2 →
      Pool (insert (taggedCombine b p q) R) (c+1))
    {S : Set (Signal n)} {k : ℕ} (h : Model F Pool S k)
    {f g : Signal n} (hf : f ∈ S) (hg : g ∈ S) (b : Bool)
    (hgood : Good colour (taggedCombine b f g).2) :
    Model F Pool (insert (taggedCombine b f g) S) (k+1) := by
  classical
  obtain ⟨R,P,T,c,pool,sound,sub,budget,reps⟩ := h
  have finish {s : Signal n} {R' P' T' c'}
      (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T')
      (pl : Pool R' c') (so : Sound F R' P') (su : T' ⊆ P')
      (bu : c'+P'.card+T'.card ≤ k+1) (rep : Repr R' P' T' s) :
      Model F Pool (insert s S) (k+1) := by
    refine ⟨R',P',T',c',pl,so,su,bu,?_⟩
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact rep
    · exact repr_mono hr hp ht (reps a ha)
  have virtual {a d : Signal n} {t} (ht : t ∈ P)
      (hc : Covers T a.1 (fun x => t.1.1 x ∧ t.2.1 x)) (hd : Repr R P T d) :
      Model F Pool (insert (taggedCombine b a d) S) (k+1) := by
    cases b
    · let U := insert t T
      have incl : T ⊆ U := Finset.subset_insert t T
      have cover {s : Test n} (cs : Covers T d.1 s) :
          Covers U (taggedCombine false a d).1 s := by
        intro x hx
        rcases hx with ha | hd'
        · rcases hc x ha with hh | hh
          · exact Or.inl (hit_mono incl hh)
          · exact Or.inl ⟨t,Finset.mem_insert_self _ _,hh⟩
        · exact (cs x hd').imp (hit_mono incl) id
      apply finish (Set.Subset.rfl) (Finset.Subset.refl _) incl pool sound
        (Finset.insert_subset ht sub) (by have := Finset.card_insert_le t T; dsimp [U]; omega)
      rcases hd with ⟨q,hq,hbound,hlo,hcov⟩ | ⟨s,hs,hcov⟩
      · exact Or.inl ⟨q,hq,fun u hu => Finset.mem_union_right _ (hbound hu),
          fun x hx => Or.inr (hlo x hx),cover hcov⟩
      · exact Or.inr ⟨s,hs,cover hcov⟩
    · exact finish (Set.Subset.rfl) (Finset.Subset.refl _) (Finset.Subset.refl _)
        pool sound sub (by omega) (Or.inr ⟨t,ht,fun x hx => hc x hx.1⟩)
  have rf := reps f hf
  have rg := reps g hg
  rcases rf with ⟨p,hp,bp,lp,cp⟩ | ⟨t,ht,ct⟩
  · rcases rg with ⟨q,hq,bq,lq,cq⟩ | ⟨t,ht,ct⟩
    · have cov := cov_combine b cp cq
      by_cases dirty : Dirty F (combine b p.1 q.1)
      · have hr : R ⊆ insert (taggedCombine b p q) R := Set.subset_insert _ _
        have htgood := good_subset colour (taggedCombine_subset b bp bq) hgood
        refine finish hr (Finset.Subset.refl _) (Finset.Subset.refl _)
          (pool_append R c pool p hp q hq b dirty htgood) ?_ sub (by omega) ?_
        · intro t ht
          obtain ⟨ha,hb,hf'⟩ := sound t ht
          exact ⟨hr ha,hr hb,hf'⟩
        · refine Or.inl ⟨taggedCombine b p q, Set.mem_insert _ _,
            taggedCombine_subset b bp bq, ?_,cov⟩
          intro x hx
          cases b
          · exact hx.elim (fun h => Or.inl (lp x h)) (fun h => Or.inr (lq x h))
          · exact ⟨lp x hx.1,lq x hx.2⟩
      · cases b
        · obtain ⟨x,hx,hn⟩ := pool_dirty R c pool p hp
          exact (dirty ⟨x,Or.inl hx,hn⟩).elim
        · let t : Term n := (p,q)
          have incl := Finset.subset_insert t P
          refine finish (Set.Subset.rfl) incl (Finset.Subset.refl _) pool ?_ (sub.trans incl)
            (by have := Finset.card_insert_le t P; omega) ?_
          · intro s hs
            rcases Finset.mem_insert.mp hs with rfl | hs
            · refine ⟨hp,hq,?_⟩
              intro x hx hy
              by_contra hn
              exact dirty ⟨x,⟨hx,hy⟩,hn⟩
            · exact sound s hs
          · exact Or.inr ⟨t,Finset.mem_insert_self _ _,cov⟩
    · rw [taggedCombine_comm b f g]
      exact virtual ht ct (Or.inl ⟨p,hp,bp,lp,cp⟩)
  · exact virtual ht ct rg

end PEqualNP.Outside.L_meta_4970_aux.TaggedModel

namespace PEqualNP.Outside.L_meta_4970_aux.TaggedPool

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970_aux.Normalization

abbrev Signal (n : ℕ) := TaggedModel.Signal n

def Safe {n : ℕ} (colour : Fin n → Bool)
    (reach : List Gate → ℕ → Finset (Fin n)) (gs : List Gate) : Prop :=
  ∀ j < gs.length, TaggedModel.Good colour (reach gs (n+j))

def Pool {n : ℕ} (F : Test n) (colour : Fin n → Bool)
    (reach : List Gate → ℕ → Finset (Fin n)) (R : Set (Signal n)) (c : ℕ) : Prop :=
  ∃ gs : List Gate, gs.length ≤ c ∧ Layout n gs ∧ Clean F gs ∧ Safe colour reach gs ∧
    ∀ p ∈ R, Dirty F p.1 ∧ ∃ i < n+gs.length, W n gs i = p.1 ∧ reach gs i ⊆ p.2

lemma pool_dirty {n : ℕ} (F : Test n) (colour : Fin n → Bool)
    (reach : List Gate → ℕ → Finset (Fin n)) (R : Set (Signal n)) (c : ℕ)
    (h : Pool F colour reach R c) : ∀ p ∈ R, TaggedModel.Dirty F p.1 := by
  obtain ⟨gs,_,_,_,_,hr⟩ := h
  intro p hp
  exact (hr p hp).1

lemma pool_append {n : ℕ} (F : Test n) (colour : Fin n → Bool)
    (reach : List Gate → ℕ → Finset (Fin n))
    (reach_old : ∀ gs g i, i < n+gs.length → reach (gs ++ [g]) i = reach gs i)
    (reach_new : ∀ gs b u v, u < n+gs.length → v < n+gs.length →
      reach (gs ++ [binary b u v]) (n+gs.length) =
        if b then ∅ else reach gs u ∪ reach gs v)
    (R : Set (Signal n)) (c : ℕ) (h : Pool F colour reach R c)
    (p : Signal n) (hp : p ∈ R) (q : Signal n) (hq : q ∈ R) (b : Bool)
    (hd : TaggedModel.Dirty F (TaggedModel.combine b p.1 q.1))
    (hgood : TaggedModel.Good colour (TaggedModel.taggedCombine b p q).2) :
    Pool F colour reach (insert (TaggedModel.taggedCombine b p q) R) (c+1) := by
  classical
  obtain ⟨gs,hc,hl,hcl,hsafe,hr⟩ := h
  obtain ⟨u,hu,hpu,hru⟩ := (hr p hp).2
  obtain ⟨v,hv,hqv,hrv⟩ := (hr q hq).2
  let g := binary b u v
  have hn : W n (gs ++ [g]) (n+gs.length) = TaggedModel.combine b p.1 q.1 := by
    rw [new_wire, hpu, hqv]
    rfl
  have hreach : reach (gs ++ [g]) (n+gs.length) ⊆
      (TaggedModel.taggedCombine b p q).2 := by
    rw [reach_new gs b u v hu hv]
    cases b
    · exact Finset.union_subset_union hru hrv
    · exact Finset.Subset.refl ∅
  refine ⟨gs ++ [g],by simp; omega,?_,?_,?_,?_⟩
  · intro i hi
    by_cases hj : i < gs.length
    · simpa [List.getElem_append_left hj] using hl i hj
    · have : i = gs.length := by simp at hi; omega
      subst i
      exact ⟨b,u,v,by simp [g],hu,hv⟩
  · intro i hi ho
    by_cases hj : i < gs.length
    · rw [old_wire (by omega)]
      exact hcl i hj (by simpa [List.getElem_append_left hj] using ho)
    · have : i = gs.length := by simp at hi; omega
      subst i
      rwa [hn]
  · intro i hi
    by_cases hj : i < gs.length
    · rw [reach_old gs g (n+i) (by omega)]
      exact hsafe i hj
    · have : i = gs.length := by simp at hi; omega
      subst i
      exact TaggedModel.good_subset colour hreach hgood
  · intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact ⟨hd,n+gs.length,by simp,hn,hreach⟩
    · obtain ⟨hsd,i,hi,he,hri⟩ := hr s hs
      refine ⟨hsd,i,by simp; omega,(old_wire hi g).trans he,?_⟩
      rwa [reach_old gs g i hi]

def Signals {n : ℕ} (reach : List Gate → ℕ → Finset (Fin n))
    (gs : List Gate) : Set (Signal n) :=
  {p | ∃ i < n+gs.length, (W n gs i,reach gs i) = p}

lemma initial {n : ℕ} (F : Test n) (colour : Fin n → Bool)
    (reach : List Gate → ℕ → Finset (Fin n))
    (inputs : ∀ i < n, Dirty F (W n [] i)) :
    TaggedModel.Model F (Pool F colour reach) (Signals reach []) 0 := by
  classical
  refine ⟨Signals reach [],∅,∅,0,?_,by simp [TaggedModel.Sound],by simp,by simp,?_⟩
  · refine ⟨[],by simp,by simp [Layout],by simp [Clean],by simp [Safe],?_⟩
    intro p hp
    obtain ⟨i,hi,rfl⟩ := hp
    exact ⟨inputs i (by simpa using hi),i,hi,rfl,Finset.Subset.refl _⟩
  · intro p hp
    exact Or.inl ⟨p,hp,Finset.Subset.refl _,fun _ => id,fun _ hx => Or.inr hx⟩

lemma simulate {n : ℕ} (F : Test n) (colour : Fin n → Bool)
    (reach : List Gate → ℕ → Finset (Fin n))
    (reach_old : ∀ gs g i, i < n+gs.length → reach (gs ++ [g]) i = reach gs i)
    (reach_new : ∀ gs b u v, u < n+gs.length → v < n+gs.length →
      reach (gs ++ [binary b u v]) (n+gs.length) =
        if b then ∅ else reach gs u ∪ reach gs v)
    (inputs : ∀ i < n, Dirty F (W n [] i)) (gs : List Gate)
    (hl : Layout n gs) (hsafe : Safe colour reach gs) :
    TaggedModel.Model F (Pool F colour reach) (Signals reach gs) gs.length := by
  classical
  induction gs using List.reverseRecOn with
  | nil => exact initial F colour reach inputs
  | append_singleton gs last ih =>
    have layout : Layout n gs := by
      intro i hi
      obtain ⟨b,u,v,he,hu,hv⟩ := hl i (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hi).symm.trans he,hu,hv⟩
    have safe : Safe colour reach gs := by
      intro i hi
      have h := hsafe i (by simp; omega)
      rwa [reach_old gs last (n+i) (by omega)] at h
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst last
    have hg : TaggedModel.Good colour
        (TaggedModel.taggedCombine b (W n gs u,reach gs u) (W n gs v,reach gs v)).2 := by
      have h := hsafe gs.length (by simp)
      rw [reach_new gs b u v hu hv] at h
      exact h
    have h := TaggedModel.model_add F colour (Pool F colour reach)
      (pool_dirty F colour reach) (pool_append F colour reach reach_old reach_new)
      (ih layout safe) (f := (W n gs u,reach gs u)) (g := (W n gs v,reach gs v))
      ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩ b hg
    obtain ⟨R,P,T,c,hp,hs,ht,hb,hr⟩ := h
    refine ⟨R,P,T,c,hp,hs,ht,by simpa using hb,?_⟩
    intro p hm
    obtain ⟨i,hi,rfl⟩ := hm
    by_cases hj : i < n+gs.length
    · rw [old_wire hj,reach_old gs (binary b u v) i hj]
      exact hr _ (Set.mem_insert_of_mem _ ⟨i,hj,rfl⟩)
    · have : i = n+gs.length := by simp at hi; omega
      subst i
      rw [new_wire,reach_new gs b u v hu hv]
      exact hr _ (Set.mem_insert _ _)

end PEqualNP.Outside.L_meta_4970_aux.TaggedPool

namespace PEqualNP.Outside.L_meta_4970_aux.ReachBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n+k) g ↔ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n+k ∧ OrReaches n C i g)) := by
  rw [orReaches_iff]
  simp only [hk,true_and]

lemma reach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n+k) k := (reach_iff n C k k hk).mpr (Or.inl rfl)

lemma reach_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → n+g ≤ w ∧ w < n+C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hn : n ≤ w := hr.1
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    obtain ⟨hk,h⟩ := (orReaches_iff n C k g).mp hr
    refine ⟨?_,by omega⟩
    rcases h with rfl | ⟨_,u,_,hu,hr⟩
    · omega
    · have hh := (ih u hu hr).1
      omega

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

lemma orIn_input (n : ℕ) (C : Circuit) (u : Fin n) : orIn n C u.val = {u} := by
  ext v
  rw [mem_orIn,Finset.mem_singleton]
  constructor
  · rintro (h | ⟨j,_,hr,_,_⟩)
    · exact Fin.ext h
    · have h := hr.1
      have hu := u.isLt
      omega
  · intro h
    subst v
    exact Or.inl rfl

lemma gateAt_append_old (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAt ⟨gs++[g],0⟩ j = gateAt ⟨gs,0⟩ j := by
  simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_append_left hj]

lemma gateAt_append_new (gs : List Gate) (g : Gate) : gateAt ⟨gs++[g],0⟩ gs.length = g := by
  simp [gateAt,List.getD_eq_getElem?_getD]

lemma reaches_append_old (n : ℕ) (gs : List Gate) (g : Gate) (w j : ℕ)
    (hw : w < n+gs.length) :
    OrReaches n ⟨gs++[g],0⟩ w j ↔ OrReaches n ⟨gs,0⟩ w j := by
  by_cases hn : n ≤ w
  · have hk : w-n < gs.length := by omega
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by rw [orSets_len]; simp
    unfold OrReaches orSets
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,orStep]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : w-n < (gs.foldl (orStep n) []).length)]
  · simp only [OrReaches,hn,false_and]

lemma orIn_append_old (n : ℕ) (gs : List Gate) (g : Gate) (w : ℕ)
    (hw : w < n+gs.length) :
    orIn n ⟨gs++[g],0⟩ w = orIn n ⟨gs,0⟩ w := by
  ext v
  rw [mem_orIn,mem_orIn]
  constructor
  · rintro (h | ⟨j,hj,hr,hop,hin⟩)
    · exact Or.inl h
    · have hj' : j < gs.length := by
        have h := (reach_bound n ⟨gs++[g],0⟩ j w hr).1
        omega
      rw [gateAt_append_old gs g j hj'] at hop hin
      exact Or.inr ⟨j,hj',(reaches_append_old n gs g w j hw).mp hr,hop,hin⟩
  · rintro (h | ⟨j,hj,hr,hop,hin⟩)
    · exact Or.inl h
    · rw [← gateAt_append_old gs g j hj] at hop hin
      exact Or.inr ⟨j,by simpa using Nat.lt_succ_of_lt hj,(reaches_append_old n gs g w j hw).mpr hr,hop,hin⟩

lemma orIn_and (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) : orIn n C (n+j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rcases (mem_orIn n C (n+j) v).mp hv with h | ⟨k,hk,hr,hko,_⟩
  · have hv := v.isLt
    omega
  · rcases (reach_iff n C j k hj).mp hr with h | ⟨hjo,_⟩
    · subst k
      rw [hop] at hko
      cases hko
    · rw [hop] at hjo
      cases hjo

lemma orIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, mem_orIn, mem_orIn, mem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (reach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, reach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (reach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, reach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (reach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma orIn_append_and (n : ℕ) (gs : List Gate) (u v : ℕ) :
    orIn n ⟨gs++[⟨GateOp.and,[u,v]⟩],0⟩ (n+gs.length) = ∅ := by
  apply orIn_and n _ gs.length (by simp)
  rw [gateAt_append_new]

lemma orIn_append_or (n : ℕ) (gs : List Gate) (u v : ℕ)
    (hu : u < n+gs.length) (hv : v < n+gs.length) :
    orIn n ⟨gs++[⟨GateOp.or,[u,v]⟩],0⟩ (n+gs.length) =
      orIn n ⟨gs,0⟩ u ∪ orIn n ⟨gs,0⟩ v := by
  rw [orIn_or n _ gs.length u v (by simp) (by rw [gateAt_append_new])
    (by rw [gateAt_append_new]) hu hv]
  rw [orIn_append_old n gs _ u hu,orIn_append_old n gs _ v hv]

def binary (b : Bool) (u v : ℕ) : Gate := ⟨if b then GateOp.and else GateOp.or,[u,v]⟩

lemma orIn_append_binary (n : ℕ) (gs : List Gate) (b : Bool) (u v : ℕ)
    (hu : u < n+gs.length) (hv : v < n+gs.length) :
    orIn n ⟨gs++[binary b u v],0⟩ (n+gs.length) =
      if b then ∅ else orIn n ⟨gs,0⟩ u ∪ orIn n ⟨gs,0⟩ v := by
  cases b
  · exact orIn_append_or n gs u v hu hv
  · exact orIn_append_and n gs u v

end PEqualNP.Outside.L_meta_4970_aux.ReachBridge

namespace PEqualNP.Outside.L_meta_4970_aux.Normalization

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm


def unit {n : ℕ} (u : Fin n) : Fin n → Bool := fun v => decide (v = u)

def pureOr {n : ℕ} (Q : Finset (Fin n)) : Test n :=
  fun x => ∃ u ∈ Q, x u = true

lemma wire_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (w : ℕ)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    W n C.gates w x → W n C.gates w y :=
  Semantics.mono n C hC.1 x y hxy w

lemma pure_or_and_prime_bool {n : ℕ} (Q : Finset (Fin n)) (f g : Test n)
    (hf : ∀ x y, (∀ u, x u = true → y u = true) → f x → f y)
    (hg : ∀ x y, (∀ u, x u = true → y u = true) → g x → g y)
    (h : combine true f g = pureOr Q) : f = pureOr Q ∨ g = pureOr Q := by
  let z : Fin n → Bool := fun u => decide (u ∉ Q)
  have hz : ¬ (f z ∧ g z) := by
    intro hz
    have hp : pureOr Q z := by rw [← h]; exact hz
    obtain ⟨u,hu,huz⟩ := hp
    have hnu : u ∉ Q := by simpa [z] using huz
    exact hnu hu
  have go (k : Test n) (hk : ∀ x y, (∀ u, x u = true → y u = true) → k x → k y)
      (hkz : ¬ k z) (hlo : ∀ x, pureOr Q x → k x) : k = pureOr Q := by
    funext x
    apply propext
    constructor
    · intro hx
      by_contra hn
      apply hkz
      apply hk x z ?_ hx
      intro u hu
      have hnu : u ∉ Q := fun hmem => hn ⟨u,hmem,hu⟩
      simpa [z] using hnu
    · exact hlo x
  rcases not_and_or.mp hz with hfz | hgz
  · exact Or.inl (go f hf hfz (fun x hx => by
      have hfg : f x ∧ g x := by rw [← h] at hx; exact hx
      exact hfg.1))
  · exact Or.inr (go g hg hgz (fun x hx => by
      have hfg : f x ∧ g x := by rw [← h] at hx; exact hx
      exact hfg.2))

lemma pure_or_wire_has_or (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card) :
    ∀ w, w < n + C.gates.length → W n C.gates w = pureOr Q →
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.or ∧
        W n C.gates (n + j) = pureOr Q := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwire
    by_cases hin : w < n
    · have hu : ∀ u ∈ Q, (⟨w,hin⟩ : Fin n) = u := by
        intro u hmem
        have ht : W n C.gates w (unit u) := by
          rw [hwire]
          exact ⟨u,hmem,by simp [unit]⟩
        change Semantics.val C (List.ofFn (unit u)) w = true at ht
        rw [Semantics.val_ofFn_lt C (unit u) w hin] at ht
        simpa [unit] using ht
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
      exact (hab ((hu a ha).symm.trans (hu b hb))).elim
    · obtain ⟨j,rfl⟩ : ∃ j, w = n + j := ⟨w-n,by omega⟩
      have hj : j < C.gates.length := by omega
      rcases hC.1 _ (Semantics.gateAt_mem hj) with hop | hop
      · let a := (gateAt C j).inputs.getD 0 0
        let b := (gateAt C j).inputs.getD 1 0
        have hlen := hC.2.2 _ (Semantics.gateAt_mem hj)
        obtain ⟨u,v,hinputs⟩ := List.length_eq_two.mp hlen
        have ha : a < n+j := by
          have hr := hC.2.1 j hj u (by simp [hinputs])
          simpa [a,hinputs] using hr
        have hb : b < n+j := by
          have hr := hC.2.1 j hj v (by simp [hinputs])
          simpa [b,hinputs] using hr
        have heq : combine true (W n C.gates a) (W n C.gates b) = pureOr Q := by
          rw [← hwire]
          funext x
          apply propext
          change (Semantics.val C (List.ofFn x) a = true ∧
            Semantics.val C (List.ofFn x) b = true) ↔
            Semantics.val C (List.ofFn x) (n+j) = true
          rw [Semantics.and_val n C hC _ (by simp) j hj hop]
          simp only [Bool.and_eq_true, a, b]
        rcases pure_or_and_prime_bool Q (W n C.gates a) (W n C.gates b)
          (wire_mono n C hC a) (wire_mono n C hC b) heq with hpa | hpb
        · exact ih a ha (by omega) hpa
        · exact ih b hb (by omega) hpb
      · exact ⟨j,hj,hop,hwire⟩

end PEqualNP.Outside.L_meta_4970_aux.Normalization

namespace PEqualNP.Outside.L_meta_4970_aux.TaggedPool

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970_aux.Normalization

def actualReach (n : ℕ) (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  PEqualNP.TopForm.orIn n ⟨gs,0⟩ w

lemma actualReach_old (n : ℕ) (gs : List Gate) (g : Gate) (i : ℕ)
    (hi : i < n+gs.length) : actualReach n (gs ++ [g]) i = actualReach n gs i :=
  ReachBridge.orIn_append_old n gs g i hi

lemma actualReach_new (n : ℕ) (gs : List Gate) (b : Bool) (u v : ℕ)
    (hu : u < n+gs.length) (hv : v < n+gs.length) :
    actualReach n (gs ++ [binary b u v]) (n+gs.length) =
      if b then ∅ else actualReach n gs u ∪ actualReach n gs v :=
  ReachBridge.orIn_append_binary n gs b u v hu hv

lemma safe_of_tCount_zero (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (colour : ℕ → Bool) (hT : PEqualNP.TwoColour.tCount n C colour = 0) :
    Safe (fun i : Fin n => colour i.val) (actualReach n) C.gates := by
  have hemp : PEqualNP.TwoColour.twoColour n C colour = ∅ :=
    Finset.card_eq_zero.mp hT
  intro j hj a ha b hb
  rcases hC.1 _ (Semantics.gateAt_mem hj) with hop | hop
  · have he : actualReach n C.gates (n+j) = ∅ :=
      ReachBridge.orIn_and n C j hj hop
    rw [he] at ha
    exact (Finset.notMem_empty _ ha).elim
  · by_contra hne
    have hmix : (colour a.val = false ∧ colour b.val = true) ∨
        (colour b.val = false ∧ colour a.val = true) := by
      cases hca : colour a.val <;> cases hcb : colour b.val <;> simp_all
    have ht : PEqualNP.TwoColour.IsTwoColour n C colour j := by
      refine ⟨hj,hop,?_⟩
      rcases hmix with ⟨hfa,htb⟩ | ⟨hfb,hta⟩
      · exact ⟨⟨a,ha,hfa⟩,⟨b,hb,htb⟩⟩
      · exact ⟨⟨b,hb,hfb⟩,⟨a,ha,hta⟩⟩
    have hm : j ∈ PEqualNP.TwoColour.twoColour n C colour := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,ht⟩
    rw [hemp] at hm
    exact Finset.notMem_empty _ hm

lemma tCount_zero_of_safe (n : ℕ) (gs : List Gate) (colour : ℕ → Bool)
    (h : Safe (fun i : Fin n => colour i.val) (actualReach n) gs) :
    PEqualNP.TwoColour.tCount n ⟨gs,0⟩ colour = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨_,hj,_,⟨a,ha,hca⟩,⟨b,hb,hcb⟩⟩ := Finset.mem_filter.mp hj
  have he := h j hj a ha b hb
  change colour a.val = colour b.val at he
  rw [hca,hcb] at he
  contradiction

lemma pool_mono {n : ℕ} {F : Test n} {colour : Fin n → Bool}
    {reach : List Gate → ℕ → Finset (Fin n)} {R : Set (Signal n)} {c : ℕ}
    (hpool : Pool F colour reach R c) {p : Signal n} (hp : p ∈ R)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) : p.1 x → p.1 y := by
  obtain ⟨gs,_,hLayout,_,_,hreal⟩ := hpool
  obtain ⟨i,_,heq,_⟩ := (hreal p hp).2
  intro hx
  have hx' : Semantics.val ⟨gs,0⟩ (List.ofFn x) i = true := by
    change W n gs i x
    rwa [heq]
  have hy := Semantics.mono n ⟨gs,0⟩ (layout_ao hLayout).1 x y hxy i hx'
  change W n gs i y at hy
  rwa [heq] at hy

lemma pure_or_repr_physical {n : ℕ} {F : Test n} {colour : Fin n → Bool}
    {reach : List Gate → ℕ → Finset (Fin n)} {R : Set (Signal n)}
    {P T : Finset (TaggedModel.Term n)} {c : ℕ} (hpool : Pool F colour reach R c)
    (hsound : TaggedModel.Sound F R P) (hsub : T ⊆ P)
    (hzero : ∀ u : Fin n, ¬ F (unit u))
    (Q B : Finset (Fin n)) (hQ : Q.Nonempty)
    (hrep : TaggedModel.Repr R P T (pureOr Q,B)) :
    ∃ p ∈ R, p.1 = pureOr Q := by
  have nhit : ∀ u : Fin n, ¬ TaggedModel.Hit T (unit u) := by
    intro u hh
    obtain ⟨t,ht,ha,hb⟩ := hh
    exact hzero u ((hsound t (hsub ht)).2.2 (unit u) ha hb)
  have hs : ∀ u ∈ Q, pureOr Q (unit u) := by
    intro u hu
    exact ⟨u,hu,by simp [unit]⟩
  rcases hrep with ⟨p,hp,_,hle,hcov⟩ | ⟨t,ht,hcov⟩
  · refine ⟨p,hp,?_⟩
    funext x
    apply propext
    constructor
    · exact hle x
    · rintro ⟨u,hu,hxu⟩
      have hpunit : p.1 (unit u) := (hcov (unit u) (hs u hu)).resolve_left (nhit u)
      apply pool_mono hpool hp (unit u) x ?_ hpunit
      intro v hv
      have h : v = u := by simpa [unit] using hv
      simpa [h] using hxu
  · obtain ⟨u,hu⟩ := hQ
    have pair := (hcov (unit u) (hs u hu)).resolve_left (nhit u)
    exact (hzero u ((hsound t ht).2.2 (unit u) pair.1 pair.2)).elim

lemma extract_tCount_pure_or {n} (F : Test n)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hzero : ∀ u : Fin n, ¬ F (unit u))
    (C : Circuit) (hl : IsAO2 n C) (hne : ∃ x, F x)
    (ho : W n C.gates C.output = F) (colour : ℕ → Bool)
    (hT : PEqualNP.TwoColour.tCount n C colour = 0) :
    ∃ (gs : List Gate) (U : Finset (ℕ × ℕ)), Layout n gs ∧ Clean F gs ∧
      PEqualNP.TwoColour.tCount n ⟨gs,0⟩ colour = 0 ∧
      (∀ t ∈ U, ∀ x, W n gs t.1 x → W n gs t.2 x → F x) ∧
      (∀ x, F x → ∃ t ∈ U, W n gs t.1 x ∧ W n gs t.2 x) ∧
      gs.length + 2 * U.card ≤ C.size + 1 ∧
      ∀ Q : Finset (Fin n), 2 ≤ Q.card →
        (∃ i < n+C.gates.length, W n C.gates i = pureOr Q) →
        ∃ j < gs.length, (gateAt ⟨gs,0⟩ j).op = GateOp.or ∧
          W n gs (n+j) = pureOr Q := by
  classical
  obtain ⟨R,P,T,c,pool,sound,sub,budget,reps⟩ :=
    simulate F (fun i : Fin n => colour i.val) (actualReach n)
      (actualReach_old n) (actualReach_new n) inputs C.gates (layout_of hl)
      (safe_of_tCount_zero n C hl colour hT)
  have hout : C.output < n+C.gates.length := by
    by_contra! h
    obtain ⟨x,hx⟩ := hne
    rw [← ho] at hx
    have hlen := length_fold C.gates (List.ofFn x)
    simp only [List.length_ofFn] at hlen
    simp [W, List.getD, List.getElem?_eq_none (hlen ▸ h :
        (C.gates.foldl step (List.ofFn x)).length ≤ C.output)] at hx
  have preserved : ∀ Q : Finset (Fin n), Q.Nonempty →
      (∃ i < n+C.gates.length, W n C.gates i = pureOr Q) →
      ∃ p ∈ R, p.1 = pureOr Q := by
    intro Q hQ hsignal
    obtain ⟨i,hi,hie⟩ := hsignal
    apply pure_or_repr_physical pool sound sub hzero Q (actualReach n C.gates i) hQ
    apply reps
    exact ⟨i,hi,Prod.ext hie rfl⟩
  obtain ⟨gs,hc,hg,hclean,hsafe,real⟩ := pool
  have rep := reps (F,actualReach n C.gates C.output) ⟨C.output,hout,Prod.ext ho rfl⟩
  rcases rep with ⟨p,hp,_,hlo,_⟩ | ⟨t,ht,hcov⟩
  · obtain ⟨x,hx,hn⟩ := (real p hp).1
    exact (hn (hlo x hx)).elim
  · let U := insert t T
    have hu : U ⊆ P := Finset.insert_subset ht sub
    have cu := Finset.card_le_card hu
    have ct : U.card ≤ T.card + 1 := Finset.card_insert_le t T
    let index (p : Signal n) : ℕ := if hp : p ∈ R then ((real p hp).2).choose else 0
    have idx {p : Signal n} (hp : p ∈ R) : W n gs (index p) = p.1 := by
      simpa [index,hp] using ((real p hp).2).choose_spec.2.1
    let enc (s : TaggedModel.Term n) := (index s.1,index s.2)
    refine ⟨gs,U.image enc,hg,hclean,tCount_zero_of_safe n gs colour hsafe,?_,?_,?_,?_⟩
    · intro v hv
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨ha,hb,hsafe⟩ := sound s (hu hs)
      simpa only [enc,idx ha,idx hb] using hsafe
    · intro x hx
      have hit : TaggedModel.Hit U x := by
        rcases hcov x hx with hh | hh
        · exact TaggedModel.hit_mono (Finset.subset_insert t T) hh
        · exact ⟨t,Finset.mem_insert_self _ _,hh⟩
      obtain ⟨s,hs,ha,hb⟩ := hit
      obtain ⟨hm,hn,_⟩ := sound s (hu hs)
      exact ⟨enc s,Finset.mem_image_of_mem enc hs,by simpa only [enc,idx hm] using ha,
        by simpa only [enc,idx hn] using hb⟩
    · have h := Finset.card_image_le (s := U) (f := enc)
      unfold Circuit.size
      omega
    · intro Q hQ hsignal
      have hn : Q.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p,hp,hpQ⟩ := preserved Q hn hsignal
      obtain ⟨i,hi,hip,_⟩ := (real p hp).2
      exact pure_or_wire_has_or n ⟨gs,0⟩ (layout_ao hg) Q hQ i hi (hip.trans hpQ)

end PEqualNP.Outside.L_meta_4970_aux.TaggedPool
