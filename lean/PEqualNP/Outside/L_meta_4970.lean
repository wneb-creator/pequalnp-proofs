import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

namespace H8Tagged

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev Test (n : ℕ) := (Fin n → Bool) → Prop
abbrev Signal (n : ℕ) := Test n × Finset (Fin n)
abbrev Term (n : ℕ) := Signal n × Signal n

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

def traceStep {n : ℕ} (w : List (Finset (Fin n))) (g : Gate) : List (Finset (Fin n)) :=
  w ++ [match g.op with
    | .or => (g.inputs.map fun i => w.getD i ∅).foldl (fun (a b : Finset (Fin n)) => a ∪ b) ∅
    | _ => ∅]

def trace (n : ℕ) (gs : List Gate) (i : ℕ) : Finset (Fin n) :=
  (gs.foldl traceStep (List.ofFn fun j : Fin n => {j})).getD i ∅

def tagged (n : ℕ) (gs : List Gate) (i : ℕ) : Signal n :=
  (W n gs i, trace n gs i)

def tcombine {n : ℕ} (b : Bool) (p q : Signal n) : Signal n :=
  (combine b p.1 q.1, if b then ∅ else p.2 ∪ q.2)

lemma trace_length {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) :
    (gs.foldl traceStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, traceStep]; omega

lemma old_trace {n gs i} (hi : i < n + gs.length) (g : Gate) :
    trace n (gs ++ [g]) i = trace n gs i := by
  have hl := trace_length gs (List.ofFn fun j : Fin n => {j})
  simp only [List.length_ofFn] at hl
  simp [trace, List.foldl_append, traceStep, List.getD,
    List.getElem?_append_left (hl ▸ hi : i < (gs.foldl traceStep (List.ofFn fun j : Fin n => {j})).length)]

lemma new_trace (n) (gs : List Gate) (b u v) :
    trace n (gs ++ [binary b u v]) (n + gs.length) =
      if b then ∅ else trace n gs u ∪ trace n gs v := by
  have hl := trace_length gs (List.ofFn fun j : Fin n => {j})
  simp only [List.length_ofFn] at hl
  cases b <;> simp [trace, List.foldl_append, traceStep, binary,
    ← hl, List.getD]

lemma old_tagged {n gs i} (hi : i < n + gs.length) (g : Gate) :
    tagged n (gs ++ [g]) i = tagged n gs i := by
  simp only [tagged, old_wire hi, old_trace hi]

lemma new_tagged (n) (gs : List Gate) (b u v) :
    tagged n (gs ++ [binary b u v]) (n + gs.length) =
      tcombine b (tagged n gs u) (tagged n gs v) := by
  simp only [tagged, new_wire, new_trace, tcombine]

def Dirty {n} (F p : Test n) : Prop := ∃ x, p x ∧ ¬ F x

def Clean {n} (F : Test n) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), gs[i].op = .and → Dirty F (W n gs (n+i))

def Tame (n : ℕ) (colour : Fin n → Bool) (gs : List Gate) : Prop :=
  ∀ i < n + gs.length, ∀ a ∈ trace n gs i, ∀ b ∈ trace n gs i, colour a = colour b

def MonoTag {n : ℕ} (colour : Fin n → Bool) (s : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, colour a = colour b

lemma monotag_subset {n : ℕ} {colour : Fin n → Bool} {s t : Finset (Fin n)}
    (h : s ⊆ t) (ht : MonoTag colour t) : MonoTag colour s := by
  intro a ha b hb
  exact ht a (h ha) b (h hb)

lemma tcombine_tag_subset {n : ℕ} (b : Bool) {p q f g : Signal n}
    (hp : p.2 ⊆ f.2) (hq : q.2 ⊆ g.2) :
    (tcombine b p q).2 ⊆ (tcombine b f g).2 := by
  cases b
  · exact Finset.union_subset_union hp hq
  · exact Finset.Subset.refl _

def Pool {n} (F : Test n) (colour : Fin n → Bool) (R : Set (Signal n)) (c : ℕ) : Prop :=
  ∃ gs : List Gate, gs.length ≤ c ∧ Layout n gs ∧ Clean F gs ∧ Tame n colour gs ∧
    ∀ p ∈ R, Dirty F p.1 ∧ ∃ i < n + gs.length, tagged n gs i = p

lemma pool_append {n} {F : Test n} {colour : Fin n → Bool} {R c}
    (h : Pool F colour R c) {p q} (hp : p ∈ R) (hq : q ∈ R) (b : Bool)
    (hd : Dirty F (tcombine b p q).1) (ht : MonoTag colour (tcombine b p q).2) :
    Pool F colour (insert (tcombine b p q) R) (c+1) := by
  classical
  obtain ⟨gs,hc,hl,hcl,hct,hr⟩ := h
  obtain ⟨u,hu,hpu⟩ := (hr p hp).2
  obtain ⟨v,hv,hqv⟩ := (hr q hq).2
  let g := binary b u v
  have hn : tagged n (gs ++ [g]) (n+gs.length) = tcombine b p q := by
    rw [new_tagged, hpu, hqv]
  refine ⟨gs ++ [g], by simp; omega, ?_, ?_, ?_, ?_⟩
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
      change Dirty F (tagged n (gs ++ [g]) (n+gs.length)).1
      rw [hn]
      exact hd
  · intro i hi
    by_cases hj : i < n + gs.length
    · rw [old_trace hj]
      exact hct i hj
    · have : i = n + gs.length := by simp at hi; omega
      subst i
      change MonoTag colour (tagged n (gs ++ [g]) (n+gs.length)).2
      rw [hn]
      exact ht
  · intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact ⟨hd, n+gs.length, by simp, hn⟩
    · obtain ⟨hsd,i,hi,he⟩ := hr s hs
      exact ⟨hsd,i,by simp; omega,(old_tagged hi g).trans he⟩

def Hit {n} (T : Finset (Term n)) (x : Fin n → Bool) : Prop :=
  ∃ t ∈ T, t.1.1 x ∧ t.2.1 x

def Covers {n} (T : Finset (Term n)) (f p : Test n) : Prop :=
  ∀ x, f x → Hit T x ∨ p x

def Repr {n} (R : Set (Signal n)) (P T : Finset (Term n)) (f : Signal n) : Prop :=
  (∃ p ∈ R, (∀ x, p.1 x → f.1 x) ∧ Covers T f.1 p.1 ∧ p.2 ⊆ f.2) ∨
  ∃ t ∈ P, Covers T f.1 (fun x => t.1.1 x ∧ t.2.1 x)

def Sound {n} (F : Test n) (R : Set (Signal n)) (P : Finset (Term n)) : Prop :=
  ∀ t ∈ P, t.1 ∈ R ∧ t.2 ∈ R ∧ ∀ x, t.1.1 x → t.2.1 x → F x

def Model {n} (F : Test n) (colour : Fin n → Bool) (S : Set (Signal n)) (k : ℕ) : Prop :=
  ∃ R P T c, Pool F colour R c ∧ Sound F R P ∧ T ⊆ P ∧
    c + P.card + T.card ≤ k ∧ ∀ f ∈ S, Repr R P T f

lemma hit_mono {n} {T U : Finset (Term n)} (h : T ⊆ U) {x} :
    Hit T x → Hit U x := fun ⟨t,ht,ha⟩ => ⟨t,h ht,ha⟩

lemma repr_mono {n} {R R' : Set (Signal n)} {P P' T T' : Finset (Term n)} {f}
    (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T') (h : Repr R P T f) :
    Repr R' P' T' f := by
  have liftCov {a : Test n} (hc : Covers T f.1 a) : Covers T' f.1 a :=
    fun x hx => (hc x hx).imp (hit_mono ht) id
  rcases h with ⟨p,hm,hl,hc,htag⟩ | ⟨t,hm,hc⟩
  · exact Or.inl ⟨p,hr hm,hl,liftCov hc,htag⟩
  · exact Or.inr ⟨t,hp hm,liftCov hc⟩

lemma combine_comm {n} (b) (f g : Test n) :
    combine b f g = combine b g f := by
  funext x
  cases b <;> simp [combine, and_comm, or_comm]

lemma tcombine_comm {n} (b) (f g : Signal n) :
    tcombine b f g = tcombine b g f := by
  cases b <;> simp [tcombine, combine_comm, Finset.union_comm]

lemma cov_combine {n} {T : Finset (Term n)} {f g p q} (b)
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
    · exact ⟨ha hx.1, hb hx.2⟩

lemma model_add {n} {F : Test n} {colour : Fin n → Bool} {S k}
    (h : Model F colour S k) {f g} (hf : f ∈ S) (hg : g ∈ S) (b)
    (hmono : MonoTag colour (tcombine b f g).2) :
    Model F colour (insert (tcombine b f g) S) (k+1) := by
  classical
  obtain ⟨R,P,T,c,pool,sound,sub,budget,reps⟩ := h
  have finish {s : Signal n} {R' P' T' c'}
      (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T')
      (pl : Pool F colour R' c') (so : Sound F R' P') (su : T' ⊆ P')
      (bu : c'+P'.card+T'.card ≤ k+1) (rep : Repr R' P' T' s) :
      Model F colour (insert s S) (k+1) := by
    refine ⟨R',P',T',c',pl,so,su,bu,?_⟩
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact rep
    · exact repr_mono hr hp ht (reps a ha)
  have virtual {a d : Signal n} {t} (ht : t ∈ P)
      (hc : Covers T a.1 (fun x => t.1.1 x ∧ t.2.1 x)) (hd : Repr R P T d) :
      Model F colour (insert (tcombine b a d) S) (k+1) := by
    cases b
    · let U := insert t T
      have incl : T ⊆ U := Finset.subset_insert t T
      have cover {s : Test n} (cs : Covers T d.1 s) : Covers U (tcombine false a d).1 s := by
        intro x hx
        rcases hx with ha | hd'
        · rcases hc x ha with hh | hh
          · exact Or.inl (hit_mono incl hh)
          · exact Or.inl ⟨t,Finset.mem_insert_self _ _,hh⟩
        · exact (cs x hd').imp (hit_mono incl) id
      apply finish (Set.Subset.rfl) (Finset.Subset.refl _) incl pool sound
        (Finset.insert_subset ht sub) (by have := Finset.card_insert_le t T; dsimp [U]; omega)
      rcases hd with ⟨q,hq,hlo,hcov,htag⟩ | ⟨s,hs,hcov⟩
      · exact Or.inl ⟨q,hq,fun x hx => Or.inr (hlo x hx),cover hcov,
          fun i hi => Finset.mem_union_right a.2 (htag hi)⟩
      · exact Or.inr ⟨s,hs,cover hcov⟩
    · exact finish (Set.Subset.rfl) (Finset.Subset.refl _) (Finset.Subset.refl _) pool sound sub (by omega)
        (Or.inr ⟨t,ht,fun x hx => hc x hx.1⟩)
  have rf := reps f hf
  have rg := reps g hg
  rcases rf with ⟨p,hp,lp,cp,tp⟩ | ⟨t,ht,ct⟩
  · rcases rg with ⟨q,hq,lq,cq,tq⟩ | ⟨t,ht,ct⟩
    · have cov := cov_combine b cp cq
      have tags := tcombine_tag_subset b tp tq
      by_cases dirty : Dirty F (tcombine b p q).1
      · have hr : R ⊆ insert (tcombine b p q) R := Set.subset_insert _ _
        refine finish hr (Finset.Subset.refl _) (Finset.Subset.refl _)
          (pool_append pool hp hq b dirty (monotag_subset tags hmono)) ?_ sub (by omega) ?_
        · intro t ht
          obtain ⟨ha,hb,hf⟩ := sound t ht
          exact ⟨hr ha,hr hb,hf⟩
        · refine Or.inl ⟨tcombine b p q, Set.mem_insert _ _, ?_,cov,tags⟩
          intro x hx
          cases b
          · exact hx.elim (fun h => Or.inl (lp x h)) (fun h => Or.inr (lq x h))
          · exact ⟨lp x hx.1,lq x hx.2⟩
      · cases b
        · obtain ⟨gs,-,-,-,-,hr⟩ := pool
          obtain ⟨x,hx,hn⟩ := (hr p hp).1
          exact (dirty ⟨x, Or.inl hx,hn⟩).elim
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
    · rw [tcombine_comm b f g]
      exact virtual ht ct (Or.inl ⟨p,hp,lp,cp,tp⟩)
  · exact virtual ht ct rg

def Signals (n : ℕ) (gs : List Gate) : Set (Signal n) :=
  {p | ∃ i < n + gs.length, tagged n gs i = p}

lemma simulate {n} (F : Test n) (colour : Fin n → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (gs : List Gate) (hl : Layout n gs) (hcol : Tame n colour gs) :
    Model F colour (Signals n gs) gs.length := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Signals n [], ∅, ∅, 0, ?_, by simp [Sound], by simp, by simp, ?_⟩
    · refine ⟨[],by simp,by simp [Layout],by simp [Clean],hcol,?_⟩
      intro p hp
      obtain ⟨i,hi,rfl⟩ := hp
      exact ⟨inputs i (by simpa using hi), i,hi,rfl⟩
    · intro p hp
      exact Or.inl ⟨p,hp,fun _ => id, fun _ hx => Or.inr hx, Finset.Subset.refl _⟩
  | append_singleton gs last ih =>
    have layout : Layout n gs := by
      intro i hi
      obtain ⟨b,u,v,he,hu,hv⟩ := hl i (by simp; omega)
      exact ⟨b,u,v, (List.getElem_append_left hi).symm.trans he,hu,hv⟩
    have colour_old : Tame n colour gs := by
      intro i hi
      have hh := hcol i (by simp; omega)
      rwa [old_trace hi] at hh
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst last
    have colour_new : MonoTag colour
        (tcombine b (tagged n gs u) (tagged n gs v)).2 := by
      rw [← new_tagged]
      exact hcol (n+gs.length) (by simp)
    have h := model_add (ih layout colour_old)
      (f := tagged n gs u) (g := tagged n gs v)
      ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩ b colour_new
    obtain ⟨R,P,T,c,hp,hs,ht,hb,hr⟩ := h
    refine ⟨R,P,T,c,hp,hs,ht,by simpa using hb,?_⟩
    intro p hm
    obtain ⟨i,hi,rfl⟩ := hm
    by_cases hj : i < n + gs.length
    · rw [old_tagged hj]
      exact hr _ (Set.mem_insert_of_mem _ ⟨i,hj,rfl⟩)
    · have : i = n+gs.length := by simp at hi; omega
      subst i
      rw [new_tagged]
      exact hr _ (Set.mem_insert _ _)

def singleton {n : ℕ} (a : Fin n) (i : Fin n) : Bool := decide (i = a)

def OrOf {n : ℕ} (Q : Finset (Fin n)) : Test n :=
  fun x => ∃ i ∈ Q, x i = true

lemma W_mono {n : ℕ} (gs : List Gate) (h : Layout n gs) (i : ℕ)
    (x y : Fin n → Bool) (hxy : ∀ j, x j = true → y j = true) :
    W n gs i x → W n gs i y := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i < n
    · simpa [W, List.getD, hi] using hxy ⟨i,hi⟩
    · simp [W, List.getD, hi]
  | append_singleton gs g ih =>
    have hp : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := h j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    obtain ⟨b,u,v,he,hu,hv⟩ := h gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst g
    by_cases hi : i < n + gs.length
    · rw [old_wire hi]
      exact ih hp i
    · by_cases hei : i = n + gs.length
      · subst i
        rw [new_wire]
        cases b
        · exact fun hx => hx.elim (fun h => Or.inl (ih hp u h))
            (fun h => Or.inr (ih hp v h))
        · exact fun hx => ⟨ih hp u hx.1,ih hp v hx.2⟩
      · have hl := length_fold (gs ++ [binary b u v]) (List.ofFn x)
        simp only [List.length_ofFn,List.length_append,List.length_singleton] at hl
        have hh : ((gs ++ [binary b u v]).foldl step (List.ofFn x)).length ≤ i := by omega
        simp only [W, List.getD, List.getElem?_eq_none hh, Option.getD_none, Bool.false_eq_true, false_implies]

lemma repr_pure_exact {n : ℕ} {F : Test n} {colour : Fin n → Bool} {R : Set (Signal n)}
    {P T : Finset (Term n)} {c : ℕ} (pool : Pool F colour R c)
    (sound : Sound F R P) (sub : T ⊆ P)
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (Q : Finset (Fin n)) (hQ : Q.Nonempty) {f : Signal n}
    (hf : f.1 = OrOf Q) (rep : Repr R P T f) :
    ∃ p ∈ R, p.1 = OrOf Q := by
  have nohit (a : Fin n) : ¬ Hit T (singleton a) := by
    rintro ⟨t,ht,hp,hq⟩
    exact hsingle a ((sound t (sub ht)).2.2 _ hp hq)
  rcases rep with ⟨p,hp,hlo,hcov,-⟩ | ⟨t,ht,hcov⟩
  · rw [hf] at hlo hcov
    refine ⟨p,hp,?_⟩
    obtain ⟨gs,-,hl,-,-,hr⟩ := pool
    obtain ⟨i,hi,he⟩ := (hr p hp).2
    have he' : W n gs i = p.1 := congrArg Prod.fst he
    funext x
    apply propext
    refine ⟨hlo x,?_⟩
    rintro ⟨a,ha,hxa⟩
    have hs : OrOf Q (singleton a) := ⟨a,ha,by simp [singleton]⟩
    have hpa := (hcov (singleton a) hs).resolve_left (nohit a)
    rw [← he'] at hpa ⊢
    apply W_mono gs hl i (singleton a) x ?_ hpa
    intro j hj
    have : j = a := by simpa [singleton] using hj
    simpa [this] using hxa
  · rw [hf] at hcov
    obtain ⟨a,ha⟩ := hQ
    have hs : OrOf Q (singleton a) := ⟨a,ha,by simp [singleton]⟩
    obtain hh | hh := hcov (singleton a) hs
    · exact (nohit a hh).elim
    · exact (hsingle a ((sound t ht).2.2 _ hh.1 hh.2)).elim

lemma extract_pure {n : ℕ} (F : Test n) (colour : Fin n → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (C : Circuit) (hl : IsAO2 n C) (hcol : Tame n colour C.gates) (hne : ∃ x, F x)
    (ho : W n C.gates C.output = F) :
    ∃ (gs : List Gate) (U : Finset (ℕ × ℕ)), Layout n gs ∧ Clean F gs ∧
      Tame n colour gs ∧
      (∀ t ∈ U, t.1 < n + gs.length ∧ t.2 < n + gs.length) ∧
      (∀ t ∈ U, ∀ x, W n gs t.1 x → W n gs t.2 x → F x) ∧
      (∀ x, F x → ∃ t ∈ U, W n gs t.1 x ∧ W n gs t.2 x) ∧
      gs.length + 2 * U.card ≤ C.size + 1 ∧
      (∀ (Q : Finset (Fin n)), Q.Nonempty →
        (∃ i < n + C.gates.length, W n C.gates i = OrOf Q) →
        ∃ i < n + gs.length, W n gs i = OrOf Q) := by
  classical
  obtain ⟨R,P,T,c,pool,sound,sub,budget,reps⟩ :=
    simulate F colour inputs C.gates (layout_of hl) hcol
  have hout : C.output < n+C.gates.length := by
    by_contra! h
    obtain ⟨x,hx⟩ := hne
    rw [← ho] at hx
    have hlen := length_fold C.gates (List.ofFn x)
    simp only [List.length_ofFn] at hlen
    simp [W, List.getD, List.getElem?_eq_none (hlen ▸ h :
        (C.gates.foldl step (List.ofFn x)).length ≤ C.output)] at hx
  obtain ⟨gs,hc,hg,hclean,hcolour,real⟩ := pool
  have pure (Q : Finset (Fin n)) (hQ : Q.Nonempty)
      (hwire : ∃ i < n + C.gates.length, W n C.gates i = OrOf Q) :
      ∃ i < n + gs.length, W n gs i = OrOf Q := by
    obtain ⟨i,hi,he⟩ := hwire
    obtain ⟨p,hp,hpQ⟩ := repr_pure_exact ⟨gs,hc,hg,hclean,hcolour,real⟩ sound sub hsingle Q hQ he
      (reps _ ⟨i,hi,rfl⟩)
    obtain ⟨j,hj,hp⟩ := (real p hp).2
    exact ⟨j,hj,(congrArg Prod.fst hp).trans hpQ⟩
  have rep := reps (tagged n C.gates C.output) ⟨C.output,hout,rfl⟩
  rcases rep with ⟨p,hp,hlo,-⟩ | ⟨t,ht,hcov⟩
  · obtain ⟨x,hx,hn⟩ := (real p hp).1
    have hf := hlo x hx
    change W n C.gates C.output x at hf
    rw [ho] at hf
    exact (hn hf).elim
  · let U := insert t T
    have hu : U ⊆ P := Finset.insert_subset ht sub
    have cu := Finset.card_le_card hu
    have ct : U.card ≤ T.card + 1 := Finset.card_insert_le t T
    let index (p : Signal n) : ℕ := if hp : p ∈ R then ((real p hp).2).choose else 0
    have idx {p : Signal n} (hp : p ∈ R) : W n gs (index p) = p.1 := by
      have hh : tagged n gs (index p) = p := by
        simpa [index,hp] using ((real p hp).2).choose_spec.2
      exact congrArg Prod.fst hh
    let enc (s : Term n) := (index s.1, index s.2)
    refine ⟨gs,U.image enc,hg,hclean,hcolour,?_,?_,?_,?_,pure⟩
    · intro v hv
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨ha,hb,-⟩ := sound s (hu hs)
      constructor
      · simpa [enc,index,ha] using ((real s.1 ha).2).choose_spec.1
      · simpa [enc,index,hb] using ((real s.2 hb).2).choose_spec.1
    · intro v hv
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨ha,hb,hsafe⟩ := sound s (hu hs)
      simpa only [enc, idx ha, idx hb] using hsafe
    · intro x hx
      have hit : Hit U x := by
        have hx' : (tagged n C.gates C.output).1 x := by
          change W n C.gates C.output x
          rw [ho]
          exact hx
        rcases hcov x hx' with hh | hh
        · exact hit_mono (Finset.subset_insert t T) hh
        · exact ⟨t, Finset.mem_insert_self _ _, hh⟩
      obtain ⟨s,hs,ha,hb⟩ := hit
      obtain ⟨hm,hn,-⟩ := sound s (hu hs)
      exact ⟨enc s,Finset.mem_image_of_mem enc hs, by simpa only [enc,idx hm] using ha,
        by simpa only [enc,idx hn] using hb⟩
    · have h := Finset.card_image_le (s := U) (f := enc)
      unfold Circuit.size
      omega

open PEqualNP.TwoColour

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

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

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

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

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

lemma orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_orIn, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨j, hj, hr, ho, hi⟩)
    · exact Fin.ext he
    · have := hr.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

lemma orIn_invalid (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : orIn n C w = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  rcases (mem_orIn n C w i).mp hi with he | ⟨j, hj, hr, ho, hi⟩
  · have := i.isLt
    omega
  · have := (orReaches_bound n C j w hr).2
    omega

lemma orIn_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    orIn n C (n + j) = @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
      ((gateAt C j).inputs.toFinset.biUnion (orIn n C)) ∅ := by
  classical
  ext a
  rw [mem_orIn]
  by_cases hop : (gateAt C j).op = .or
  · simp only [hop, ↓reduceIte, Finset.mem_biUnion]
    constructor
    · rintro (he | ⟨k, hk, hr, hok, hai⟩)
      · have := a.isLt
        omega
      · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨_, w, hw, hlt, hrw⟩⟩
        · subst k
          exact ⟨a.val, List.mem_toFinset.mpr hai, orIn_self n C a⟩
        · exact ⟨w, List.mem_toFinset.mpr hw,
            (mem_orIn n C w a).mpr (Or.inr ⟨k, hk, hrw, hok, hai⟩)⟩
    · rintro ⟨w, hw, haw⟩
      have hw' := List.mem_toFinset.mp hw
      exact (mem_orIn n C (n+j) a).mp
        (orIn_up n C j w a hj hop hw' (hC j hj w hw') haw)
  · simp only [hop, ↓reduceIte]
    simp only [Finset.notMem_empty, iff_false]
    rintro (he | ⟨k, hk, hr, hok, hai⟩)
    · have := a.isLt
      omega
    · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨ho, _⟩⟩
      · subst k
        exact hop hok
      · exact hop ho

noncomputable def reachFrom {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) : List (Finset (Fin n)) := by
  classical
  exact gs.foldl (fun acc g => acc ++ [if g.op = .or then
    g.inputs.toFinset.biUnion (fun i => acc.getD i ∅) else ∅]) w

noncomputable def reachValues (n : ℕ) (gs : List Gate) : List (Finset (Fin n)) :=
  reachFrom gs (List.ofFn fun i : Fin n => {i})

lemma reachFrom_append {n : ℕ} (gs₁ gs₂ : List Gate) (w : List (Finset (Fin n))) :
    reachFrom (gs₁ ++ gs₂) w = reachFrom gs₂ (reachFrom gs₁ w) := by
  simp [reachFrom, List.foldl_append]

lemma reachFrom_ext {n : ℕ} (gs : List Gate) : ∀ w : List (Finset (Fin n)),
    ∃ t : List (Finset (Fin n)), reachFrom gs w = w ++ t ∧ t.length = gs.length := by
  classical
  induction gs with
  | nil => intro w; exact ⟨[], by simp [reachFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := if g.op = .or then g.inputs.toFinset.biUnion (fun i => w.getD i ∅) else ∅
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : reachFrom (g :: gs) w = reachFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma reachFrom_length {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) :
    (reachFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := reachFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma reachValues_length (n : ℕ) (gs : List Gate) :
    (reachValues n gs).length = n + gs.length := by
  simp [reachValues, reachFrom_length]

lemma reachValues_append (n : ℕ) (gs : List Gate) (g : Gate) :
    reachValues n (gs ++ [g]) = reachValues n gs ++
      [@ite (Finset (Fin n)) (g.op = .or) (Classical.propDecidable _)
        (g.inputs.toFinset.biUnion (fun i => (reachValues n gs).getD i ∅)) ∅] := by
  classical
  simp [reachValues, reachFrom, List.foldl_append]

lemma getD_reachFrom_lt {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (i : ℕ) (hi : i < w.length) :
    (reachFrom gs w).getD i ∅ = w.getD i ∅ := by
  obtain ⟨t, ht, _⟩ := reachFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma getD_reachFrom_take {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (k i : ℕ) (hk : k ≤ gs.length) :
    (reachFrom (gs.take k) w).getD i ∅ =
      if i < w.length + k then (reachFrom gs w).getD i ∅ else ∅ := by
  have hlen : (reachFrom (gs.take k) w).length = w.length + k := by
    rw [reachFrom_length, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, reachFrom_append]
    exact (getD_reachFrom_lt (gs.drop k) (reachFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_reachFrom_gate {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (k : ℕ) (hk : k < gs.length) :
    (reachFrom gs w).getD (w.length + k) ∅ =
      @ite (Finset (Fin n)) ((gs[k]).op = .or) (Classical.propDecidable _)
        ((gs[k]).inputs.toFinset.biUnion (fun i =>
          if i < w.length + k then (reachFrom gs w).getD i ∅ else ∅)) ∅ := by
  classical
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (reachFrom (gs.take k) w).length = w.length + k := by
    rw [reachFrom_length, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  let v := if (gs[k]).op = .or then (gs[k]).inputs.toFinset.biUnion
    (fun i => (reachFrom (gs.take k) w).getD i ∅) else ∅
  have heq : reachFrom gs w = reachFrom (gs.drop (k + 1))
      (reachFrom (gs.take k) w ++ [v]) := by
    conv_lhs => rw [hsplit, reachFrom_append]
    rfl
  rw [heq, getD_reachFrom_lt]
  · rw [← hlen]
    have hs : (reachFrom (gs.take k) w ++ [v]).getD (reachFrom (gs.take k) w).length ∅ = v := by simp
    rw [hs]
    unfold v
    split_ifs with hop
    · apply Finset.biUnion_congr rfl
      intro i hi
      rw [getD_reachFrom_take gs w k i (Nat.le_of_lt hk), heq, hlen]
      simp only [v, hop, ↓reduceIte]
    · rfl
  · rw [List.length_append, hlen]
    simp

lemma reachValues_input (n : ℕ) (gs : List Gate) (w : ℕ) (hw : w < n) :
    (reachValues n gs).getD w ∅ = {⟨w, hw⟩} := by
  unfold reachValues
  rw [getD_reachFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma reachValues_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (reachValues n C.gates).getD (n+j) ∅ =
      @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
        ((gateAt C j).inputs.toFinset.biUnion (fun i => (reachValues n C.gates).getD i ∅)) ∅ := by
  classical
  have he := getD_reachFrom_gate C.gates (List.ofFn fun i : Fin n => {i}) j hj
  simp only [List.length_ofFn] at he
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, hj]
  unfold reachValues
  rw [he, ← hg]
  split_ifs with hop
  · apply Finset.biUnion_congr rfl
    intro i hi
    simp only [hC j hj i (List.mem_toFinset.mp hi), ↓reduceIte]
  · rfl

lemma reachValues_eq_orIn (n : ℕ) (C : Circuit) (hC : ReadsBack n C) :
    ∀ w, (reachValues n C.gates).getD w ∅ = orIn n C w := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hi : w < n
    · rw [reachValues_input n C.gates w hi, orIn_input n C w hi]
    · by_cases hw : w < n + C.gates.length
      · have hj : w-n < C.gates.length := by omega
        have he : n+(w-n) = w := by omega
        rw [← he, reachValues_gate n C hC (w-n) hj, orIn_gate n C hC (w-n) hj]
        split_ifs with hop
        · apply Finset.biUnion_congr rfl
          intro i hmem
          exact ih i (by have := hC (w-n) hj i (List.mem_toFinset.mp hmem); omega)
        · rfl
      · rw [List.getD_eq_default _ _ (by rw [reachValues_length]; omega),
          orIn_invalid n C w (by omega)]

lemma tCount_zero_iff_gate (n : ℕ) (C : Circuit) (lin : ℕ → Bool) :
    tCount n C lin = 0 ↔ ∀ j < C.gates.length, (gateAt C j).op = .or →
      ∀ a ∈ orIn n C (n+j), ∀ b ∈ orIn n C (n+j), lin a.val = lin b.val := by
  classical
  rw [tCount, Finset.card_eq_zero]
  constructor
  · intro hz j hj hop a ha b hb
    by_contra hne
    have hm : (∃ i ∈ orIn n C (n+j), lin i.val = false) ∧
        (∃ i ∈ orIn n C (n+j), lin i.val = true) := by
      cases hla : lin a.val <;> cases hlb : lin b.val
      · exact (hne (hla.trans hlb.symm)).elim
      · exact ⟨⟨a,ha,hla⟩,⟨b,hb,hlb⟩⟩
      · exact ⟨⟨b,hb,hlb⟩,⟨a,ha,hla⟩⟩
      · exact (hne (hla.trans hlb.symm)).elim
    have hmem : j ∈ twoColour n C lin :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, hop, hm⟩
    rw [hz] at hmem
    exact Finset.notMem_empty j hmem
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro j hj
    obtain ⟨_, hj', hop, ⟨a,ha,hla⟩, ⟨b,hb,hlb⟩⟩ := Finset.mem_filter.mp hj
    have he := h j hj' hop a ha b hb
    rw [hla, hlb] at he
    cases he

lemma tCount_zero_all_wires (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) (hT : tCount n C lin = 0) :
    ∀ w, ∀ a ∈ orIn n C w, ∀ b ∈ orIn n C w, lin a.val = lin b.val := by
  classical
  intro w a ha b hb
  by_cases hw : w < n
  · rw [orIn_input n C w hw, Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · by_cases hv : w < n+C.gates.length
    · have hj : w-n < C.gates.length := by omega
      have he : n+(w-n) = w := by omega
      by_cases hop : (gateAt C (w-n)).op = .or
      · exact (tCount_zero_iff_gate n C lin).mp hT (w-n) hj hop a
          (by simpa [he] using ha) b (by simpa [he] using hb)
      · have hempty : orIn n C w = ∅ := by
          rw [← he, orIn_gate n C hC (w-n) hj]
          simp only [hop, ↓reduceIte]
        rw [hempty] at ha
        exact (Finset.notMem_empty a ha).elim
    · rw [orIn_invalid n C w (by omega)] at ha
      exact (Finset.notMem_empty a ha).elim

lemma tCount_zero_iff_reachValues (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) :
    tCount n C lin = 0 ↔ ∀ w, ∀ a ∈ (reachValues n C.gates).getD w ∅,
      ∀ b ∈ (reachValues n C.gates).getD w ∅, lin a.val = lin b.val := by
  simp only [reachValues_eq_orIn n C hC]
  constructor
  · exact tCount_zero_all_wires n C lin hC
  · intro h
    exact (tCount_zero_iff_gate n C lin).mpr (fun j hj hop => h (n+j))


lemma trace_fold_eq_reachValues {n : ℕ} {gs : List Gate} (hl : Layout n gs) :
    gs.foldl traceStep (List.ofFn fun j : Fin n => {j}) = reachValues n gs := by
  classical
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    have hp : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := hl j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst g
    rw [List.foldl_append, ih hp, reachValues_append]
    cases b <;> simp [traceStep,binary]

lemma trace_eq_orIn {n : ℕ} (C : Circuit) (hl : IsAO2 n C) (i : ℕ) :
    trace n C.gates i = orIn n C i := by
  rw [trace, trace_fold_eq_reachValues (layout_of hl)]
  exact reachValues_eq_orIn n C hl.2.1 i

lemma tame_iff_tCount_zero {n : ℕ} (C : Circuit) (hl : IsAO2 n C) (lin : ℕ → Bool) :
    Tame n (fun i => lin i.val) C.gates ↔ tCount n C lin = 0 := by
  constructor
  · intro ht
    apply (tCount_zero_iff_gate n C lin).mpr
    intro j hj hop a ha b hb
    rw [← trace_eq_orIn C hl] at ha hb
    exact ht (n+j) (by omega) a ha b hb
  · intro ht i hi a ha b hb
    rw [trace_eq_orIn C hl] at ha hb
    exact tCount_zero_all_wires n C lin hl.2.1 ht i a ha b hb

lemma extract_pure_official {n : ℕ} (F : Test n) (lin : ℕ → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (C : Circuit) (hl : IsAO2 n C) (hcol : tCount n C lin = 0)
    (hne : ∃ x, F x) (ho : W n C.gates C.output = F) :
    ∃ (D : Circuit) (U : Finset (ℕ × ℕ)), IsAO2 n D ∧
      tCount n D lin = 0 ∧ Clean F D.gates ∧
      (∀ t ∈ U, t.1 < n + D.gates.length ∧ t.2 < n + D.gates.length) ∧
      (∀ t ∈ U, ∀ x, W n D.gates t.1 x → W n D.gates t.2 x → F x) ∧
      (∀ x, F x → ∃ t ∈ U, W n D.gates t.1 x ∧ W n D.gates t.2 x) ∧
      D.size + 2 * U.card ≤ C.size + 1 ∧
      (∀ (Q : Finset (Fin n)), Q.Nonempty →
        (∃ i < n + C.gates.length, W n C.gates i = OrOf Q) →
        ∃ i < n + D.gates.length, W n D.gates i = OrOf Q) := by
  obtain ⟨gs,U,hg,hclean,ht,hb,hs,hcov,hsize,hpure⟩ :=
    extract_pure F (fun i => lin i.val) inputs hsingle C hl
      ((tame_iff_tCount_zero C hl lin).mpr hcol) hne ho
  have hD := layout_ao hg
  exact ⟨⟨gs,0⟩,U,hD,(tame_iff_tCount_zero ⟨gs,0⟩ hD lin).mp ht,
    hclean,hb,hs,hcov,hsize,hpure⟩

end H8Tagged


namespace H8Assembly

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4970.H8Tagged

lemma old_wire_append {n : ℕ} (gs hs : List Gate) {i : ℕ}
    (hi : i < n + gs.length) : W n (gs ++ hs) i = W n gs i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, old_wire (by simp; omega), ih]

lemma old_trace_append {n : ℕ} (gs hs : List Gate) {i : ℕ}
    (hi : i < n + gs.length) : trace n (gs ++ hs) i = trace n gs i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, old_trace (by simp; omega), ih]

lemma layout_append_binary {n : ℕ} {gs : List Gate} (hl : Layout n gs)
    (b : Bool) (u v : ℕ) (hu : u < n + gs.length) (hv : v < n + gs.length) :
    Layout n (gs ++ [binary b u v]) := by
  intro i hi
  by_cases hj : i < gs.length
  · obtain ⟨b',u',v',he,hu',hv'⟩ := hl i hj
    exact ⟨b',u',v',by simpa [List.getElem_append_left hj] using he,hu',hv'⟩
  · have hei : i = gs.length := by simp at hi; omega
    subst i
    exact ⟨b,u,v,by simp,hu,hv⟩

lemma tame_append_binary {n : ℕ} {colour : Fin n → Bool} {gs : List Gate}
    (ht : Tame n colour gs) (b : Bool) (u v : ℕ)
    (hm : MonoTag colour (if b then ∅ else trace n gs u ∪ trace n gs v)) :
    Tame n colour (gs ++ [binary b u v]) := by
  intro i hi
  by_cases hj : i < n + gs.length
  · rw [old_trace hj]
    exact ht i hj
  · have hei : i = n + gs.length := by simp at hi; omega
    subst i
    rw [new_trace]
    exact hm

def AndBound (n k : ℕ) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), gs[i].op = .and → ∀ w ∈ gs[i].inputs, w < n + k

lemma andBound_base {n : ℕ} {gs : List Gate} (hl : Layout n gs) :
    AndBound n gs.length gs := by
  intro i hi hop w hw
  obtain ⟨b,u,v,he,hu,hv⟩ := hl i hi
  rw [he] at hw
  simp [binary] at hw
  rcases hw with rfl | rfl <;> omega

lemma andBound_append {n k : ℕ} {gs : List Gate} (hb : AndBound n k gs)
    (b : Bool) (u v : ℕ) (hnew : b = true → u < n+k ∧ v < n+k) :
    AndBound n k (gs ++ [binary b u v]) := by
  intro i hi hop w hw
  by_cases hj : i < gs.length
  · exact hb i hj (by simpa [List.getElem_append_left hj] using hop) w
      (by simpa [List.getElem_append_left hj] using hw)
  · have hei : i = gs.length := by simp at hi; omega
    subst i
    have hbtrue : b = true := by cases b <;> simp_all [binary]
    obtain ⟨hu,hv⟩ := hnew hbtrue
    simp [binary] at hw
    rcases hw with rfl | rfl <;> assumption

lemma mono_empty {n : ℕ} (colour : Fin n → Bool) : MonoTag colour ∅ := by
  simp [MonoTag]

lemma assemble_nonempty {n : ℕ} (colour : Fin n → Bool) (gs : List Gate)
    (hl : Layout n gs) (ht : Tame n colour gs)
    (us : List (ℕ × ℕ)) (hne : us ≠ [])
    (hb : ∀ p ∈ us, p.1 < n+gs.length ∧ p.2 < n+gs.length) :
    ∃ (hs : List Gate) (out : ℕ), gs.IsPrefix hs ∧
      hs.length + 1 = gs.length + 2 * us.length ∧ Layout n hs ∧ Tame n colour hs ∧
      out < n+hs.length ∧ trace n hs out = ∅ ∧ AndBound n gs.length hs ∧
      (∀ x, W n hs out x ↔ ∃ p ∈ us, W n gs p.1 x ∧ W n gs p.2 x) := by
  induction us with
  | nil => exact (hne rfl).elim
  | cons p ps ih =>
    have hp := hb p (by simp)
    by_cases hz : ps = []
    · subst ps
      let g := binary true p.1 p.2
      refine ⟨gs ++ [g],n+gs.length,⟨[g],rfl⟩,by simp,?_,?_,by simp,?_,?_,?_⟩
      · exact layout_append_binary hl true p.1 p.2 hp.1 hp.2
      · exact tame_append_binary ht true p.1 p.2 (mono_empty colour)
      · exact new_trace n gs true p.1 p.2
      · exact andBound_append (andBound_base hl) true p.1 p.2 (fun _ => hp)
      · intro x
        rw [new_wire]
        simp [combine]
    · obtain ⟨hs,o,hprefix,hlen,hhl,hht,ho,hto,hab,hsem⟩ :=
        ih hz (fun q hq => hb q (by simp [hq]))
      obtain ⟨suffix,hs_eq⟩ := hprefix
      have hgslen : gs.length ≤ hs.length := by rw [← hs_eq]; simp
      have hpu : p.1 < n+hs.length := by omega
      have hpv : p.2 < n+hs.length := by omega
      let prod := binary true p.1 p.2
      let mid := hs ++ [prod]
      let join := binary false o (n+hs.length)
      have hlmid : Layout n mid := layout_append_binary hhl true p.1 p.2 hpu hpv
      have htmid : Tame n colour mid := tame_append_binary hht true p.1 p.2 (mono_empty colour)
      have homid : o < n+mid.length := by simp [mid]; omega
      have hpmid : n+hs.length < n+mid.length := by simp [mid]
      have tr_o : trace n mid o = ∅ := by rw [old_trace ho]; exact hto
      have tr_p : trace n mid (n+hs.length) = ∅ := new_trace n hs true p.1 p.2
      refine ⟨mid ++ [join],n+mid.length,?_,?_,?_,?_,by simp,?_,?_,?_⟩
      · refine ⟨suffix ++ [prod,join],?_⟩
        simp [mid,← hs_eq,List.append_assoc]
      · simp only [List.length_append,List.length_cons]
        dsimp [mid]
        simp only [List.length_append,List.length_singleton]
        omega
      · exact layout_append_binary hlmid false o (n+hs.length) homid hpmid
      · apply tame_append_binary htmid false o (n+hs.length)
        simpa [tr_o,tr_p] using mono_empty colour
      · rw [new_trace]
        simp [tr_o,tr_p]
      · exact andBound_append (andBound_append hab true p.1 p.2 (fun _ => hp))
          false o (n+hs.length) (by simp)
      · intro x
        rw [new_wire]
        change (W n mid o x ∨ W n mid (n+hs.length) x) ↔ _
        rw [old_wire ho,new_wire,hsem]
        have hpu_old : W n hs p.1 = W n gs p.1 := by
          rw [← hs_eq]; exact old_wire_append gs suffix hp.1
        have hpv_old : W n hs p.2 = W n gs p.2 := by
          rw [← hs_eq]; exact old_wire_append gs suffix hp.2
        simp only [combine,hpu_old,hpv_old]
        simp [or_comm]

lemma normalize_preserving {n : ℕ} (F : Test n) (lin : ℕ → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hcol : PEqualNP.TwoColour.tCount n C lin = 0)
    (hne : ∃ x, F x) (ho : W n C.gates C.output = F) :
    ∃ (D : Circuit) (k : ℕ), D.size ≤ C.size ∧ PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.TwoColour.tCount n D lin = 0 ∧ W n D.gates D.output = F ∧
      AndBound n k D.gates ∧
      (∀ i (hi : i < D.gates.length), i < k → D.gates[i].op = .and →
        Dirty F (W n D.gates (n+i))) ∧
      (∀ (Q : Finset (Fin n)), Q.Nonempty →
        (∃ i < n + C.gates.length, W n C.gates i = OrOf Q) →
        ∃ i < n + D.gates.length, W n D.gates i = OrOf Q) := by
  classical
  obtain ⟨base,U,hbase,htbase,hclean,hb,hsafe,hcover,hsize,hpure⟩ :=
    extract_pure_official F lin inputs hsingle C hC hcol hne ho
  have hU : U.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨p,hp,-⟩ := hcover x hx
    exact ⟨p,hp⟩
  have hlist : U.toList ≠ [] := by simpa using hU.ne_empty
  obtain ⟨gs,out,hprefix,hlen,hl,ht,hout,htrace,hand,hfun⟩ :=
    assemble_nonempty (fun i : Fin n => lin i.val) base.gates (layout_of hbase)
      ((tame_iff_tCount_zero base hbase lin).mpr htbase) U.toList hlist
      (by simpa using hb)
  obtain ⟨suffix,hsuffix⟩ := hprefix
  have hbaselen : base.gates.length ≤ gs.length := by rw [← hsuffix]; simp
  have hD : PEqualNP.TopForm.IsAO2 n (⟨gs,out⟩ : Circuit) := layout_ao hl
  refine ⟨⟨gs,out⟩,base.gates.length,?_,hD,?_,?_,hand,?_,?_⟩
  · simp only [Finset.length_toList] at hlen
    change gs.length ≤ C.size
    change base.gates.length + 2 * U.card ≤ C.size + 1 at hsize
    omega
  · exact (tame_iff_tCount_zero ⟨gs,out⟩ hD lin).mp ht
  · funext x
    apply propext
    rw [hfun]
    constructor
    · rintro ⟨p,hp,h1,h2⟩
      exact hsafe p (by simpa using hp) x h1 h2
    · intro hx
      obtain ⟨p,hp,h1,h2⟩ := hcover x hx
      exact ⟨p,by simpa using hp,h1,h2⟩
  · intro i hi hik hop
    change i < gs.length at hi
    have hopbase : base.gates[i].op = .and := by
      simpa [← hsuffix,List.getElem_append_left hik] using hop
    have hd := hclean i hik hopbase
    change Dirty F (W n gs (n+i))
    rw [← hsuffix,old_wire_append base.gates suffix (by omega)]
    exact hd
  · intro Q hQ hQold
    obtain ⟨i,hi,he⟩ := hpure Q hQ hQold
    refine ⟨i,by change i < n+gs.length; omega,?_⟩
    change W n gs i = OrOf Q
    rw [← hsuffix,old_wire_append base.gates suffix hi]
    exact he

end H8Assembly


namespace H8TopBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl


lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
    intro k hk
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      gateAt_eq_getElem C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ}
    (hj : j < C.gates.length) (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w, _, hn, hw, he | he⟩ := (inCone_iff n C i j hj).mp h
    · omega
    · have hwj : w - n < j := by omega
      have hi := ih (w - n) hwj (by omega) he
      omega

lemma inCone_before_cutoff {n k : ℕ} {C : Circuit} {i j : ℕ}
    (hj : j < C.gates.length)
    (hinputs : ∀ w ∈ (gateAt C j).inputs, w < n + k)
    (h : InCone n C i j) : i < k := by
  obtain ⟨w, hwmem, hn, hw, he | he⟩ := (inCone_iff n C i j hj).mp h
  · have hk := hinputs w hwmem
    omega
  · have hk := hinputs w hwmem
    have hi := inCone_lt (by omega : w - n < C.gates.length) he
    omega

lemma safe_and_no_and_cone {n k : ℕ} {C : Circuit}
    (F : (Fin n → Bool) → Prop)
    (hinputs : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, w < n + k)
    (hdirty : ∀ i < C.gates.length, i < k → (gateAt C i).op = GateOp.and →
      ∃ x : Fin n → Bool, gateVal n C i x = true ∧ ¬ F x) :
    ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and →
      (∀ x : Fin n → Bool, gateVal n C i x = true → F x) →
      (gateAt C j).op = GateOp.and → ¬ InCone n C i j := by
  intro i hi j hj hai hsafe haj hcone
  have hik : i < k := inCone_before_cutoff hj (hinputs j hj haj) hcone
  obtain ⟨x, hx, hnot⟩ := hdirty i hi hik hai
  exact hnot (hsafe x hx)

end H8TopBridge

namespace H8Normalization

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.H8Tagged
  PEqualNP.Outside.L_meta_4970.H8Assembly
  PEqualNP.Outside.L_meta_4970.H8TopBridge

lemma normalize_top_preserving {n : ℕ} (F : Test n) (lin : ℕ → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (C : Circuit) (hC : IsAO2 n C)
    (hcol : PEqualNP.TwoColour.tCount n C lin = 0)
    (hne : ∃ x, F x) (ho : W n C.gates C.output = F) :
    ∃ D : Circuit, D.size ≤ C.size ∧ IsAO2 n D ∧
      PEqualNP.TwoColour.tCount n D lin = 0 ∧ W n D.gates D.output = F ∧
      (∀ i < D.gates.length, ∀ j < D.gates.length,
        (gateAt D i).op = .and →
        (∀ x : Fin n → Bool, gateVal n D i x = true → F x) →
        (gateAt D j).op = .and → ¬ InCone n D i j) ∧
      (∀ (Q : Finset (Fin n)), Q.Nonempty →
        (∃ i < n + C.gates.length, W n C.gates i = OrOf Q) →
        ∃ i < n + D.gates.length, W n D.gates i = OrOf Q) := by
  obtain ⟨D,k,hsize,hD,ht,hF,hbound,hdirty,hpure⟩ :=
    normalize_preserving F lin inputs hsingle C hC hcol hne ho
  refine ⟨D,hsize,hD,ht,hF,?_,hpure⟩
  apply safe_and_no_and_cone F
  · intro j hj hop w hw
    rw [gateAt_eq_getElem D j hj] at hop hw
    exact hbound j hj hop w hw
  · intro i hi hik hop
    rw [gateAt_eq_getElem D i hi] at hop
    exact hdirty i hi hik hop

end H8Normalization


namespace H8Roots

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4970.H8Tagged

lemma factor_eq_or {n : ℕ} (Q : Finset (Fin n)) (f : Test n)
    (hm : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → f x → f y)
    (hz : ¬ f (fun i => decide (i ∉ Q)))
    (hc : ∀ x, OrOf Q x → f x) : f = OrOf Q := by
  classical
  funext x
  apply propext
  refine ⟨?_,hc x⟩
  intro hx
  by_contra hn
  apply hz
  apply hm x _ ?_ hx
  intro i hi
  by_cases hq : i ∈ Q
  · exact (hn ⟨i,hq,hi⟩).elim
  · simp [hq]

lemma and_eq_or {n : ℕ} (Q : Finset (Fin n)) (f g : Test n)
    (hf : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → f x → f y)
    (hg : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → g x → g y)
    (he : combine true f g = OrOf Q) : f = OrOf Q ∨ g = OrOf Q := by
  classical
  have hc (x) (hx : OrOf Q x) : f x ∧ g x := by
    change combine true f g x
    rw [he]
    exact hx
  have hz : ¬ (f (fun i => decide (i ∉ Q)) ∧ g (fun i => decide (i ∉ Q))) := by
    change ¬ combine true f g (fun i => decide (i ∉ Q))
    rw [he]
    simp [OrOf]
  rcases not_and_or.mp hz with hz | hz
  · exact Or.inl (factor_eq_or Q f hf hz fun x hx => (hc x hx).1)
  · exact Or.inr (factor_eq_or Q g hg hz fun x hx => (hc x hx).2)

lemma pure_or_root {n : ℕ} (gs : List Gate) (hl : Layout n gs)
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (hw : ∃ i < n + gs.length, W n gs i = OrOf Q) :
    ∃ (j : ℕ) (hj : j < gs.length), gs[j].op = .or ∧ W n gs (n+j) = OrOf Q := by
  induction gs using List.reverseRecOn with
  | nil =>
    obtain ⟨i,hi,he⟩ := hw
    have hi' : i < n := by simpa using hi
    have hsub : Q ⊆ {⟨i,hi'⟩} := by
      intro a ha
      have hx : W n [] i (H8Tagged.singleton a) := by
        rw [he]
        exact ⟨a,ha,by simp [H8Tagged.singleton]⟩
      have heq : (⟨i,hi'⟩ : Fin n) = a := by
        simpa [W,List.getD,hi',H8Tagged.singleton] using hx
      simp [← heq]
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega
  | append_singleton gs last ih =>
    have hp : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := hl j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    have liftRoot (hr : ∃ (j : ℕ) (hj : j < gs.length), gs[j].op = .or ∧ W n gs (n+j) = OrOf Q) :
        ∃ (j : ℕ) (hj : j < (gs ++ [last]).length), (gs ++ [last])[j].op = .or ∧
          W n (gs ++ [last]) (n+j) = OrOf Q := by
      obtain ⟨j,hj,hop,hjQ⟩ := hr
      refine ⟨j,by simp; omega,?_,?_⟩
      · simpa [List.getElem_append_left hj] using hop
      · rw [old_wire (by omega)]
        exact hjQ
    obtain ⟨i,hi,hiQ⟩ := hw
    by_cases hold : i < n + gs.length
    · apply liftRoot
      apply ih hp
      exact ⟨i,hold,(old_wire hold last).symm.trans hiQ⟩
    · have hei : i = n + gs.length := by simp at hi; omega
      subst i
      obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
      simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
        List.getElem_cons_zero] at he
      subst last
      cases b
      · exact ⟨gs.length,by simp,by simp [binary],hiQ⟩
      · rw [new_wire] at hiQ
        have hfactor := and_eq_or Q (W n gs u) (W n gs v)
          (fun x y hxy => W_mono gs hp u x y hxy)
          (fun x y hxy => W_mono gs hp v x y hxy) hiQ
        apply liftRoot
        apply ih hp
        rcases hfactor with he | he
        · exact ⟨u,hu,he⟩
        · exact ⟨v,hv,he⟩


def served (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ (a : Fin p) (b : Fin l), (a,b) ∈ E →
    (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a,b') ∈ E) ∧
      ∀ x : Fin (p+l) → Bool, (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
    (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a',b) ∈ E) ∧
      ∀ x : Fin (p+l) → Bool, (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))


lemma preserves_pure_served {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C D : Circuit) (hD : PEqualNP.TopForm.IsAO2 (p+l) D)
    (hpure : ∀ (Q : Finset (Fin (p+l))), Q.Nonempty →
      (∃ i < p+l+C.gates.length, W (p+l) C.gates i = OrOf Q) →
      ∃ i < p+l+D.gates.length, W (p+l) D.gates i = OrOf Q)
    (hs : served p l E C) : served p l E D := by
  classical
  intro a b hab
  rcases hs a b hab with ⟨j,Q,hj,hop,hQ,hb,hsub,hval⟩ | ⟨j,P,hj,hop,hP,ha,hsub,hval⟩
  · left
    have hinj : Function.Injective (Fin.natAdd p : Fin l → Fin (p+l)) := by
      intro b b' h
      apply Fin.ext
      have hh := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hh
      omega
    let Q' := Q.image (Fin.natAdd p)
    have hc : 2 ≤ Q'.card := by rw [Finset.card_image_of_injective _ hinj]; exact hQ
    have hnon : Q'.Nonempty := Finset.card_pos.mp (by omega)
    have hwire : W (p+l) C.gates (p+l+j) = OrOf Q' := by
      funext x
      change ((C.wires (List.ofFn x)).getD (p+l+j) false = true) = _
      rw [hval x]
      simp [OrOf,Q']
    obtain ⟨k,hk,hkop,hkval⟩ := pure_or_root D.gates (layout_of hD) Q' hc
      (hpure Q' hnon ⟨p+l+j,by omega,hwire⟩)
    refine ⟨k,Q,hk,?_,hQ,hb,hsub,?_⟩
    · simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD,hk] using hkop
    · intro x
      have hh := congrFun hkval x
      change ((D.wires (List.ofFn x)).getD (p+l+k) false = true) = OrOf Q' x at hh
      have hh' := congrArg (fun P : Prop => decide P) hh
      simpa [OrOf,Q'] using hh'
  · right
    have hinj : Function.Injective (Fin.castAdd l : Fin p → Fin (p+l)) := by
      intro a a' h
      apply Fin.ext
      have hh := congrArg (fun i : Fin (p+l) => i.val) h
      simpa using hh
    let P' := P.image (Fin.castAdd l)
    have hc : 2 ≤ P'.card := by rw [Finset.card_image_of_injective _ hinj]; exact hP
    have hnon : P'.Nonempty := Finset.card_pos.mp (by omega)
    have hwire : W (p+l) C.gates (p+l+j) = OrOf P' := by
      funext x
      change ((C.wires (List.ofFn x)).getD (p+l+j) false = true) = _
      rw [hval x]
      simp [OrOf,P']
    obtain ⟨k,hk,hkop,hkval⟩ := pure_or_root D.gates (layout_of hD) P' hc
      (hpure P' hnon ⟨p+l+j,by omega,hwire⟩)
    refine ⟨k,P,hk,?_,hP,ha,hsub,?_⟩
    · simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD,hk] using hkop
    · intro x
      have hh := congrFun hkval x
      change ((D.wires (List.ofFn x)).getD (p+l+k) false = true) = OrOf P' x at hh
      have hh' := congrArg (fun P : Prop => decide P) hh
      simpa [OrOf,P'] using hh'

end H8Roots

namespace H8Posted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4970.H8Tagged
  PEqualNP.Outside.L_meta_4970.H8Normalization
  PEqualNP.Outside.L_meta_4970.H8Roots

def edgeTest {p l : ℕ} (E : Finset (Fin p × Fin l)) : Test (p+l) :=
  fun x => ∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true

lemma edge_singleton_false {p l : ℕ} (E : Finset (Fin p × Fin l))
    (i : Fin (p+l)) : ¬ edgeTest E (singleton i) := by
  rintro ⟨a,b,-,ha,hb⟩
  simp only [PEqualNP.Outside.L_meta_4970.H8Tagged.singleton,decide_eq_true_eq] at ha hb
  have hva := congrArg Fin.val ha
  have hvb := congrArg Fin.val hb
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hva hvb
  have := a.isLt
  omega

lemma input_dirty_of_singleton_false {n : ℕ} (F : Test n)
    (hsingle : ∀ a : Fin n, ¬ F (singleton a)) (i : ℕ) (hi : i < n) :
    Dirty F (W n [] i) := by
  exact ⟨singleton ⟨i,hi⟩,by simp [W,List.getD,hi,PEqualNP.Outside.L_meta_4970.H8Tagged.singleton],hsingle ⟨i,hi⟩⟩

def computes {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ x : Fin (p+l) → Bool, circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
    x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

lemma bipartite_normalize_top {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : IsAO2 (p+l) C)
    (hcomp : computes E C) (hT : tCount (p+l) C (fun i => decide (p ≤ i)) = 0)
    (hserved : served p l E C) :
    ∃ D : Circuit, D.size ≤ C.size ∧ IsAO2 (p+l) D ∧ computes E D ∧
      tCount (p+l) D (fun i => decide (p ≤ i)) = 0 ∧ served p l E D ∧
      (∀ i < D.gates.length, ∀ j < D.gates.length,
        (gateAt D i).op = .and →
        (∀ x : Fin (p+l) → Bool, gateVal (p+l) D i x = true → edgeTest E x) →
        (gateAt D j).op = .and → ¬ InCone (p+l) D i j) := by
  have hne : ∃ x, edgeTest E x := by
    obtain ⟨⟨a,b⟩,he⟩ := hE
    exact ⟨fun _ => true,a,b,he,rfl,rfl⟩
  have ho : W (p+l) C.gates C.output = edgeTest E := by
    funext x
    change (circuitFun (p+l) C x = true) = edgeTest E x
    rw [hcomp x]
    simp [edgeTest]
  obtain ⟨D,hsize,hD,hTD,hFD,htop,hpure⟩ :=
    normalize_top_preserving (edgeTest E) (fun i => decide (p ≤ i))
      (input_dirty_of_singleton_false (edgeTest E) (edge_singleton_false E))
      (edge_singleton_false E) C hC hT hne ho
  refine ⟨D,hsize,hD,?_,hTD,preserves_pure_served E C D hD hpure hserved,htop⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change W (p+l) D.gates D.output x ↔ edgeTest E x
  rw [hFD]

end H8Posted


namespace H8Cut

def singleton {α : Type*} [DecidableEq α] (i : α) : α → Bool :=
  fun j => decide (j = i)

def disjunction {α : Type*} [DecidableEq α] (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∃ i ∈ Q, x i = true)

lemma singleton_le {α : Type*} [DecidableEq α] {i : α} {x : α → Bool}
    (hi : x i = true) : singleton i ≤ x := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [singleton, hi]
  · simp [singleton, hji]

lemma disjunction_singleton {α : Type*} [DecidableEq α] (Q : Finset α) (i : α) :
    disjunction Q (singleton i) = decide (i ∈ Q) := by
  simp [disjunction, singleton]

lemma pure_disjunction_preserved {α : Type*} [DecidableEq α]
    (Q : Finset α) (f f' : (α → Bool) → Bool)
    (hmono : Monotone f') (hle : ∀ x, f' x ≤ f x)
    (hsingle : ∀ i, f' (singleton i) = f (singleton i))
    (hpure : ∀ x, f x = disjunction Q x) :
    ∀ x, f' x = disjunction Q x := by
  intro x
  apply le_antisymm
  · simpa only [hpure x] using hle x
  · cases hx : disjunction Q x with
    | false => simp
    | true =>
        have hx' : ∃ i ∈ Q, x i = true := by
          simpa only [disjunction, decide_eq_true_eq] using hx
        obtain ⟨i, hi, hxi⟩ := hx'
        have hs : f' (singleton i) = true := by
          rw [hsingle i, hpure, disjunction_singleton]
          simp only [hi, decide_true]
        have hm := hmono (singleton_le hxi)
        simpa only [hs] using hm

lemma safe_cut_lift {α : Type*} (F F' g : α → Bool)
    (hmatch : ∀ x, g x = false → F' x = F x)
    (hsafe : ∀ x, g x = true → F x = true) :
    ∀ x, (F' x || g x) = F x := by
  intro x
  cases hg : g x with
  | false => simpa only [Bool.or_false] using hmatch x hg
  | true => simp only [Bool.or_true, hsafe x hg]

lemma context_cut_le {α : Type*} (H : α → Bool → Bool) (h : α → Bool)
    (hmono : ∀ x, Monotone (H x)) :
    ∀ x, H x false ≤ H x (h x) := by
  intro x
  exact hmono x (by cases h x <;> decide)

lemma safe_and_cut_lift {α : Type*}
    (H : α → Bool → Bool) (g r : α → Bool)
    (hsafe : ∀ x, g x = true → H x (g x && r x) = true) :
    ∀ x, (H x false || g x) = H x (g x && r x) := by
  apply safe_cut_lift (fun x => H x (g x && r x)) (fun x => H x false) g
  · intro x hg
    simp only [hg, Bool.false_and]
  · exact hsafe

lemma pure_disjunction_context_cut {α : Type*} [DecidableEq α]
    (Q : Finset α) (H : (α → Bool) → Bool → Bool) (h : (α → Bool) → Bool)
    (hxmono : Monotone (fun x => H x false))
    (hzmono : ∀ x, Monotone (H x))
    (hsingle : ∀ i, h (singleton i) = false)
    (hpure : ∀ x, H x (h x) = disjunction Q x) :
    ∀ x, H x false = disjunction Q x := by
  apply pure_disjunction_preserved Q (fun x => H x (h x)) (fun x => H x false)
    hxmono (context_cut_le H h hzmono)
  · intro i
    rw [hsingle i]
  · exact hpure

lemma safe_false_on_singletons {α : Type*} [DecidableEq α]
    (F g : (α → Bool) → Bool)
    (hsafe : ∀ x, g x = true → F x = true)
    (hF : ∀ i, F (singleton i) = false) :
    ∀ i, g (singleton i) = false := by
  intro i
  cases hg : g (singleton i) with
  | false => rfl
  | true =>
      have hf := hsafe (singleton i) hg
      rw [hF i] at hf
      cases hf

lemma safe_and_preserves_pure_disjunction {α : Type*} [DecidableEq α]
    (Q : Finset α) (F g r : (α → Bool) → Bool)
    (H : (α → Bool) → Bool → Bool)
    (hsafe : ∀ x, g x = true → F x = true)
    (hF : ∀ i, F (singleton i) = false)
    (hxmono : Monotone (fun x => H x false))
    (hzmono : ∀ x, Monotone (H x))
    (hpure : ∀ x, H x (g x && r x) = disjunction Q x) :
    ∀ x, H x false = disjunction Q x := by
  apply pure_disjunction_context_cut Q H (fun x => g x && r x) hxmono hzmono
  · intro i
    rw [safe_false_on_singletons F g hsafe hF i]
    rfl
  · exact hpure

end H8Cut



namespace H8TaggedCounts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev Test (n : ℕ) := (Fin n → Bool) → Prop
abbrev Signal (n : ℕ) := Test n × Finset (Fin n)
abbrev Term (n : ℕ) := Signal n × Signal n

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

def traceStep {n : ℕ} (w : List (Finset (Fin n))) (g : Gate) : List (Finset (Fin n)) :=
  w ++ [match g.op with
    | .or => (g.inputs.map fun i => w.getD i ∅).foldl (fun (a b : Finset (Fin n)) => a ∪ b) ∅
    | _ => ∅]

def trace (n : ℕ) (gs : List Gate) (i : ℕ) : Finset (Fin n) :=
  (gs.foldl traceStep (List.ofFn fun j : Fin n => {j})).getD i ∅

def tagged (n : ℕ) (gs : List Gate) (i : ℕ) : Signal n :=
  (W n gs i, trace n gs i)

def tcombine {n : ℕ} (b : Bool) (p q : Signal n) : Signal n :=
  (combine b p.1 q.1, if b then ∅ else p.2 ∪ q.2)

lemma trace_length {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) :
    (gs.foldl traceStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, traceStep]; omega

lemma old_trace {n gs i} (hi : i < n + gs.length) (g : Gate) :
    trace n (gs ++ [g]) i = trace n gs i := by
  have hl := trace_length gs (List.ofFn fun j : Fin n => {j})
  simp only [List.length_ofFn] at hl
  simp [trace, List.foldl_append, traceStep, List.getD,
    List.getElem?_append_left (hl ▸ hi : i < (gs.foldl traceStep (List.ofFn fun j : Fin n => {j})).length)]

lemma new_trace (n) (gs : List Gate) (b u v) :
    trace n (gs ++ [binary b u v]) (n + gs.length) =
      if b then ∅ else trace n gs u ∪ trace n gs v := by
  have hl := trace_length gs (List.ofFn fun j : Fin n => {j})
  simp only [List.length_ofFn] at hl
  cases b <;> simp [trace, List.foldl_append, traceStep, binary,
    ← hl, List.getD]

lemma old_tagged {n gs i} (hi : i < n + gs.length) (g : Gate) :
    tagged n (gs ++ [g]) i = tagged n gs i := by
  simp only [tagged, old_wire hi, old_trace hi]

lemma new_tagged (n) (gs : List Gate) (b u v) :
    tagged n (gs ++ [binary b u v]) (n + gs.length) =
      tcombine b (tagged n gs u) (tagged n gs v) := by
  simp only [tagged, new_wire, new_trace, tcombine]

def Dirty {n} (F p : Test n) : Prop := ∃ x, p x ∧ ¬ F x

def Clean {n} (F : Test n) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), gs[i].op = .and → Dirty F (W n gs (n+i))

def Tame (n : ℕ) (colour : Fin n → Bool) (gs : List Gate) : Prop :=
  ∀ i < n + gs.length, ∀ a ∈ trace n gs i, ∀ b ∈ trace n gs i, colour a = colour b

def MonoTag {n : ℕ} (colour : Fin n → Bool) (s : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, colour a = colour b

lemma monotag_subset {n : ℕ} {colour : Fin n → Bool} {s t : Finset (Fin n)}
    (h : s ⊆ t) (ht : MonoTag colour t) : MonoTag colour s := by
  intro a ha b hb
  exact ht a (h ha) b (h hb)

lemma tcombine_tag_subset {n : ℕ} (b : Bool) {p q f g : Signal n}
    (hp : p.2 ⊆ f.2) (hq : q.2 ⊆ g.2) :
    (tcombine b p q).2 ⊆ (tcombine b f g).2 := by
  cases b
  · exact Finset.union_subset_union hp hq
  · exact Finset.Subset.refl _

def countAnd (gs : List Gate) : ℕ :=
  gs.countP fun g => match g.op with | .and => true | _ => false

def countOr (gs : List Gate) : ℕ :=
  gs.countP fun g => match g.op with | .or => true | _ => false

def aDelta (b : Bool) : ℕ := if b then 1 else 0

def oDelta (b : Bool) : ℕ := if b then 0 else 1

lemma countAnd_append (gs : List Gate) (b : Bool) (u v : ℕ) :
    countAnd (gs ++ [binary b u v]) = countAnd gs + aDelta b := by
  cases b <;> simp [countAnd,binary,aDelta]

lemma countOr_append (gs : List Gate) (b : Bool) (u v : ℕ) :
    countOr (gs ++ [binary b u v]) = countOr gs + oDelta b := by
  cases b <;> simp [countOr,binary,oDelta]

def Pool {n} (F : Test n) (colour : Fin n → Bool) (R : Set (Signal n)) (c ca co : ℕ) : Prop :=
  ∃ gs : List Gate, gs.length ≤ c ∧ countAnd gs ≤ ca ∧ countOr gs ≤ co ∧ Layout n gs ∧ Clean F gs ∧ Tame n colour gs ∧
    ∀ p ∈ R, Dirty F p.1 ∧ ∃ i < n + gs.length, tagged n gs i = p

lemma pool_append {n} {F : Test n} {colour : Fin n → Bool} {R c ca co}
    (h : Pool F colour R c ca co) {p q} (hp : p ∈ R) (hq : q ∈ R) (b : Bool)
    (hd : Dirty F (tcombine b p q).1) (ht : MonoTag colour (tcombine b p q).2) :
    Pool F colour (insert (tcombine b p q) R) (c+1) (ca+aDelta b) (co+oDelta b) := by
  classical
  obtain ⟨gs,hc,hca,hco,hl,hcl,hct,hr⟩ := h
  obtain ⟨u,hu,hpu⟩ := (hr p hp).2
  obtain ⟨v,hv,hqv⟩ := (hr q hq).2
  let g := binary b u v
  have hn : tagged n (gs ++ [g]) (n+gs.length) = tcombine b p q := by
    rw [new_tagged, hpu, hqv]
  refine ⟨gs ++ [g], by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change countAnd (gs ++ [binary b u v]) ≤ ca+aDelta b
    rw [countAnd_append]
    omega
  · change countOr (gs ++ [binary b u v]) ≤ co+oDelta b
    rw [countOr_append]
    omega
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
      change Dirty F (tagged n (gs ++ [g]) (n+gs.length)).1
      rw [hn]
      exact hd
  · intro i hi
    by_cases hj : i < n + gs.length
    · rw [old_trace hj]
      exact hct i hj
    · have : i = n + gs.length := by simp at hi; omega
      subst i
      change MonoTag colour (tagged n (gs ++ [g]) (n+gs.length)).2
      rw [hn]
      exact ht
  · intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact ⟨hd, n+gs.length, by simp, hn⟩
    · obtain ⟨hsd,i,hi,he⟩ := hr s hs
      exact ⟨hsd,i,by simp; omega,(old_tagged hi g).trans he⟩

def Hit {n} (T : Finset (Term n)) (x : Fin n → Bool) : Prop :=
  ∃ t ∈ T, t.1.1 x ∧ t.2.1 x

def Covers {n} (T : Finset (Term n)) (f p : Test n) : Prop :=
  ∀ x, f x → Hit T x ∨ p x

def Repr {n} (R : Set (Signal n)) (P T : Finset (Term n)) (f : Signal n) : Prop :=
  (∃ p ∈ R, (∀ x, p.1 x → f.1 x) ∧ Covers T f.1 p.1 ∧ p.2 ⊆ f.2) ∨
  ∃ t ∈ P, Covers T f.1 (fun x => t.1.1 x ∧ t.2.1 x)

def Sound {n} (F : Test n) (R : Set (Signal n)) (P : Finset (Term n)) : Prop :=
  ∀ t ∈ P, t.1 ∈ R ∧ t.2 ∈ R ∧ ∀ x, t.1.1 x → t.2.1 x → F x

def Model {n} (F : Test n) (colour : Fin n → Bool) (S : Set (Signal n)) (k ka ko : ℕ) : Prop :=
  ∃ R P T c ca co, Pool F colour R c ca co ∧ Sound F R P ∧ T ⊆ P ∧
    c + P.card + T.card ≤ k ∧ ca + P.card ≤ ka ∧ co + T.card ≤ ko ∧
    ∀ f ∈ S, Repr R P T f

lemma hit_mono {n} {T U : Finset (Term n)} (h : T ⊆ U) {x} :
    Hit T x → Hit U x := fun ⟨t,ht,ha⟩ => ⟨t,h ht,ha⟩

lemma repr_mono {n} {R R' : Set (Signal n)} {P P' T T' : Finset (Term n)} {f}
    (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T') (h : Repr R P T f) :
    Repr R' P' T' f := by
  have liftCov {a : Test n} (hc : Covers T f.1 a) : Covers T' f.1 a :=
    fun x hx => (hc x hx).imp (hit_mono ht) id
  rcases h with ⟨p,hm,hl,hc,htag⟩ | ⟨t,hm,hc⟩
  · exact Or.inl ⟨p,hr hm,hl,liftCov hc,htag⟩
  · exact Or.inr ⟨t,hp hm,liftCov hc⟩

lemma combine_comm {n} (b) (f g : Test n) :
    combine b f g = combine b g f := by
  funext x
  cases b <;> simp [combine, and_comm, or_comm]

lemma tcombine_comm {n} (b) (f g : Signal n) :
    tcombine b f g = tcombine b g f := by
  cases b <;> simp [tcombine, combine_comm, Finset.union_comm]

lemma cov_combine {n} {T : Finset (Term n)} {f g p q} (b)
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
    · exact ⟨ha hx.1, hb hx.2⟩

lemma model_add {n} {F : Test n} {colour : Fin n → Bool} {S k ka ko}
    (h : Model F colour S k ka ko) {f g} (hf : f ∈ S) (hg : g ∈ S) (b)
    (hmono : MonoTag colour (tcombine b f g).2) :
    Model F colour (insert (tcombine b f g) S) (k+1) (ka+aDelta b) (ko+oDelta b) := by
  classical
  obtain ⟨R,P,T,c,ca,co,pool,sound,sub,budget,budgetA,budgetO,reps⟩ := h
  have finish {s : Signal n} {R' P' T' c' ca' co'}
      (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T')
      (pl : Pool F colour R' c' ca' co') (so : Sound F R' P') (su : T' ⊆ P')
      (bu : c'+P'.card+T'.card ≤ k+1)
      (buA : ca'+P'.card ≤ ka+aDelta b) (buO : co'+T'.card ≤ ko+oDelta b)
      (rep : Repr R' P' T' s) :
      Model F colour (insert s S) (k+1) (ka+aDelta b) (ko+oDelta b) := by
    refine ⟨R',P',T',c',ca',co',pl,so,su,bu,buA,buO,?_⟩
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact rep
    · exact repr_mono hr hp ht (reps a ha)
  have virtual {a d : Signal n} {t} (ht : t ∈ P)
      (hc : Covers T a.1 (fun x => t.1.1 x ∧ t.2.1 x)) (hd : Repr R P T d) :
      Model F colour (insert (tcombine b a d) S) (k+1) (ka+aDelta b) (ko+oDelta b) := by
    cases b
    · let U := insert t T
      have incl : T ⊆ U := Finset.subset_insert t T
      have cover {s : Test n} (cs : Covers T d.1 s) : Covers U (tcombine false a d).1 s := by
        intro x hx
        rcases hx with ha | hd'
        · rcases hc x ha with hh | hh
          · exact Or.inl (hit_mono incl hh)
          · exact Or.inl ⟨t,Finset.mem_insert_self _ _,hh⟩
        · exact (cs x hd').imp (hit_mono incl) id
      apply finish (Set.Subset.rfl) (Finset.Subset.refl _) incl pool sound
        (Finset.insert_subset ht sub) (by have := Finset.card_insert_le t T; dsimp [U]; omega)
        (by simpa [aDelta] using budgetA)
        (by have := Finset.card_insert_le t T; dsimp [U,oDelta]; omega)
      rcases hd with ⟨q,hq,hlo,hcov,htag⟩ | ⟨s,hs,hcov⟩
      · exact Or.inl ⟨q,hq,fun x hx => Or.inr (hlo x hx),cover hcov,
          fun i hi => Finset.mem_union_right a.2 (htag hi)⟩
      · exact Or.inr ⟨s,hs,cover hcov⟩
    · exact finish (Set.Subset.rfl) (Finset.Subset.refl _) (Finset.Subset.refl _) pool sound sub (by omega) (by dsimp [aDelta]; omega) (by simpa [oDelta] using budgetO)
        (Or.inr ⟨t,ht,fun x hx => hc x hx.1⟩)
  have rf := reps f hf
  have rg := reps g hg
  rcases rf with ⟨p,hp,lp,cp,tp⟩ | ⟨t,ht,ct⟩
  · rcases rg with ⟨q,hq,lq,cq,tq⟩ | ⟨t,ht,ct⟩
    · have cov := cov_combine b cp cq
      have tags := tcombine_tag_subset b tp tq
      by_cases dirty : Dirty F (tcombine b p q).1
      · have hr : R ⊆ insert (tcombine b p q) R := Set.subset_insert _ _
        refine finish hr (Finset.Subset.refl _) (Finset.Subset.refl _)
          (pool_append pool hp hq b dirty (monotag_subset tags hmono)) ?_ sub (by omega)
          (by omega) (by omega) ?_
        · intro t ht
          obtain ⟨ha,hb,hf⟩ := sound t ht
          exact ⟨hr ha,hr hb,hf⟩
        · refine Or.inl ⟨tcombine b p q, Set.mem_insert _ _, ?_,cov,tags⟩
          intro x hx
          cases b
          · exact hx.elim (fun h => Or.inl (lp x h)) (fun h => Or.inr (lq x h))
          · exact ⟨lp x hx.1,lq x hx.2⟩
      · cases b
        · obtain ⟨gs,-,-,-,-,-,-,hr⟩ := pool
          obtain ⟨x,hx,hn⟩ := (hr p hp).1
          exact (dirty ⟨x, Or.inl hx,hn⟩).elim
        · let t : Term n := (p,q)
          have incl := Finset.subset_insert t P
          refine finish (Set.Subset.rfl) incl (Finset.Subset.refl _) pool ?_ (sub.trans incl)
            (by have := Finset.card_insert_le t P; omega)
            (by have := Finset.card_insert_le t P; dsimp [aDelta]; omega)
            (by simpa [oDelta] using budgetO) ?_
          · intro s hs
            rcases Finset.mem_insert.mp hs with rfl | hs
            · refine ⟨hp,hq,?_⟩
              intro x hx hy
              by_contra hn
              exact dirty ⟨x,⟨hx,hy⟩,hn⟩
            · exact sound s hs
          · exact Or.inr ⟨t,Finset.mem_insert_self _ _,cov⟩
    · rw [tcombine_comm b f g]
      exact virtual ht ct (Or.inl ⟨p,hp,lp,cp,tp⟩)
  · exact virtual ht ct rg

def Signals (n : ℕ) (gs : List Gate) : Set (Signal n) :=
  {p | ∃ i < n + gs.length, tagged n gs i = p}

lemma simulate {n} (F : Test n) (colour : Fin n → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (gs : List Gate) (hl : Layout n gs) (hcol : Tame n colour gs) :
    Model F colour (Signals n gs) gs.length (countAnd gs) (countOr gs) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Signals n [], ∅, ∅, 0, 0, 0, ?_, by simp [Sound], by simp, by simp,
      by simp [countAnd], by simp [countOr], ?_⟩
    · refine ⟨[],by simp,by simp [countAnd],by simp [countOr],by simp [Layout],by simp [Clean],hcol,?_⟩
      intro p hp
      obtain ⟨i,hi,rfl⟩ := hp
      exact ⟨inputs i (by simpa using hi), i,hi,rfl⟩
    · intro p hp
      exact Or.inl ⟨p,hp,fun _ => id, fun _ hx => Or.inr hx, Finset.Subset.refl _⟩
  | append_singleton gs last ih =>
    have layout : Layout n gs := by
      intro i hi
      obtain ⟨b,u,v,he,hu,hv⟩ := hl i (by simp; omega)
      exact ⟨b,u,v, (List.getElem_append_left hi).symm.trans he,hu,hv⟩
    have colour_old : Tame n colour gs := by
      intro i hi
      have hh := hcol i (by simp; omega)
      rwa [old_trace hi] at hh
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst last
    have colour_new : MonoTag colour
        (tcombine b (tagged n gs u) (tagged n gs v)).2 := by
      rw [← new_tagged]
      exact hcol (n+gs.length) (by simp)
    have h := model_add (ih layout colour_old)
      (f := tagged n gs u) (g := tagged n gs v)
      ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩ b colour_new
    obtain ⟨R,P,T,c,ca,co,hp,hs,ht,hb,hbA,hbO,hr⟩ := h
    refine ⟨R,P,T,c,ca,co,hp,hs,ht,by simpa using hb,
      by simpa only [countAnd_append] using hbA, by simpa only [countOr_append] using hbO,?_⟩
    intro p hm
    obtain ⟨i,hi,rfl⟩ := hm
    by_cases hj : i < n + gs.length
    · rw [old_tagged hj]
      exact hr _ (Set.mem_insert_of_mem _ ⟨i,hj,rfl⟩)
    · have : i = n+gs.length := by simp at hi; omega
      subst i
      rw [new_tagged]
      exact hr _ (Set.mem_insert _ _)

def singleton {n : ℕ} (a : Fin n) (i : Fin n) : Bool := decide (i = a)

def OrOf {n : ℕ} (Q : Finset (Fin n)) : Test n :=
  fun x => ∃ i ∈ Q, x i = true

lemma W_mono {n : ℕ} (gs : List Gate) (h : Layout n gs) (i : ℕ)
    (x y : Fin n → Bool) (hxy : ∀ j, x j = true → y j = true) :
    W n gs i x → W n gs i y := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i < n
    · simpa [W, List.getD, hi] using hxy ⟨i,hi⟩
    · simp [W, List.getD, hi]
  | append_singleton gs g ih =>
    have hp : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := h j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    obtain ⟨b,u,v,he,hu,hv⟩ := h gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst g
    by_cases hi : i < n + gs.length
    · rw [old_wire hi]
      exact ih hp i
    · by_cases hei : i = n + gs.length
      · subst i
        rw [new_wire]
        cases b
        · exact fun hx => hx.elim (fun h => Or.inl (ih hp u h))
            (fun h => Or.inr (ih hp v h))
        · exact fun hx => ⟨ih hp u hx.1,ih hp v hx.2⟩
      · have hl := length_fold (gs ++ [binary b u v]) (List.ofFn x)
        simp only [List.length_ofFn,List.length_append,List.length_singleton] at hl
        have hh : ((gs ++ [binary b u v]).foldl step (List.ofFn x)).length ≤ i := by omega
        simp only [W, List.getD, List.getElem?_eq_none hh, Option.getD_none, Bool.false_eq_true, false_implies]

lemma repr_pure_exact {n : ℕ} {F : Test n} {colour : Fin n → Bool} {R : Set (Signal n)}
    {P T : Finset (Term n)} {c ca co : ℕ} (pool : Pool F colour R c ca co)
    (sound : Sound F R P) (sub : T ⊆ P)
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (Q : Finset (Fin n)) (hQ : Q.Nonempty) {f : Signal n}
    (hf : f.1 = OrOf Q) (rep : Repr R P T f) :
    ∃ p ∈ R, p.1 = OrOf Q := by
  have nohit (a : Fin n) : ¬ Hit T (singleton a) := by
    rintro ⟨t,ht,hp,hq⟩
    exact hsingle a ((sound t (sub ht)).2.2 _ hp hq)
  rcases rep with ⟨p,hp,hlo,hcov,-⟩ | ⟨t,ht,hcov⟩
  · rw [hf] at hlo hcov
    refine ⟨p,hp,?_⟩
    obtain ⟨gs,-,-,-,hl,-,-,hr⟩ := pool
    obtain ⟨i,hi,he⟩ := (hr p hp).2
    have he' : W n gs i = p.1 := congrArg Prod.fst he
    funext x
    apply propext
    refine ⟨hlo x,?_⟩
    rintro ⟨a,ha,hxa⟩
    have hs : OrOf Q (singleton a) := ⟨a,ha,by simp [singleton]⟩
    have hpa := (hcov (singleton a) hs).resolve_left (nohit a)
    rw [← he'] at hpa ⊢
    apply W_mono gs hl i (singleton a) x ?_ hpa
    intro j hj
    have : j = a := by simpa [singleton] using hj
    simpa [this] using hxa
  · rw [hf] at hcov
    obtain ⟨a,ha⟩ := hQ
    have hs : OrOf Q (singleton a) := ⟨a,ha,by simp [singleton]⟩
    obtain hh | hh := hcov (singleton a) hs
    · exact (nohit a hh).elim
    · exact (hsingle a ((sound t ht).2.2 _ hh.1 hh.2)).elim

lemma extract_pure {n : ℕ} (F : Test n) (colour : Fin n → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (C : Circuit) (hl : IsAO2 n C) (hcol : Tame n colour C.gates) (hne : ∃ x, F x)
    (ho : W n C.gates C.output = F) :
    ∃ (gs : List Gate) (U : Finset (ℕ × ℕ)), Layout n gs ∧ Clean F gs ∧
      Tame n colour gs ∧
      (∀ t ∈ U, t.1 < n + gs.length ∧ t.2 < n + gs.length) ∧
      (∀ t ∈ U, ∀ x, W n gs t.1 x → W n gs t.2 x → F x) ∧
      (∀ x, F x → ∃ t ∈ U, W n gs t.1 x ∧ W n gs t.2 x) ∧
      gs.length + 2 * U.card ≤ C.size + 1 ∧
      countAnd gs + U.card ≤ countAnd C.gates ∧
      countOr gs + U.card ≤ countOr C.gates + 1 ∧
      (∀ (Q : Finset (Fin n)), Q.Nonempty →
        (∃ i < n + C.gates.length, W n C.gates i = OrOf Q) →
        ∃ i < n + gs.length, W n gs i = OrOf Q) := by
  classical
  obtain ⟨R,P,T,c,ca,co,pool,sound,sub,budget,budgetA,budgetO,reps⟩ :=
    simulate F colour inputs C.gates (layout_of hl) hcol
  have hout : C.output < n+C.gates.length := by
    by_contra! h
    obtain ⟨x,hx⟩ := hne
    rw [← ho] at hx
    have hlen := length_fold C.gates (List.ofFn x)
    simp only [List.length_ofFn] at hlen
    simp [W, List.getD, List.getElem?_eq_none (hlen ▸ h :
        (C.gates.foldl step (List.ofFn x)).length ≤ C.output)] at hx
  obtain ⟨gs,hc,hca,hco,hg,hclean,hcolour,real⟩ := pool
  have pure (Q : Finset (Fin n)) (hQ : Q.Nonempty)
      (hwire : ∃ i < n + C.gates.length, W n C.gates i = OrOf Q) :
      ∃ i < n + gs.length, W n gs i = OrOf Q := by
    obtain ⟨i,hi,he⟩ := hwire
    obtain ⟨p,hp,hpQ⟩ := repr_pure_exact ⟨gs,hc,hca,hco,hg,hclean,hcolour,real⟩ sound sub hsingle Q hQ he
      (reps _ ⟨i,hi,rfl⟩)
    obtain ⟨j,hj,hp⟩ := (real p hp).2
    exact ⟨j,hj,(congrArg Prod.fst hp).trans hpQ⟩
  have rep := reps (tagged n C.gates C.output) ⟨C.output,hout,rfl⟩
  rcases rep with ⟨p,hp,hlo,-⟩ | ⟨t,ht,hcov⟩
  · obtain ⟨x,hx,hn⟩ := (real p hp).1
    have hf := hlo x hx
    change W n C.gates C.output x at hf
    rw [ho] at hf
    exact (hn hf).elim
  · let U := insert t T
    have hu : U ⊆ P := Finset.insert_subset ht sub
    have cu := Finset.card_le_card hu
    have ct : U.card ≤ T.card + 1 := Finset.card_insert_le t T
    let index (p : Signal n) : ℕ := if hp : p ∈ R then ((real p hp).2).choose else 0
    have idx {p : Signal n} (hp : p ∈ R) : W n gs (index p) = p.1 := by
      have hh : tagged n gs (index p) = p := by
        simpa [index,hp] using ((real p hp).2).choose_spec.2
      exact congrArg Prod.fst hh
    let enc (s : Term n) := (index s.1, index s.2)
    refine ⟨gs,U.image enc,hg,hclean,hcolour,?_,?_,?_,?_,?_,?_,pure⟩
    · intro v hv
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨ha,hb,-⟩ := sound s (hu hs)
      constructor
      · simpa [enc,index,ha] using ((real s.1 ha).2).choose_spec.1
      · simpa [enc,index,hb] using ((real s.2 hb).2).choose_spec.1
    · intro v hv
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨ha,hb,hsafe⟩ := sound s (hu hs)
      simpa only [enc, idx ha, idx hb] using hsafe
    · intro x hx
      have hit : Hit U x := by
        have hx' : (tagged n C.gates C.output).1 x := by
          change W n C.gates C.output x
          rw [ho]
          exact hx
        rcases hcov x hx' with hh | hh
        · exact hit_mono (Finset.subset_insert t T) hh
        · exact ⟨t, Finset.mem_insert_self _ _, hh⟩
      obtain ⟨s,hs,ha,hb⟩ := hit
      obtain ⟨hm,hn,-⟩ := sound s (hu hs)
      exact ⟨enc s,Finset.mem_image_of_mem enc hs, by simpa only [enc,idx hm] using ha,
        by simpa only [enc,idx hn] using hb⟩
    · have h := Finset.card_image_le (s := U) (f := enc)
      unfold Circuit.size
      omega
    · have h := Finset.card_image_le (s := U) (f := enc)
      omega
    · have h := Finset.card_image_le (s := U) (f := enc)
      omega

open PEqualNP.TwoColour

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

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

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

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

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

lemma orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_orIn, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨j, hj, hr, ho, hi⟩)
    · exact Fin.ext he
    · have := hr.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

lemma orIn_invalid (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : orIn n C w = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  rcases (mem_orIn n C w i).mp hi with he | ⟨j, hj, hr, ho, hi⟩
  · have := i.isLt
    omega
  · have := (orReaches_bound n C j w hr).2
    omega

lemma orIn_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    orIn n C (n + j) = @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
      ((gateAt C j).inputs.toFinset.biUnion (orIn n C)) ∅ := by
  classical
  ext a
  rw [mem_orIn]
  by_cases hop : (gateAt C j).op = .or
  · simp only [hop, ↓reduceIte, Finset.mem_biUnion]
    constructor
    · rintro (he | ⟨k, hk, hr, hok, hai⟩)
      · have := a.isLt
        omega
      · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨_, w, hw, hlt, hrw⟩⟩
        · subst k
          exact ⟨a.val, List.mem_toFinset.mpr hai, orIn_self n C a⟩
        · exact ⟨w, List.mem_toFinset.mpr hw,
            (mem_orIn n C w a).mpr (Or.inr ⟨k, hk, hrw, hok, hai⟩)⟩
    · rintro ⟨w, hw, haw⟩
      have hw' := List.mem_toFinset.mp hw
      exact (mem_orIn n C (n+j) a).mp
        (orIn_up n C j w a hj hop hw' (hC j hj w hw') haw)
  · simp only [hop, ↓reduceIte]
    simp only [Finset.notMem_empty, iff_false]
    rintro (he | ⟨k, hk, hr, hok, hai⟩)
    · have := a.isLt
      omega
    · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨ho, _⟩⟩
      · subst k
        exact hop hok
      · exact hop ho

noncomputable def reachFrom {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) : List (Finset (Fin n)) := by
  classical
  exact gs.foldl (fun acc g => acc ++ [if g.op = .or then
    g.inputs.toFinset.biUnion (fun i => acc.getD i ∅) else ∅]) w

noncomputable def reachValues (n : ℕ) (gs : List Gate) : List (Finset (Fin n)) :=
  reachFrom gs (List.ofFn fun i : Fin n => {i})

lemma reachFrom_append {n : ℕ} (gs₁ gs₂ : List Gate) (w : List (Finset (Fin n))) :
    reachFrom (gs₁ ++ gs₂) w = reachFrom gs₂ (reachFrom gs₁ w) := by
  simp [reachFrom, List.foldl_append]

lemma reachFrom_ext {n : ℕ} (gs : List Gate) : ∀ w : List (Finset (Fin n)),
    ∃ t : List (Finset (Fin n)), reachFrom gs w = w ++ t ∧ t.length = gs.length := by
  classical
  induction gs with
  | nil => intro w; exact ⟨[], by simp [reachFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := if g.op = .or then g.inputs.toFinset.biUnion (fun i => w.getD i ∅) else ∅
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : reachFrom (g :: gs) w = reachFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma reachFrom_length {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) :
    (reachFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := reachFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma reachValues_length (n : ℕ) (gs : List Gate) :
    (reachValues n gs).length = n + gs.length := by
  simp [reachValues, reachFrom_length]

lemma reachValues_append (n : ℕ) (gs : List Gate) (g : Gate) :
    reachValues n (gs ++ [g]) = reachValues n gs ++
      [@ite (Finset (Fin n)) (g.op = .or) (Classical.propDecidable _)
        (g.inputs.toFinset.biUnion (fun i => (reachValues n gs).getD i ∅)) ∅] := by
  classical
  simp [reachValues, reachFrom, List.foldl_append]

lemma getD_reachFrom_lt {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (i : ℕ) (hi : i < w.length) :
    (reachFrom gs w).getD i ∅ = w.getD i ∅ := by
  obtain ⟨t, ht, _⟩ := reachFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma getD_reachFrom_take {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (k i : ℕ) (hk : k ≤ gs.length) :
    (reachFrom (gs.take k) w).getD i ∅ =
      if i < w.length + k then (reachFrom gs w).getD i ∅ else ∅ := by
  have hlen : (reachFrom (gs.take k) w).length = w.length + k := by
    rw [reachFrom_length, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, reachFrom_append]
    exact (getD_reachFrom_lt (gs.drop k) (reachFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_reachFrom_gate {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (k : ℕ) (hk : k < gs.length) :
    (reachFrom gs w).getD (w.length + k) ∅ =
      @ite (Finset (Fin n)) ((gs[k]).op = .or) (Classical.propDecidable _)
        ((gs[k]).inputs.toFinset.biUnion (fun i =>
          if i < w.length + k then (reachFrom gs w).getD i ∅ else ∅)) ∅ := by
  classical
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (reachFrom (gs.take k) w).length = w.length + k := by
    rw [reachFrom_length, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  let v := if (gs[k]).op = .or then (gs[k]).inputs.toFinset.biUnion
    (fun i => (reachFrom (gs.take k) w).getD i ∅) else ∅
  have heq : reachFrom gs w = reachFrom (gs.drop (k + 1))
      (reachFrom (gs.take k) w ++ [v]) := by
    conv_lhs => rw [hsplit, reachFrom_append]
    rfl
  rw [heq, getD_reachFrom_lt]
  · rw [← hlen]
    have hs : (reachFrom (gs.take k) w ++ [v]).getD (reachFrom (gs.take k) w).length ∅ = v := by simp
    rw [hs]
    unfold v
    split_ifs with hop
    · apply Finset.biUnion_congr rfl
      intro i hi
      rw [getD_reachFrom_take gs w k i (Nat.le_of_lt hk), heq, hlen]
      simp only [v, hop, ↓reduceIte]
    · rfl
  · rw [List.length_append, hlen]
    simp

lemma reachValues_input (n : ℕ) (gs : List Gate) (w : ℕ) (hw : w < n) :
    (reachValues n gs).getD w ∅ = {⟨w, hw⟩} := by
  unfold reachValues
  rw [getD_reachFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma reachValues_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (reachValues n C.gates).getD (n+j) ∅ =
      @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
        ((gateAt C j).inputs.toFinset.biUnion (fun i => (reachValues n C.gates).getD i ∅)) ∅ := by
  classical
  have he := getD_reachFrom_gate C.gates (List.ofFn fun i : Fin n => {i}) j hj
  simp only [List.length_ofFn] at he
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, hj]
  unfold reachValues
  rw [he, ← hg]
  split_ifs with hop
  · apply Finset.biUnion_congr rfl
    intro i hi
    simp only [hC j hj i (List.mem_toFinset.mp hi), ↓reduceIte]
  · rfl

lemma reachValues_eq_orIn (n : ℕ) (C : Circuit) (hC : ReadsBack n C) :
    ∀ w, (reachValues n C.gates).getD w ∅ = orIn n C w := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hi : w < n
    · rw [reachValues_input n C.gates w hi, orIn_input n C w hi]
    · by_cases hw : w < n + C.gates.length
      · have hj : w-n < C.gates.length := by omega
        have he : n+(w-n) = w := by omega
        rw [← he, reachValues_gate n C hC (w-n) hj, orIn_gate n C hC (w-n) hj]
        split_ifs with hop
        · apply Finset.biUnion_congr rfl
          intro i hmem
          exact ih i (by have := hC (w-n) hj i (List.mem_toFinset.mp hmem); omega)
        · rfl
      · rw [List.getD_eq_default _ _ (by rw [reachValues_length]; omega),
          orIn_invalid n C w (by omega)]

lemma tCount_zero_iff_gate (n : ℕ) (C : Circuit) (lin : ℕ → Bool) :
    tCount n C lin = 0 ↔ ∀ j < C.gates.length, (gateAt C j).op = .or →
      ∀ a ∈ orIn n C (n+j), ∀ b ∈ orIn n C (n+j), lin a.val = lin b.val := by
  classical
  rw [tCount, Finset.card_eq_zero]
  constructor
  · intro hz j hj hop a ha b hb
    by_contra hne
    have hm : (∃ i ∈ orIn n C (n+j), lin i.val = false) ∧
        (∃ i ∈ orIn n C (n+j), lin i.val = true) := by
      cases hla : lin a.val <;> cases hlb : lin b.val
      · exact (hne (hla.trans hlb.symm)).elim
      · exact ⟨⟨a,ha,hla⟩,⟨b,hb,hlb⟩⟩
      · exact ⟨⟨b,hb,hlb⟩,⟨a,ha,hla⟩⟩
      · exact (hne (hla.trans hlb.symm)).elim
    have hmem : j ∈ twoColour n C lin :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, hop, hm⟩
    rw [hz] at hmem
    exact Finset.notMem_empty j hmem
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro j hj
    obtain ⟨_, hj', hop, ⟨a,ha,hla⟩, ⟨b,hb,hlb⟩⟩ := Finset.mem_filter.mp hj
    have he := h j hj' hop a ha b hb
    rw [hla, hlb] at he
    cases he

lemma tCount_zero_all_wires (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) (hT : tCount n C lin = 0) :
    ∀ w, ∀ a ∈ orIn n C w, ∀ b ∈ orIn n C w, lin a.val = lin b.val := by
  classical
  intro w a ha b hb
  by_cases hw : w < n
  · rw [orIn_input n C w hw, Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · by_cases hv : w < n+C.gates.length
    · have hj : w-n < C.gates.length := by omega
      have he : n+(w-n) = w := by omega
      by_cases hop : (gateAt C (w-n)).op = .or
      · exact (tCount_zero_iff_gate n C lin).mp hT (w-n) hj hop a
          (by simpa [he] using ha) b (by simpa [he] using hb)
      · have hempty : orIn n C w = ∅ := by
          rw [← he, orIn_gate n C hC (w-n) hj]
          simp only [hop, ↓reduceIte]
        rw [hempty] at ha
        exact (Finset.notMem_empty a ha).elim
    · rw [orIn_invalid n C w (by omega)] at ha
      exact (Finset.notMem_empty a ha).elim

lemma tCount_zero_iff_reachValues (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) :
    tCount n C lin = 0 ↔ ∀ w, ∀ a ∈ (reachValues n C.gates).getD w ∅,
      ∀ b ∈ (reachValues n C.gates).getD w ∅, lin a.val = lin b.val := by
  simp only [reachValues_eq_orIn n C hC]
  constructor
  · exact tCount_zero_all_wires n C lin hC
  · intro h
    exact (tCount_zero_iff_gate n C lin).mpr (fun j hj hop => h (n+j))


lemma trace_fold_eq_reachValues {n : ℕ} {gs : List Gate} (hl : Layout n gs) :
    gs.foldl traceStep (List.ofFn fun j : Fin n => {j}) = reachValues n gs := by
  classical
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    have hp : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := hl j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst g
    rw [List.foldl_append, ih hp, reachValues_append]
    cases b <;> simp [traceStep,binary]

lemma trace_eq_orIn {n : ℕ} (C : Circuit) (hl : IsAO2 n C) (i : ℕ) :
    trace n C.gates i = orIn n C i := by
  rw [trace, trace_fold_eq_reachValues (layout_of hl)]
  exact reachValues_eq_orIn n C hl.2.1 i

lemma tame_iff_tCount_zero {n : ℕ} (C : Circuit) (hl : IsAO2 n C) (lin : ℕ → Bool) :
    Tame n (fun i => lin i.val) C.gates ↔ tCount n C lin = 0 := by
  constructor
  · intro ht
    apply (tCount_zero_iff_gate n C lin).mpr
    intro j hj hop a ha b hb
    rw [← trace_eq_orIn C hl] at ha hb
    exact ht (n+j) (by omega) a ha b hb
  · intro ht i hi a ha b hb
    rw [trace_eq_orIn C hl] at ha hb
    exact tCount_zero_all_wires n C lin hl.2.1 ht i a ha b hb

lemma extract_pure_official {n : ℕ} (F : Test n) (lin : ℕ → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (C : Circuit) (hl : IsAO2 n C) (hcol : tCount n C lin = 0)
    (hne : ∃ x, F x) (ho : W n C.gates C.output = F) :
    ∃ (D : Circuit) (U : Finset (ℕ × ℕ)), IsAO2 n D ∧
      tCount n D lin = 0 ∧ Clean F D.gates ∧
      (∀ t ∈ U, t.1 < n + D.gates.length ∧ t.2 < n + D.gates.length) ∧
      (∀ t ∈ U, ∀ x, W n D.gates t.1 x → W n D.gates t.2 x → F x) ∧
      (∀ x, F x → ∃ t ∈ U, W n D.gates t.1 x ∧ W n D.gates t.2 x) ∧
      D.size + 2 * U.card ≤ C.size + 1 ∧
      countAnd D.gates + U.card ≤ countAnd C.gates ∧
      countOr D.gates + U.card ≤ countOr C.gates + 1 ∧
      (∀ (Q : Finset (Fin n)), Q.Nonempty →
        (∃ i < n + C.gates.length, W n C.gates i = OrOf Q) →
        ∃ i < n + D.gates.length, W n D.gates i = OrOf Q) := by
  obtain ⟨gs,U,hg,hclean,ht,hb,hs,hcov,hsize,hsizeA,hsizeO,hpure⟩ :=
    extract_pure F (fun i => lin i.val) inputs hsingle C hl
      ((tame_iff_tCount_zero C hl lin).mpr hcol) hne ho
  have hD := layout_ao hg
  exact ⟨⟨gs,0⟩,U,hD,(tame_iff_tCount_zero ⟨gs,0⟩ hD lin).mp ht,
    hclean,hb,hs,hcov,hsize,hsizeA,hsizeO,hpure⟩

end H8TaggedCounts

namespace H8AssemblyCounts

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4970.H8TaggedCounts

lemma old_wire_append {n : ℕ} (gs hs : List Gate) {i : ℕ}
    (hi : i < n + gs.length) : W n (gs ++ hs) i = W n gs i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, old_wire (by simp; omega), ih]

lemma old_trace_append {n : ℕ} (gs hs : List Gate) {i : ℕ}
    (hi : i < n + gs.length) : trace n (gs ++ hs) i = trace n gs i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, old_trace (by simp; omega), ih]

lemma layout_append_binary {n : ℕ} {gs : List Gate} (hl : Layout n gs)
    (b : Bool) (u v : ℕ) (hu : u < n + gs.length) (hv : v < n + gs.length) :
    Layout n (gs ++ [binary b u v]) := by
  intro i hi
  by_cases hj : i < gs.length
  · obtain ⟨b',u',v',he,hu',hv'⟩ := hl i hj
    exact ⟨b',u',v',by simpa [List.getElem_append_left hj] using he,hu',hv'⟩
  · have hei : i = gs.length := by simp at hi; omega
    subst i
    exact ⟨b,u,v,by simp,hu,hv⟩

lemma tame_append_binary {n : ℕ} {colour : Fin n → Bool} {gs : List Gate}
    (ht : Tame n colour gs) (b : Bool) (u v : ℕ)
    (hm : MonoTag colour (if b then ∅ else trace n gs u ∪ trace n gs v)) :
    Tame n colour (gs ++ [binary b u v]) := by
  intro i hi
  by_cases hj : i < n + gs.length
  · rw [old_trace hj]
    exact ht i hj
  · have hei : i = n + gs.length := by simp at hi; omega
    subst i
    rw [new_trace]
    exact hm

def AndBound (n k : ℕ) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), gs[i].op = .and → ∀ w ∈ gs[i].inputs, w < n + k

lemma andBound_base {n : ℕ} {gs : List Gate} (hl : Layout n gs) :
    AndBound n gs.length gs := by
  intro i hi hop w hw
  obtain ⟨b,u,v,he,hu,hv⟩ := hl i hi
  rw [he] at hw
  simp [binary] at hw
  rcases hw with rfl | rfl <;> omega

lemma andBound_append {n k : ℕ} {gs : List Gate} (hb : AndBound n k gs)
    (b : Bool) (u v : ℕ) (hnew : b = true → u < n+k ∧ v < n+k) :
    AndBound n k (gs ++ [binary b u v]) := by
  intro i hi hop w hw
  by_cases hj : i < gs.length
  · exact hb i hj (by simpa [List.getElem_append_left hj] using hop) w
      (by simpa [List.getElem_append_left hj] using hw)
  · have hei : i = gs.length := by simp at hi; omega
    subst i
    have hbtrue : b = true := by cases b <;> simp_all [binary]
    obtain ⟨hu,hv⟩ := hnew hbtrue
    simp [binary] at hw
    rcases hw with rfl | rfl <;> assumption

lemma mono_empty {n : ℕ} (colour : Fin n → Bool) : MonoTag colour ∅ := by
  simp [MonoTag]

lemma assemble_nonempty {n : ℕ} (colour : Fin n → Bool) (gs : List Gate)
    (hl : Layout n gs) (ht : Tame n colour gs)
    (us : List (ℕ × ℕ)) (hne : us ≠ [])
    (hb : ∀ p ∈ us, p.1 < n+gs.length ∧ p.2 < n+gs.length) :
    ∃ (hs : List Gate) (out : ℕ), gs.IsPrefix hs ∧
      hs.length + 1 = gs.length + 2 * us.length ∧
      countAnd hs = countAnd gs + us.length ∧ countOr hs + 1 = countOr gs + us.length ∧
      Layout n hs ∧ Tame n colour hs ∧
      out < n+hs.length ∧ trace n hs out = ∅ ∧ AndBound n gs.length hs ∧
      (∀ x, W n hs out x ↔ ∃ p ∈ us, W n gs p.1 x ∧ W n gs p.2 x) := by
  induction us with
  | nil => exact (hne rfl).elim
  | cons p ps ih =>
    have hp := hb p (by simp)
    by_cases hz : ps = []
    · subst ps
      let g := binary true p.1 p.2
      refine ⟨gs ++ [g],n+gs.length,⟨[g],rfl⟩,by simp,?_,?_,?_,?_,by simp,?_,?_,?_⟩
      · simp [g,countAnd_append,aDelta]
      · simp [g,countOr_append,oDelta]
      · exact layout_append_binary hl true p.1 p.2 hp.1 hp.2
      · exact tame_append_binary ht true p.1 p.2 (mono_empty colour)
      · exact new_trace n gs true p.1 p.2
      · exact andBound_append (andBound_base hl) true p.1 p.2 (fun _ => hp)
      · intro x
        rw [new_wire]
        simp [combine]
    · obtain ⟨hs,o,hprefix,hlen,hA,hO,hhl,hht,ho,hto,hab,hsem⟩ :=
        ih hz (fun q hq => hb q (by simp [hq]))
      obtain ⟨suffix,hs_eq⟩ := hprefix
      have hgslen : gs.length ≤ hs.length := by rw [← hs_eq]; simp
      have hpu : p.1 < n+hs.length := by omega
      have hpv : p.2 < n+hs.length := by omega
      let prod := binary true p.1 p.2
      let mid := hs ++ [prod]
      let join := binary false o (n+hs.length)
      have hlmid : Layout n mid := layout_append_binary hhl true p.1 p.2 hpu hpv
      have htmid : Tame n colour mid := tame_append_binary hht true p.1 p.2 (mono_empty colour)
      have homid : o < n+mid.length := by simp [mid]; omega
      have hpmid : n+hs.length < n+mid.length := by simp [mid]
      have tr_o : trace n mid o = ∅ := by rw [old_trace ho]; exact hto
      have tr_p : trace n mid (n+hs.length) = ∅ := new_trace n hs true p.1 p.2
      refine ⟨mid ++ [join],n+mid.length,?_,?_,?_,?_,?_,?_,by simp,?_,?_,?_⟩
      · refine ⟨suffix ++ [prod,join],?_⟩
        simp [mid,← hs_eq,List.append_assoc]
      · simp only [List.length_append,List.length_cons]
        dsimp [mid]
        simp only [List.length_append,List.length_singleton]
        omega
      · dsimp [mid,prod,join]
        rw [countAnd_append,countAnd_append]
        simp only [aDelta,Bool.false_eq_true,ite_false,ite_true]
        omega
      · dsimp [mid,prod,join]
        rw [countOr_append,countOr_append]
        simp only [oDelta,Bool.false_eq_true,ite_false,ite_true]
        omega
      · exact layout_append_binary hlmid false o (n+hs.length) homid hpmid
      · apply tame_append_binary htmid false o (n+hs.length)
        simpa [tr_o,tr_p] using mono_empty colour
      · rw [new_trace]
        simp [tr_o,tr_p]
      · exact andBound_append (andBound_append hab true p.1 p.2 (fun _ => hp))
          false o (n+hs.length) (by simp)
      · intro x
        rw [new_wire]
        change (W n mid o x ∨ W n mid (n+hs.length) x) ↔ _
        rw [old_wire ho,new_wire,hsem]
        have hpu_old : W n hs p.1 = W n gs p.1 := by
          rw [← hs_eq]; exact old_wire_append gs suffix hp.1
        have hpv_old : W n hs p.2 = W n gs p.2 := by
          rw [← hs_eq]; exact old_wire_append gs suffix hp.2
        simp only [combine,hpu_old,hpv_old]
        simp [or_comm]

lemma normalize_preserving {n : ℕ} (F : Test n) (lin : ℕ → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hcol : PEqualNP.TwoColour.tCount n C lin = 0)
    (hne : ∃ x, F x) (ho : W n C.gates C.output = F) :
    ∃ (D : Circuit) (k : ℕ), D.size ≤ C.size ∧
      countAnd D.gates ≤ countAnd C.gates ∧ countOr D.gates ≤ countOr C.gates ∧
      PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.TwoColour.tCount n D lin = 0 ∧ W n D.gates D.output = F ∧
      AndBound n k D.gates ∧
      (∀ i (hi : i < D.gates.length), i < k → D.gates[i].op = .and →
        Dirty F (W n D.gates (n+i))) ∧
      (∀ (Q : Finset (Fin n)), Q.Nonempty →
        (∃ i < n + C.gates.length, W n C.gates i = OrOf Q) →
        ∃ i < n + D.gates.length, W n D.gates i = OrOf Q) := by
  classical
  obtain ⟨base,U,hbase,htbase,hclean,hb,hsafe,hcover,hsize,hsizeA,hsizeO,hpure⟩ :=
    extract_pure_official F lin inputs hsingle C hC hcol hne ho
  have hU : U.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨p,hp,-⟩ := hcover x hx
    exact ⟨p,hp⟩
  have hlist : U.toList ≠ [] := by simpa using hU.ne_empty
  obtain ⟨gs,out,hprefix,hlen,hA,hO,hl,ht,hout,htrace,hand,hfun⟩ :=
    assemble_nonempty (fun i : Fin n => lin i.val) base.gates (layout_of hbase)
      ((tame_iff_tCount_zero base hbase lin).mpr htbase) U.toList hlist
      (by simpa using hb)
  obtain ⟨suffix,hsuffix⟩ := hprefix
  have hbaselen : base.gates.length ≤ gs.length := by rw [← hsuffix]; simp
  have hD : PEqualNP.TopForm.IsAO2 n (⟨gs,out⟩ : Circuit) := layout_ao hl
  refine ⟨⟨gs,out⟩,base.gates.length,?_,?_,?_,hD,?_,?_,hand,?_,?_⟩
  · simp only [Finset.length_toList] at hlen
    change gs.length ≤ C.size
    change base.gates.length + 2 * U.card ≤ C.size + 1 at hsize
    omega
  · change countAnd gs ≤ countAnd C.gates
    simp only [Finset.length_toList] at hA
    omega
  · change countOr gs ≤ countOr C.gates
    simp only [Finset.length_toList] at hO
    omega
  · exact (tame_iff_tCount_zero ⟨gs,out⟩ hD lin).mp ht
  · funext x
    apply propext
    rw [hfun]
    constructor
    · rintro ⟨p,hp,h1,h2⟩
      exact hsafe p (by simpa using hp) x h1 h2
    · intro hx
      obtain ⟨p,hp,h1,h2⟩ := hcover x hx
      exact ⟨p,by simpa using hp,h1,h2⟩
  · intro i hi hik hop
    change i < gs.length at hi
    have hopbase : base.gates[i].op = .and := by
      simpa [← hsuffix,List.getElem_append_left hik] using hop
    have hd := hclean i hik hopbase
    change Dirty F (W n gs (n+i))
    rw [← hsuffix,old_wire_append base.gates suffix (by omega)]
    exact hd
  · intro Q hQ hQold
    obtain ⟨i,hi,he⟩ := hpure Q hQ hQold
    refine ⟨i,by change i < n+gs.length; omega,?_⟩
    change W n gs i = OrOf Q
    rw [← hsuffix,old_wire_append base.gates suffix hi]
    exact he

end H8AssemblyCounts


namespace H8TopBridgeCounts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl


lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
    intro k hk
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      gateAt_eq_getElem C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ}
    (hj : j < C.gates.length) (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w, _, hn, hw, he | he⟩ := (inCone_iff n C i j hj).mp h
    · omega
    · have hwj : w - n < j := by omega
      have hi := ih (w - n) hwj (by omega) he
      omega

lemma inCone_before_cutoff {n k : ℕ} {C : Circuit} {i j : ℕ}
    (hj : j < C.gates.length)
    (hinputs : ∀ w ∈ (gateAt C j).inputs, w < n + k)
    (h : InCone n C i j) : i < k := by
  obtain ⟨w, hwmem, hn, hw, he | he⟩ := (inCone_iff n C i j hj).mp h
  · have hk := hinputs w hwmem
    omega
  · have hk := hinputs w hwmem
    have hi := inCone_lt (by omega : w - n < C.gates.length) he
    omega

lemma safe_and_no_and_cone {n k : ℕ} {C : Circuit}
    (F : (Fin n → Bool) → Prop)
    (hinputs : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, w < n + k)
    (hdirty : ∀ i < C.gates.length, i < k → (gateAt C i).op = GateOp.and →
      ∃ x : Fin n → Bool, gateVal n C i x = true ∧ ¬ F x) :
    ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and →
      (∀ x : Fin n → Bool, gateVal n C i x = true → F x) →
      (gateAt C j).op = GateOp.and → ¬ InCone n C i j := by
  intro i hi j hj hai hsafe haj hcone
  have hik : i < k := inCone_before_cutoff hj (hinputs j hj haj) hcone
  obtain ⟨x, hx, hnot⟩ := hdirty i hi hik hai
  exact hnot (hsafe x hx)

end H8TopBridgeCounts

namespace H8NormalizationCounts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.H8TaggedCounts
  PEqualNP.Outside.L_meta_4970.H8AssemblyCounts
  PEqualNP.Outside.L_meta_4970.H8TopBridgeCounts

lemma normalize_top_preserving {n : ℕ} (F : Test n) (lin : ℕ → Bool)
    (inputs : ∀ i < n, Dirty F (W n [] i))
    (hsingle : ∀ a : Fin n, ¬ F (singleton a))
    (C : Circuit) (hC : IsAO2 n C)
    (hcol : PEqualNP.TwoColour.tCount n C lin = 0)
    (hne : ∃ x, F x) (ho : W n C.gates C.output = F) :
    ∃ D : Circuit, D.size ≤ C.size ∧
      countAnd D.gates ≤ countAnd C.gates ∧ countOr D.gates ≤ countOr C.gates ∧ IsAO2 n D ∧
      PEqualNP.TwoColour.tCount n D lin = 0 ∧ W n D.gates D.output = F ∧
      (∀ i < D.gates.length, ∀ j < D.gates.length,
        (gateAt D i).op = .and →
        (∀ x : Fin n → Bool, gateVal n D i x = true → F x) →
        (gateAt D j).op = .and → ¬ InCone n D i j) ∧
      (∀ (Q : Finset (Fin n)), Q.Nonempty →
        (∃ i < n + C.gates.length, W n C.gates i = OrOf Q) →
        ∃ i < n + D.gates.length, W n D.gates i = OrOf Q) := by
  obtain ⟨D,k,hsize,hA,hO,hD,ht,hF,hbound,hdirty,hpure⟩ :=
    normalize_preserving F lin inputs hsingle C hC hcol hne ho
  refine ⟨D,hsize,hA,hO,hD,ht,hF,?_,hpure⟩
  apply safe_and_no_and_cone F
  · intro j hj hop w hw
    rw [gateAt_eq_getElem D j hj] at hop hw
    exact hbound j hj hop w hw
  · intro i hi hik hop
    rw [gateAt_eq_getElem D i hi] at hop
    exact hdirty i hi hik hop

end H8NormalizationCounts


namespace H8RootsCounts

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4970.H8TaggedCounts

lemma factor_eq_or {n : ℕ} (Q : Finset (Fin n)) (f : Test n)
    (hm : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → f x → f y)
    (hz : ¬ f (fun i => decide (i ∉ Q)))
    (hc : ∀ x, OrOf Q x → f x) : f = OrOf Q := by
  classical
  funext x
  apply propext
  refine ⟨?_,hc x⟩
  intro hx
  by_contra hn
  apply hz
  apply hm x _ ?_ hx
  intro i hi
  by_cases hq : i ∈ Q
  · exact (hn ⟨i,hq,hi⟩).elim
  · simp [hq]

lemma and_eq_or {n : ℕ} (Q : Finset (Fin n)) (f g : Test n)
    (hf : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → f x → f y)
    (hg : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → g x → g y)
    (he : combine true f g = OrOf Q) : f = OrOf Q ∨ g = OrOf Q := by
  classical
  have hc (x) (hx : OrOf Q x) : f x ∧ g x := by
    change combine true f g x
    rw [he]
    exact hx
  have hz : ¬ (f (fun i => decide (i ∉ Q)) ∧ g (fun i => decide (i ∉ Q))) := by
    change ¬ combine true f g (fun i => decide (i ∉ Q))
    rw [he]
    simp [OrOf]
  rcases not_and_or.mp hz with hz | hz
  · exact Or.inl (factor_eq_or Q f hf hz fun x hx => (hc x hx).1)
  · exact Or.inr (factor_eq_or Q g hg hz fun x hx => (hc x hx).2)

lemma pure_or_root {n : ℕ} (gs : List Gate) (hl : Layout n gs)
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (hw : ∃ i < n + gs.length, W n gs i = OrOf Q) :
    ∃ (j : ℕ) (hj : j < gs.length), gs[j].op = .or ∧ W n gs (n+j) = OrOf Q := by
  induction gs using List.reverseRecOn with
  | nil =>
    obtain ⟨i,hi,he⟩ := hw
    have hi' : i < n := by simpa using hi
    have hsub : Q ⊆ {⟨i,hi'⟩} := by
      intro a ha
      have hx : W n [] i (H8TaggedCounts.singleton a) := by
        rw [he]
        exact ⟨a,ha,by simp [H8TaggedCounts.singleton]⟩
      have heq : (⟨i,hi'⟩ : Fin n) = a := by
        simpa [W,List.getD,hi',H8TaggedCounts.singleton] using hx
      simp [← heq]
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega
  | append_singleton gs last ih =>
    have hp : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := hl j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    have liftRoot (hr : ∃ (j : ℕ) (hj : j < gs.length), gs[j].op = .or ∧ W n gs (n+j) = OrOf Q) :
        ∃ (j : ℕ) (hj : j < (gs ++ [last]).length), (gs ++ [last])[j].op = .or ∧
          W n (gs ++ [last]) (n+j) = OrOf Q := by
      obtain ⟨j,hj,hop,hjQ⟩ := hr
      refine ⟨j,by simp; omega,?_,?_⟩
      · simpa [List.getElem_append_left hj] using hop
      · rw [old_wire (by omega)]
        exact hjQ
    obtain ⟨i,hi,hiQ⟩ := hw
    by_cases hold : i < n + gs.length
    · apply liftRoot
      apply ih hp
      exact ⟨i,hold,(old_wire hold last).symm.trans hiQ⟩
    · have hei : i = n + gs.length := by simp at hi; omega
      subst i
      obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
      simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
        List.getElem_cons_zero] at he
      subst last
      cases b
      · exact ⟨gs.length,by simp,by simp [binary],hiQ⟩
      · rw [new_wire] at hiQ
        have hfactor := and_eq_or Q (W n gs u) (W n gs v)
          (fun x y hxy => W_mono gs hp u x y hxy)
          (fun x y hxy => W_mono gs hp v x y hxy) hiQ
        apply liftRoot
        apply ih hp
        rcases hfactor with he | he
        · exact ⟨u,hu,he⟩
        · exact ⟨v,hv,he⟩


def served (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ (a : Fin p) (b : Fin l), (a,b) ∈ E →
    (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a,b') ∈ E) ∧
      ∀ x : Fin (p+l) → Bool, (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
    (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a',b) ∈ E) ∧
      ∀ x : Fin (p+l) → Bool, (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))


lemma preserves_pure_served {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C D : Circuit) (hD : PEqualNP.TopForm.IsAO2 (p+l) D)
    (hpure : ∀ (Q : Finset (Fin (p+l))), Q.Nonempty →
      (∃ i < p+l+C.gates.length, W (p+l) C.gates i = OrOf Q) →
      ∃ i < p+l+D.gates.length, W (p+l) D.gates i = OrOf Q)
    (hs : served p l E C) : served p l E D := by
  classical
  intro a b hab
  rcases hs a b hab with ⟨j,Q,hj,hop,hQ,hb,hsub,hval⟩ | ⟨j,P,hj,hop,hP,ha,hsub,hval⟩
  · left
    have hinj : Function.Injective (Fin.natAdd p : Fin l → Fin (p+l)) := by
      intro b b' h
      apply Fin.ext
      have hh := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hh
      omega
    let Q' := Q.image (Fin.natAdd p)
    have hc : 2 ≤ Q'.card := by rw [Finset.card_image_of_injective _ hinj]; exact hQ
    have hnon : Q'.Nonempty := Finset.card_pos.mp (by omega)
    have hwire : W (p+l) C.gates (p+l+j) = OrOf Q' := by
      funext x
      change ((C.wires (List.ofFn x)).getD (p+l+j) false = true) = _
      rw [hval x]
      simp [OrOf,Q']
    obtain ⟨k,hk,hkop,hkval⟩ := pure_or_root D.gates (layout_of hD) Q' hc
      (hpure Q' hnon ⟨p+l+j,by omega,hwire⟩)
    refine ⟨k,Q,hk,?_,hQ,hb,hsub,?_⟩
    · simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD,hk] using hkop
    · intro x
      have hh := congrFun hkval x
      change ((D.wires (List.ofFn x)).getD (p+l+k) false = true) = OrOf Q' x at hh
      have hh' := congrArg (fun P : Prop => decide P) hh
      simpa [OrOf,Q'] using hh'
  · right
    have hinj : Function.Injective (Fin.castAdd l : Fin p → Fin (p+l)) := by
      intro a a' h
      apply Fin.ext
      have hh := congrArg (fun i : Fin (p+l) => i.val) h
      simpa using hh
    let P' := P.image (Fin.castAdd l)
    have hc : 2 ≤ P'.card := by rw [Finset.card_image_of_injective _ hinj]; exact hP
    have hnon : P'.Nonempty := Finset.card_pos.mp (by omega)
    have hwire : W (p+l) C.gates (p+l+j) = OrOf P' := by
      funext x
      change ((C.wires (List.ofFn x)).getD (p+l+j) false = true) = _
      rw [hval x]
      simp [OrOf,P']
    obtain ⟨k,hk,hkop,hkval⟩ := pure_or_root D.gates (layout_of hD) P' hc
      (hpure P' hnon ⟨p+l+j,by omega,hwire⟩)
    refine ⟨k,P,hk,?_,hP,ha,hsub,?_⟩
    · simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD,hk] using hkop
    · intro x
      have hh := congrFun hkval x
      change ((D.wires (List.ofFn x)).getD (p+l+k) false = true) = OrOf P' x at hh
      have hh' := congrArg (fun P : Prop => decide P) hh
      simpa [OrOf,P'] using hh'

end H8RootsCounts

namespace H8PostedCounts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4970.H8TaggedCounts
  PEqualNP.Outside.L_meta_4970.H8NormalizationCounts
  PEqualNP.Outside.L_meta_4970.H8RootsCounts

def edgeTest {p l : ℕ} (E : Finset (Fin p × Fin l)) : Test (p+l) :=
  fun x => ∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true

lemma edge_singleton_false {p l : ℕ} (E : Finset (Fin p × Fin l))
    (i : Fin (p+l)) : ¬ edgeTest E (singleton i) := by
  rintro ⟨a,b,-,ha,hb⟩
  simp only [PEqualNP.Outside.L_meta_4970.H8TaggedCounts.singleton,decide_eq_true_eq] at ha hb
  have hva := congrArg Fin.val ha
  have hvb := congrArg Fin.val hb
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hva hvb
  have := a.isLt
  omega

lemma input_dirty_of_singleton_false {n : ℕ} (F : Test n)
    (hsingle : ∀ a : Fin n, ¬ F (singleton a)) (i : ℕ) (hi : i < n) :
    Dirty F (W n [] i) := by
  exact ⟨singleton ⟨i,hi⟩,by simp [W,List.getD,hi,PEqualNP.Outside.L_meta_4970.H8TaggedCounts.singleton],hsingle ⟨i,hi⟩⟩

def computes {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ x : Fin (p+l) → Bool, circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
    x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

lemma bipartite_normalize_top {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : IsAO2 (p+l) C)
    (hcomp : computes E C) (hT : tCount (p+l) C (fun i => decide (p ≤ i)) = 0)
    (hserved : served p l E C) :
    ∃ D : Circuit, D.size ≤ C.size ∧
      countAnd D.gates ≤ countAnd C.gates ∧ countOr D.gates ≤ countOr C.gates ∧
      IsAO2 (p+l) D ∧ computes E D ∧
      tCount (p+l) D (fun i => decide (p ≤ i)) = 0 ∧ served p l E D ∧
      (∀ i < D.gates.length, ∀ j < D.gates.length,
        (gateAt D i).op = .and →
        (∀ x : Fin (p+l) → Bool, gateVal (p+l) D i x = true → edgeTest E x) →
        (gateAt D j).op = .and → ¬ InCone (p+l) D i j) := by
  have hne : ∃ x, edgeTest E x := by
    obtain ⟨⟨a,b⟩,he⟩ := hE
    exact ⟨fun _ => true,a,b,he,rfl,rfl⟩
  have ho : W (p+l) C.gates C.output = edgeTest E := by
    funext x
    change (circuitFun (p+l) C x = true) = edgeTest E x
    rw [hcomp x]
    simp [edgeTest]
  obtain ⟨D,hsize,hA,hO,hD,hTD,hFD,htop,hpure⟩ :=
    normalize_top_preserving (edgeTest E) (fun i => decide (p ≤ i))
      (input_dirty_of_singleton_false (edgeTest E) (edge_singleton_false E))
      (edge_singleton_false E) C hC hT hne ho
  refine ⟨D,hsize,hA,hO,hD,?_,hTD,preserves_pure_served E C D hD hpure hserved,htop⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change W (p+l) D.gates D.output x ↔ edgeTest E x
  rw [hFD]

end H8PostedCounts

end PEqualNP.Outside.L_meta_4970
