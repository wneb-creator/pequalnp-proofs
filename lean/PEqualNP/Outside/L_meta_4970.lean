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

namespace H8Residual

def sourceVector {p : ℕ} {I : Type*} (Q : I → Finset (Fin p))
    (x : Fin p → Bool) : I → Bool :=
  fun i => decide (∃ a ∈ Q i, x a = true)

lemma source_separates_edge {p l : ℕ} {I : Type*}
    (E : Finset (Fin p × Fin l)) (Q : I → Finset (Fin p))
    (D : (I → Bool) → (Fin l → Bool) → Bool)
    (hm : ∀ y, Monotone (fun u => D u y))
    (hc : ∀ x y, D (sourceVector Q x) y =
      decide (∃ a b, (a,b) ∈ E ∧ x a = true ∧ y b = true))
    (a : Fin p) (b : Fin l) (hab : (a,b) ∈ E) :
    ∃ i, a ∈ Q i ∧ ∀ a' ∈ Q i, (a',b) ∈ E := by
  classical
  let x : Fin p → Bool := fun a' => decide (a' = a)
  let y : Fin p → Bool := fun a' => decide ((a',b) ∉ E)
  let z : Fin l → Bool := fun b' => decide (b' = b)
  have ht : D (sourceVector Q x) z = true := by
    rw [hc]
    simp only [decide_eq_true_eq]
    exact ⟨a,b,hab,by simp [x],by simp [z]⟩
  have hf : D (sourceVector Q y) z = false := by
    rw [hc]
    simp only [decide_eq_false_iff_not]
    rintro ⟨a',b',he,hy,hz⟩
    have hb : b' = b := by simpa [z] using hz
    subst b'
    have hy' : (a',b) ∉ E := by simpa [y] using hy
    exact hy' he
  by_contra hsep
  have bad : ∀ i, a ∈ Q i → ∃ a' ∈ Q i, (a',b) ∉ E := by
    intro i hi
    by_contra h
    apply hsep
    refine ⟨i,hi,?_⟩
    intro a' ha'
    by_contra hn
    exact h ⟨a',ha',hn⟩
  have hle : sourceVector Q x ≤ sourceVector Q y := by
    intro i
    cases hv : sourceVector Q x i with
    | false => simp
    | true =>
      have hi : a ∈ Q i := by simpa [sourceVector,x] using hv
      obtain ⟨a',ha',hne⟩ := bad i hi
      have hv' : sourceVector Q y i = true := by
        simp only [sourceVector,decide_eq_true_eq]
        exact ⟨a',ha',by simp [y,hne]⟩
      simp [hv']
  have h := hm z hle
  change D (sourceVector Q x) z ≤ D (sourceVector Q y) z at h
  rw [ht,hf] at h
  exact (by decide : ¬ ((true : Bool) ≤ false)) h

lemma one_source_cover {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (Q : Finset (Fin p)) :
    ∃ S : Finset (Fin (p+l)), S.card ≤ 1 ∧
      ∀ a b, a ∈ Q → (∀ a' ∈ Q, (a',b) ∈ E) →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  classical
  by_cases hsmall : Q.card ≤ 1
  · refine ⟨Q.image (Fin.castAdd l), (Finset.card_image_le).trans hsmall, ?_⟩
    intro a b ha _
    exact Or.inl (Finset.mem_image_of_mem _ ha)
  · have hlarge : 1 < Q.card := by omega
    obtain ⟨a,ha,a',ha',hne⟩ := Finset.one_lt_card.mp hlarge
    by_cases hex : ∃ b : Fin l, ∀ a' ∈ Q, (a',b) ∈ E
    · obtain ⟨b0,hb0⟩ := hex
      refine ⟨{Fin.natAdd p b0}, by simp, ?_⟩
      intro c b hc hb
      right
      have hbb : b = b0 := by
        by_contra hne'
        exact h4 a a' b b0 hne hne' ⟨hb a ha,hb0 a ha,hb a' ha',hb0 a' ha'⟩
      simp [hbb]
    · refine ⟨∅, by simp, ?_⟩
      intro a b ha hb
      exact (hex ⟨b,hb⟩).elim

lemma sources_give_cover {p l : ℕ} {I : Type*} [Fintype I]
    (E : Finset (Fin p × Fin l)) (Q : I → Finset (Fin p))
    (h4 : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hs : ∀ a b, (a,b) ∈ E → ∃ i, a ∈ Q i ∧ ∀ a' ∈ Q i, (a',b) ∈ E) :
    ∃ S : Finset (Fin (p+l)), S.card ≤ Fintype.card I ∧
      ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  classical
  choose T hT hcover using fun i => one_source_cover E h4 (Q i)
  refine ⟨Finset.univ.biUnion T, ?_, ?_⟩
  · calc
      (Finset.univ.biUnion T).card ≤ ∑ i : I, (T i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : I, 1 := Finset.sum_le_sum fun i _ => hT i
      _ = Fintype.card I := by simp
  · intro a b hab
    obtain ⟨i,hai,hbi⟩ := hs a b hab
    rcases hcover i a b hai hbi with ha | hb
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ha⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hb⟩)

lemma monochromatic_decoder_cover {p l : ℕ} {I : Type*} [Fintype I]
    (E : Finset (Fin p × Fin l)) (Q : I → Finset (Fin p))
    (D : (I → Bool) → (Fin l → Bool) → Bool)
    (h4 : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hm : ∀ y, Monotone (fun u => D u y))
    (hc : ∀ x y, D (sourceVector Q x) y =
      decide (∃ a b, (a,b) ∈ E ∧ x a = true ∧ y b = true)) :
    ∃ S : Finset (Fin (p+l)), S.card ≤ Fintype.card I ∧
      ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  apply sources_give_cover E Q h4
  intro a b hab
  exact source_separates_edge E Q D hm hc a b hab

def singletonAssignment {p : ℕ} (a : Fin p) : Fin p → Bool :=
  fun a' => decide (a' = a)

lemma function_source_separates_edge {p l : ℕ} {I : Type*}
    (E : Finset (Fin p × Fin l)) (q : I → (Fin p → Bool) → Bool)
    (D : (I → Bool) → (Fin l → Bool) → Bool)
    (hq : ∀ i, Monotone (q i))
    (hm : ∀ y, Monotone (fun u => D u y))
    (hc : ∀ x y, D (fun i => q i x) y =
      decide (∃ a b, (a,b) ∈ E ∧ x a = true ∧ y b = true))
    (a : Fin p) (b : Fin l) (hab : (a,b) ∈ E) :
    ∃ i, q i (singletonAssignment a) = true ∧
      ∀ a', q i (singletonAssignment a') = true → (a',b) ∈ E := by
  classical
  let x := singletonAssignment a
  let y : Fin p → Bool := fun a' => decide ((a',b) ∉ E)
  let z : Fin l → Bool := fun b' => decide (b' = b)
  have ht : D (fun i => q i x) z = true := by
    rw [hc]
    simp only [decide_eq_true_eq]
    exact ⟨a,b,hab,by simp [x,singletonAssignment],by simp [z]⟩
  have hf : D (fun i => q i y) z = false := by
    rw [hc]
    simp only [decide_eq_false_iff_not]
    rintro ⟨a',b',he,hy,hz⟩
    have hb : b' = b := by simpa [z] using hz
    subst b'
    have hy' : (a',b) ∉ E := by simpa [y] using hy
    exact hy' he
  have hex : ∃ i, q i x = true ∧ q i y = false := by
    by_contra hn
    have hle : (fun i => q i x) ≤ (fun i => q i y) := by
      intro i
      change q i x ≤ q i y
      cases hx : q i x <;> cases hy : q i y
      · decide
      · decide
      · exact (hn ⟨i,hx,hy⟩).elim
      · decide
    have h := hm z hle
    change D (fun i => q i x) z ≤ D (fun i => q i y) z at h
    rw [ht,hf] at h
    exact (by decide : ¬ ((true : Bool) ≤ false)) h
  obtain ⟨i,hi,hiy⟩ := hex
  refine ⟨i,hi,?_⟩
  intro a' ha'
  by_contra hn
  have hle : singletonAssignment a' ≤ y := by
    intro c
    by_cases he : c = a'
    · subst c
      simp [singletonAssignment,y,hn]
    · simp [singletonAssignment,he]
  have h := hq i hle
  rw [ha',hiy] at h
  exact (by decide : ¬ ((true : Bool) ≤ false)) h

lemma monochromatic_function_decoder_cover {p l : ℕ} {I : Type*} [Fintype I]
    (E : Finset (Fin p × Fin l)) (q : I → (Fin p → Bool) → Bool)
    (D : (I → Bool) → (Fin l → Bool) → Bool)
    (h4 : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hq : ∀ i, Monotone (q i))
    (hm : ∀ y, Monotone (fun u => D u y))
    (hc : ∀ x y, D (fun i => q i x) y =
      decide (∃ a b, (a,b) ∈ E ∧ x a = true ∧ y b = true)) :
    ∃ S : Finset (Fin (p+l)), S.card ≤ Fintype.card I ∧
      ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  classical
  let Q : I → Finset (Fin p) := fun i =>
    Finset.univ.filter fun a => q i (singletonAssignment a) = true
  apply sources_give_cover E Q h4
  intro a b hab
  obtain ⟨i,hi,hn⟩ := function_source_separates_edge E q D hq hm hc a b hab
  refine ⟨i,by simpa [Q] using hi,?_⟩
  intro a' ha'
  exact hn a' (by simpa [Q] using ha')

end H8Residual

namespace H8Active

def assignmentOf {α : Type*} [DecidableEq α] (S : Finset α) : α → Bool :=
  fun a => decide (a ∈ S)

def dnf {α : Type*} [DecidableEq α] (P : Finset (Finset α)) (x : α → Bool) : Bool :=
  decide (∃ S ∈ P, ∀ a ∈ S, x a = true)

def disjunction {α : Type*} [DecidableEq α] (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∃ a ∈ Q, x a = true)

def conjunction {α ι : Type*} [DecidableEq ι] (P : Finset ι)
    (f : ι → (α → Bool) → Bool) (x : α → Bool) : Bool :=
  decide (∀ i ∈ P, f i x = true)

lemma assignmentOf_le {α : Type*} [DecidableEq α] {S : Finset α} {x : α → Bool}
    (hx : ∀ a ∈ S, x a = true) : assignmentOf S ≤ x := by
  intro a
  by_cases ha : a ∈ S
  · simp [assignmentOf, ha, hx a ha]
  · simp [assignmentOf, ha]

lemma dnf_preserved {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (f g : (α → Bool) → Bool)
    (hg : Monotone g) (hle : ∀ x, g x ≤ f x)
    (hs : ∀ S ∈ P, g (assignmentOf S) = f (assignmentOf S))
    (hf : ∀ x, f x = dnf P x) : ∀ x, g x = dnf P x := by
  intro x
  apply le_antisymm
  · simpa only [hf x] using hle x
  · apply Bool.le_iff_imp.mpr
    intro hx
    obtain ⟨S,hSP,hSx⟩ : ∃ S ∈ P, ∀ a ∈ S, x a = true := by
      simpa only [dnf, decide_eq_true_eq] using hx
    have ht : f (assignmentOf S) = true := by
      rw [hf]
      simp only [dnf, decide_eq_true_eq]
      exact ⟨S,hSP,fun a ha => by simp [assignmentOf,ha]⟩
    have ht' : g (assignmentOf S) = true := by rw [hs S hSP]; exact ht
    exact Bool.le_iff_imp.mp (hg (assignmentOf_le hSx)) ht'

lemma or_bypass_le {α : Type*} (H : α → Bool → Bool) (h k : α → Bool)
    (hH : ∀ x, Monotone (H x)) : ∀ x, H x (k x) ≤ H x (h x || k x) := by
  intro x
  apply hH x
  cases h x <;> cases k x <;> decide

lemma or_bypass_sample {α : Type*} (H : α → Bool → Bool) (h k : α → Bool)
    (x : α) (hx : h x = false) : H x (k x) = H x (h x || k x) := by
  simp [hx]

lemma or_bypass_preserves_dnf {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (H : (α → Bool) → Bool → Bool)
    (h k : (α → Bool) → Bool)
    (hH : ∀ x, Monotone (H x)) (hm : Monotone (fun x => H x (k x)))
    (hz : ∀ S ∈ P, h (assignmentOf S) = false)
    (hf : ∀ x, H x (h x || k x) = dnf P x) :
    ∀ x, H x (k x) = dnf P x := by
  apply dnf_preserved P (fun x => H x (h x || k x)) (fun x => H x (k x))
    hm (or_bypass_le H h k hH)
  · intro S hS
    exact or_bypass_sample H h k (assignmentOf S) (hz S hS)
  · exact hf

lemma pure_disjunction_preserved {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hg : Monotone g) (hle : ∀ x, g x ≤ f x)
    (hs : ∀ a ∈ Q, g (assignmentOf {a}) = f (assignmentOf {a}))
    (hf : ∀ x, f x = disjunction Q x) : ∀ x, g x = disjunction Q x := by
  intro x
  apply le_antisymm
  · simpa only [hf x] using hle x
  · apply Bool.le_iff_imp.mpr
    intro hx
    obtain ⟨a,ha,hxa⟩ : ∃ a ∈ Q, x a = true := by
      simpa only [disjunction,decide_eq_true_eq] using hx
    have ht : f (assignmentOf {a}) = true := by
      rw [hf]
      simp only [disjunction,decide_eq_true_eq]
      exact ⟨a,ha,by simp [assignmentOf]⟩
    have ht' : g (assignmentOf {a}) = true := by rw [hs a ha]; exact ht
    have hsub : assignmentOf {a} ≤ x := assignmentOf_le (by simpa using hxa)
    exact Bool.le_iff_imp.mp (hg hsub) ht'

lemma or_bypass_preserves_pure_disjunction {α : Type*} [DecidableEq α]
    (Q : Finset α) (H : (α → Bool) → Bool → Bool)
    (h k : (α → Bool) → Bool)
    (hH : ∀ x, Monotone (H x)) (hm : Monotone (fun x => H x (k x)))
    (hz : ∀ a ∈ Q, h (assignmentOf {a}) = false)
    (hf : ∀ x, H x (h x || k x) = disjunction Q x) :
    ∀ x, H x (k x) = disjunction Q x := by
  apply pure_disjunction_preserved Q (fun x => H x (h x || k x))
    (fun x => H x (k x)) hm (or_bypass_le H h k hH)
  · intro a ha
    exact or_bypass_sample H h k (assignmentOf {a}) (hz a ha)
  · exact hf

lemma bypassed_pure_root {α : Type*} [DecidableEq α]
    (Q : Finset α) (h k : (α → Bool) → Bool)
    (hk : Monotone k) (hz : ∀ a ∈ Q, h (assignmentOf {a}) = false)
    (hp : ∀ x, (h x || k x) = disjunction Q x) :
    ∀ x, k x = disjunction Q x := by
  exact or_bypass_preserves_pure_disjunction Q (fun _ z => z) h k
    (fun _ => monotone_id) hk hz hp

lemma conjunction_eq_disjunction_factor {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (Q : Finset α) (P : Finset ι) (f : ι → (α → Bool) → Bool)
    (hm : ∀ i ∈ P, Monotone (f i))
    (he : ∀ x, conjunction P f x = disjunction Q x) :
    ∃ i ∈ P, ∀ x, f i x = disjunction Q x := by
  classical
  let outside : α → Bool := fun a => decide (a ∉ Q)
  have hz : conjunction P f outside = false := by
    rw [he]
    simp [disjunction,outside]
  have hn : ¬ ∀ i ∈ P, f i outside = true := by
    simpa only [conjunction,decide_eq_false_iff_not] using hz
  push Not at hn
  obtain ⟨i,hi,hfi⟩ := hn
  refine ⟨i,hi,?_⟩
  intro x
  apply le_antisymm
  · apply Bool.le_iff_imp.mpr
    intro hx
    by_contra hd
    have hnone : ¬ ∃ a ∈ Q, x a = true := by
      simpa only [disjunction,decide_eq_true_eq] using hd
    have hxo : x ≤ outside := by
      intro a
      apply Bool.le_iff_imp.mpr
      intro hxa
      have ha : a ∉ Q := fun haq => hnone ⟨a,haq,hxa⟩
      simp [outside,ha]
    exact hfi (Bool.le_iff_imp.mp (hm i hi hxo) hx)
  · apply Bool.le_iff_imp.mpr
    intro hx
    have hc : conjunction P f x = true := by rw [he]; exact hx
    have hall : ∀ j ∈ P, f j x = true := by
      simpa only [conjunction,decide_eq_true_eq] using hc
    exact hall i hi

lemma or_bypass_sample_of_le {α : Type*} (H : α → Bool → Bool) (h k : α → Bool)
    (x : α) (hx : h x ≤ k x) : H x (k x) = H x (h x || k x) := by
  have he : (h x || k x) = k x := by
    cases hh : h x <;> cases hk : k x
    · rfl
    · rfl
    · exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) (by simpa only [hh,hk] using hx))
    · rfl
  rw [he]

lemma or_bypass_preserves_dnf_of_le {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (H : (α → Bool) → Bool → Bool)
    (h k : (α → Bool) → Bool)
    (hH : ∀ x, Monotone (H x)) (hm : Monotone (fun x => H x (k x)))
    (hs : ∀ S ∈ P, h (assignmentOf S) ≤ k (assignmentOf S))
    (hf : ∀ x, H x (h x || k x) = dnf P x) :
    ∀ x, H x (k x) = dnf P x := by
  apply dnf_preserved P (fun x => H x (h x || k x)) (fun x => H x (k x))
    hm (or_bypass_le H h k hH)
  · intro S hS
    exact or_bypass_sample_of_le H h k (assignmentOf S) (hs S hS)
  · exact hf

lemma or_bypass_preserves_pure_disjunction_of_le {α : Type*} [DecidableEq α]
    (Q : Finset α) (H : (α → Bool) → Bool → Bool)
    (h k : (α → Bool) → Bool)
    (hH : ∀ x, Monotone (H x)) (hm : Monotone (fun x => H x (k x)))
    (hs : ∀ a ∈ Q, h (assignmentOf {a}) ≤ k (assignmentOf {a}))
    (hf : ∀ x, H x (h x || k x) = disjunction Q x) :
    ∀ x, H x (k x) = disjunction Q x := by
  apply pure_disjunction_preserved Q (fun x => H x (h x || k x))
    (fun x => H x (k x)) hm (or_bypass_le H h k hH)
  · intro a ha
    exact or_bypass_sample_of_le H h k (assignmentOf {a}) (hs a ha)
  · exact hf

lemma bypassed_pure_root_of_le {α : Type*} [DecidableEq α]
    (Q : Finset α) (h k : (α → Bool) → Bool)
    (hk : Monotone k) (hs : ∀ a ∈ Q, h (assignmentOf {a}) ≤ k (assignmentOf {a}))
    (hp : ∀ x, (h x || k x) = disjunction Q x) :
    ∀ x, k x = disjunction Q x := by
  exact or_bypass_preserves_pure_disjunction_of_le Q (fun _ z => z) h k
    (fun _ => monotone_id) hk hs hp

end H8Active

namespace H8AndFree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev Node := Finset ℕ × Finset ℕ

def conj (v : ℕ → Bool) (s : Finset ℕ) : Bool :=
  decide (∀ i ∈ s, v i = true)

def step (w : List Bool) (g : Node) : List Bool :=
  w ++ [conj (fun i => w.getD i false) g.1 || conj (fun i => w.getD i false) g.2]

def values (n : ℕ) (gs : List Node) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

def wire (n : ℕ) (gs : List Node) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (values n gs x).getD i false

def term (n : ℕ) (gs : List Node) (s : Finset ℕ) (x : Fin n → Bool) : Bool :=
  conj (fun i => wire n gs i x) s

def Valid (n : ℕ) (gs : List Node) : Prop :=
  ∀ j (hj : j < gs.length),
    gs[j].1.Nonempty ∧ gs[j].2.Nonempty ∧
    (∀ i ∈ gs[j].1, i < n+j) ∧ (∀ i ∈ gs[j].2, i < n+j)

lemma conj_singleton (v : ℕ → Bool) (i : ℕ) : conj v {i} = v i := by
  simp only [conj, Finset.mem_singleton, forall_eq]
  cases v i <;> rfl

lemma conj_union (v : ℕ → Bool) (a b : Finset ℕ) :
    conj v (a ∪ b) = (conj v a && conj v b) := by
  simp only [conj, Finset.mem_union, or_imp, forall_and]
  by_cases ha : ∀ i ∈ a, v i = true <;> by_cases hb : ∀ i ∈ b, v i = true <;> simp [ha,hb]

lemma conj_congr {v w : ℕ → Bool} {s : Finset ℕ}
    (h : ∀ i ∈ s, v i = w i) : conj v s = conj w s := by
  unfold conj
  congr 1
  apply propext
  constructor <;> intro hv i hi
  · rw [← h i hi]; exact hv i hi
  · rw [h i hi]; exact hv i hi

lemma length_fold (gs : List Node) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, step]; omega

lemma values_length (n : ℕ) (gs : List Node) (x : Fin n → Bool) :
    (values n gs x).length = n + gs.length := by
  simp [values, length_fold]

lemma old_wire {n : ℕ} {gs : List Node} {i : ℕ}
    (hi : i < n + gs.length) (g : Node) (x : Fin n → Bool) :
    wire n (gs ++ [g]) i x = wire n gs i x := by
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp [wire, values, List.foldl_append, step, List.getD,
    List.getElem?_append_left (hl ▸ hi : i < (gs.foldl step (List.ofFn x)).length)]

lemma new_wire (n : ℕ) (gs : List Node) (g : Node) (x : Fin n → Bool) :
    wire n (gs ++ [g]) (n + gs.length) x =
      (term n gs g.1 x || term n gs g.2 x) := by
  have hl := values_length n gs x
  simp only [wire, values, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
  simp [← hl, List.getD, term, wire, values]

lemma old_term {n : ℕ} {gs : List Node} {s : Finset ℕ}
    (hs : ∀ i ∈ s, i < n + gs.length) (g : Node) (x : Fin n → Bool) :
    term n (gs ++ [g]) s x = term n gs s x := by
  apply conj_congr
  intro i hi
  exact old_wire (hs i hi) g x

lemma valid_append {n : ℕ} {gs : List Node} (hg : Valid n gs)
    (a b : Finset ℕ) (ha : a.Nonempty) (hb : b.Nonempty)
    (hba : ∀ i ∈ a, i < n + gs.length) (hbb : ∀ i ∈ b, i < n + gs.length) :
    Valid n (gs ++ [(a,b)]) := by
  intro j hj
  by_cases h : j < gs.length
  · simpa [List.getElem_append_left h] using hg j h
  · have he : j = gs.length := by simp at hj; omega
    subst j
    simpa using And.intro ha (And.intro hb (And.intro hba hbb))

def binary (b : Bool) (u v : ℕ) : Gate :=
  ⟨if b then .and else .or, [u,v]⟩

def originalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def original (n : ℕ) (gs : List Gate) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl originalStep (List.ofFn x)).getD i false

def Layout (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), ∃ b u v, gs[i] = binary b u v ∧ u < n+i ∧ v < n+i

lemma original_length (gs : List Gate) (w : List Bool) :
    (gs.foldl originalStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, originalStep]; omega

lemma old_original {n : ℕ} {gs : List Gate} {i : ℕ}
    (hi : i < n + gs.length) (g : Gate) (x : Fin n → Bool) :
    original n (gs ++ [g]) i x = original n gs i x := by
  have hl := original_length gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp [original, List.foldl_append, originalStep, List.getD,
    List.getElem?_append_left (hl ▸ hi : i < (gs.foldl originalStep (List.ofFn x)).length)]

lemma new_original (n : ℕ) (gs : List Gate) (b : Bool) (u v : ℕ) (x : Fin n → Bool) :
    original n (gs ++ [binary b u v]) (n + gs.length) x =
      if b then original n gs u x && original n gs v x
      else original n gs u x || original n gs v x := by
  have hl := original_length gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  cases b <;> simp [original, List.foldl_append, originalStep, binary, GateOp.eval,
    ← hl, List.getD]

def orCount (gs : List Gate) : ℕ := gs.countP fun g =>
  match g.op with | .or => true | _ => false

def Sim (n : ℕ) (gs : List Gate) (hs : List Node) (m : ℕ → Finset ℕ) : Prop :=
  ∀ i < n + gs.length,
    (m i).Nonempty ∧ (∀ j ∈ m i, j < n + hs.length) ∧
    ∀ x : Fin n → Bool, term n hs (m i) x = original n gs i x

lemma exists_normalform (n : ℕ) (gs : List Gate) (hl : Layout n gs) :
    ∃ (hs : List Node) (m : ℕ → Finset ℕ),
      Valid n hs ∧ hs.length = orCount gs ∧ Sim n gs hs m ∧
      ∀ j (hj : j < gs.length), gs[j].op = .or →
        ∃ k < hs.length, m (n+j) = {n+k} := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun i => {i}, ?_, rfl, ?_, ?_⟩
    · intro j hj; simp at hj
    · intro i hi
      have hi' : i < n := by simpa using hi
      refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
      · intro j hj; simpa using Finset.mem_singleton.mp hj ▸ hi'
      · intro x
        simp [term,conj_singleton,wire,values,original]
    · intro j hj; simp at hj
  | append_singleton gs g ih =>
    have hp : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := hl j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    obtain ⟨hs,m,hvalid,hcount,hsim,hroots⟩ := ih hp
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst g
    obtain ⟨hune,hub,husim⟩ := hsim u hu
    obtain ⟨hvne,hvb,hvsim⟩ := hsim v hv
    cases b
    · let mm : ℕ → Finset ℕ := fun i =>
        if i = n + gs.length then {n + hs.length} else m i
      refine ⟨hs ++ [(m u,m v)], mm, valid_append hvalid _ _ hune hvne hub hvb, ?_, ?_, ?_⟩
      · simp [orCount,List.countP_append,binary] at hcount ⊢
        omega
      · intro i hi
        by_cases hold : i < n + gs.length
        · have hne : i ≠ n + gs.length := Nat.ne_of_lt hold
          obtain ⟨hne',hb,heq⟩ := hsim i hold
          simp only [mm,ite_eq_right hne]
          refine ⟨hne', ?_, ?_⟩
          · intro j hj; have hh := hb j hj; simp; omega
          · intro x
            rw [old_term hb,old_original hold]
            exact heq x
        · have hei : i = n + gs.length := by simp at hi; omega
          subst i
          simp only [mm,ite_eq_left rfl]
          refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
          · intro j hj
            have heq := Finset.mem_singleton.mp hj
            simp; omega
          · intro x
            simp only [term,conj_singleton]
            rw [new_wire,new_original]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [husim,hvsim]
      · intro j hj hor
        by_cases hold : j < gs.length
        · have hop : gs[j].op = .or := by simpa [List.getElem_append_left hold] using hor
          obtain ⟨k,hk,hm⟩ := hroots j hold hop
          refine ⟨k, by simp; omega, ?_⟩
          have hne : n+j ≠ n+gs.length := by omega
          simpa only [mm,ite_eq_right hne] using hm
        · have hei : j = gs.length := by simp at hj; omega
          subst j
          exact ⟨hs.length,by simp,by simp [mm]⟩
    · let mm : ℕ → Finset ℕ := fun i =>
        if i = n + gs.length then m u ∪ m v else m i
      refine ⟨hs,mm,hvalid,?_,?_,?_⟩
      · simpa [orCount,List.countP_append,binary] using hcount
      · intro i hi
        by_cases hold : i < n + gs.length
        · have hne : i ≠ n + gs.length := Nat.ne_of_lt hold
          obtain ⟨hne',hb,heq⟩ := hsim i hold
          simp only [mm,ite_eq_right hne]
          refine ⟨hne',hb,?_⟩
          intro x
          rw [old_original hold]
          exact heq x
        · have hei : i = n + gs.length := by simp at hi; omega
          subst i
          simp only [mm,ite_eq_left rfl]
          refine ⟨hune.mono Finset.subset_union_left,?_,?_⟩
          · intro j hj
            rcases Finset.mem_union.mp hj with hj | hj
            · exact hub j hj
            · exact hvb j hj
          · intro x
            simp only [term,conj_union]
            rw [new_original]
            simp only [↓reduceIte]
            exact congrArg₂ (fun a b : Bool => a && b) (husim x) (hvsim x)
      · intro j hj hor
        have hold : j < gs.length := by
          by_contra hn
          have hei : j = gs.length := by simp at hj; omega
          subst j
          simp [binary] at hor
        have hop : gs[j].op = .or := by simpa [List.getElem_append_left hold] using hor
        obtain ⟨k,hk,hm⟩ := hroots j hold hop
        refine ⟨k,hk,?_⟩
        have hne : n+j ≠ n+gs.length := by omega
        simpa only [mm,ite_eq_right hne] using hm

lemma layout_of {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Layout n C.gates := by
  intro i hi
  have hm := List.getElem_mem (l := C.gates) hi
  obtain ⟨u,v,huv⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  have hat : gateAt C i = C.gates[i] := by simp [gateAt,List.getD,hi]
  have hr := h.2.1 i hi
  rw [hat,huv] at hr
  obtain ho | ho := h.1 _ hm
  · exact ⟨true,u,v,by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp),hr v (by simp)⟩
  · exact ⟨false,u,v,by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp),hr v (by simp)⟩

lemma output_bound_of_true {n : ℕ} {C : Circuit}
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    C.output < n + C.gates.length := by
  by_contra! h
  obtain ⟨x,hx⟩ := hpos
  have hlen := original_length C.gates (List.ofFn x)
  simp only [List.length_ofFn] at hlen
  change original n C.gates C.output x = true at hx
  simp [original,List.getD,List.getElem?_eq_none (hlen ▸ h :
    (C.gates.foldl originalStep (List.ofFn x)).length ≤ C.output)] at hx

lemma ao2_flatten {n : ℕ} (C : Circuit) (hC : IsAO2 n C) :
    ∃ (hs : List Node) (m : ℕ → Finset ℕ),
      Valid n hs ∧ hs.length = orCount C.gates ∧
      (∀ i < n + C.gates.length,
        (m i).Nonempty ∧ (∀ j ∈ m i, j < n + hs.length) ∧
        ∀ x : Fin n → Bool,
          term n hs (m i) x = (C.wires (List.ofFn x)).getD i false) ∧
      ∀ j < C.gates.length, (gateAt C j).op = .or →
        ∃ k < hs.length, ∀ x : Fin n → Bool,
          wire n hs (n+k) x = (C.wires (List.ofFn x)).getD (n+j) false := by
  obtain ⟨hs,m,hvalid,hcount,hsim,hroots⟩ := exists_normalform n C.gates (layout_of hC)
  refine ⟨hs,m,hvalid,hcount,hsim,?_⟩
  intro j hj hop
  have hat : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
  rw [hat] at hop
  obtain ⟨k,hk,hm⟩ := hroots j hj hop
  refine ⟨k,hk,?_⟩
  intro x
  have he := (hsim (n+j) (by omega)).2.2 x
  rw [hm] at he
  calc
    wire n hs (n+k) x = original n C.gates (n+j) x := by
      simpa only [term,conj_singleton] using he
    _ = (C.wires (List.ofFn x)).getD (n+j) false := rfl

lemma ao2_flatten_output {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    ∃ (hs : List Node) (s : Finset ℕ),
      Valid n hs ∧ hs.length = orCount C.gates ∧
      s.Nonempty ∧ (∀ i ∈ s, i < n + hs.length) ∧
      (∀ x : Fin n → Bool, term n hs s x = C.eval (List.ofFn x)) ∧
      ∀ j < C.gates.length, (gateAt C j).op = .or →
        ∃ k < hs.length, ∀ x : Fin n → Bool,
          wire n hs (n+k) x = (C.wires (List.ofFn x)).getD (n+j) false := by
  obtain ⟨hs,m,hvalid,hcount,hsim,hroots⟩ := ao2_flatten C hC
  obtain ⟨hne,hb,he⟩ := hsim C.output (output_bound_of_true hpos)
  exact ⟨hs,m C.output,hvalid,hcount,hne,hb,he,hroots⟩

lemma original_append_old {n : ℕ} (gs tail : List Gate) (i : ℕ)
    (hi : i < n + gs.length) (x : Fin n → Bool) :
    original n (gs ++ tail) i x = original n gs i x := by
  induction tail using List.reverseRecOn with
  | nil => simp
  | append_singleton tail g ih =>
    rw [← List.append_assoc,old_original (by simp; omega),ih]

lemma layout_append {n : ℕ} {gs : List Gate} (hl : Layout n gs)
    (b : Bool) (u v : ℕ) (hu : u < n + gs.length) (hv : v < n + gs.length) :
    Layout n (gs ++ [binary b u v]) := by
  intro j hj
  by_cases h : j < gs.length
  · obtain ⟨b',u',v',he,hu',hv'⟩ := hl j h
    exact ⟨b',u',v',by simpa [List.getElem_append_left h] using he,hu',hv'⟩
  · have he : j = gs.length := by simp at hj; omega
    subst j
    exact ⟨b,u,v,by simp,hu,hv⟩

lemma conj_insert (v : ℕ → Bool) (a : ℕ) (s : Finset ℕ) :
    conj v (insert a s) = (v a && conj v s) := by
  rw [← Finset.singleton_union,conj_union,conj_singleton]

lemma compile_conjunction {n : ℕ} (gs : List Gate) (hl : Layout n gs)
    (s : Finset ℕ) (hne : s.Nonempty) (hb : ∀ i ∈ s, i < n + gs.length) :
    ∃ (tail : List Gate) (r : ℕ),
      Layout n (gs ++ tail) ∧ orCount (gs ++ tail) = orCount gs ∧
      r < n + (gs ++ tail).length ∧
      ∀ x : Fin n → Bool, original n (gs ++ tail) r x =
        conj (fun i => original n gs i x) s := by
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
    have hab : a < n + gs.length := hb a (by simp)
    by_cases hs : s.Nonempty
    · obtain ⟨tail,r,hlt,hct,hrt,het⟩ := ih hs (fun i hi => hb i (by simp [hi]))
      refine ⟨tail ++ [binary true a r],n + (gs ++ tail).length,?_,?_,?_,?_⟩
      · rw [← List.append_assoc]
        exact layout_append hlt true a r (by simp; omega) hrt
      · rw [← List.append_assoc]
        simpa [orCount,List.countP_append,binary] using hct
      · simp
      · intro x
        rw [← List.append_assoc,new_original]
        simp only [↓reduceIte]
        rw [original_append_old gs tail a hab,het,conj_insert]
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      refine ⟨[],a,by simpa using hl,by simp,by simpa using hab,?_⟩
      intro x
      simp [conj_singleton]

lemma conj_image (v : ℕ → Bool) (m : ℕ → ℕ) (s : Finset ℕ) :
    conj v (s.image m) = conj (fun i => v (m i)) s := by
  unfold conj
  congr 1
  apply propext
  constructor
  · intro h i hi
    exact h (m i) (Finset.mem_image_of_mem m hi)
  · intro h j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact h i hi

def ReverseSim (n : ℕ) (hs : List Node) (gs : List Gate) (m : ℕ → ℕ) : Prop :=
  ∀ i < n + hs.length, m i < n + gs.length ∧
    ∀ x : Fin n → Bool, original n gs (m i) x = wire n hs i x

lemma exists_realization (n : ℕ) (hs : List Node) (hv : Valid n hs) :
    ∃ (gs : List Gate) (m : ℕ → ℕ),
      Layout n gs ∧ orCount gs = hs.length ∧ ReverseSim n hs gs m ∧
      ∀ j < hs.length, ∃ (k : ℕ) (hk : k < gs.length), m (n+j) = n+k ∧ gs[k].op = .or := by
  induction hs using List.reverseRecOn with
  | nil =>
    refine ⟨[],id,?_,rfl,?_,?_⟩
    · intro j hj; simp at hj
    · intro i hi
      refine ⟨hi,?_⟩
      intro x
      rfl
    · intro j hj; simp at hj
  | append_singleton hs node ih =>
    have hp : Valid n hs := by
      intro j hj
      have hh := hv j (by simp; omega)
      rw [List.getElem_append_left hj] at hh
      exact hh
    obtain ⟨gs,m,hgl,hgc,hgs,hgr⟩ := ih hp
    obtain ⟨ha,hb,hba,hbb⟩ := hv hs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at ha hb hba hbb
    have hma : ∀ i ∈ node.1.image m, i < n + gs.length := by
      intro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact (hgs j (hba j hj)).1
    obtain ⟨t1,r1,hl1,hc1,hr1,he1⟩ :=
      compile_conjunction gs hgl (node.1.image m) (ha.image m) hma
    have hmb : ∀ i ∈ node.2.image m, i < n + (gs ++ t1).length := by
      intro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      have hh := (hgs j (hbb j hj)).1
      simp; omega
    obtain ⟨t2,r2,hl2,hc2,hr2,he2⟩ :=
      compile_conjunction (gs ++ t1) hl1 (node.2.image m) (hb.image m) hmb
    let mm : ℕ → ℕ := fun i =>
      if i = n + hs.length then n + ((gs ++ t1) ++ t2).length else m i
    refine ⟨((gs ++ t1) ++ t2) ++ [binary false r1 r2],mm,?_,?_,?_,?_⟩
    · exact layout_append hl2 false r1 r2 (by simp at hr1 ⊢; omega) hr2
    · have hh : orCount (((gs ++ t1) ++ t2) ++ [binary false r1 r2]) =
          orCount ((gs ++ t1) ++ t2) + 1 := by simp [orCount,List.countP_append,binary,Nat.add_assoc]
      rw [hh,hc2,hc1,hgc]
      simp
    · intro i hi
      by_cases hold : i < n + hs.length
      · obtain ⟨hbound,he⟩ := hgs i hold
        have hne : i ≠ n + hs.length := Nat.ne_of_lt hold
        simp only [mm,ite_eq_right hne]
        refine ⟨by simp; omega,?_⟩
        intro x
        rw [old_original (by simp; omega),original_append_old (gs ++ t1) t2 (m i) (by simp; omega),
          original_append_old gs t1 (m i) hbound,old_wire hold]
        exact he x
      · have hei : i = n + hs.length := by simp at hi; omega
        subst i
        simp only [mm,ite_eq_left rfl]
        refine ⟨by simp,?_⟩
        intro x
        rw [new_original,new_wire]
        simp only [Bool.false_eq_true,↓reduceIte]
        rw [original_append_old (gs ++ t1) t2 r1 hr1,he1,he2]
        apply congrArg₂ (fun a b : Bool => a || b)
        · rw [conj_image]
          apply conj_congr
          intro j hj
          exact (hgs j (hba j hj)).2 x
        · rw [conj_image]
          apply conj_congr
          intro j hj
          rw [original_append_old gs t1 (m j) (hgs j (hbb j hj)).1]
          exact (hgs j (hbb j hj)).2 x
    · intro j hj
      by_cases hold : j < hs.length
      · obtain ⟨k,hk,hm,hop⟩ := hgr j hold
        refine ⟨k,by simp; omega,?_,?_⟩
        · have hne : n+j ≠ n+hs.length := by omega
          simpa only [mm,ite_eq_right hne] using hm
        · rw [List.getElem_append_left (by simp; omega),
            List.getElem_append_left (by simp; omega),List.getElem_append_left hk]
          exact hop
      · have hei : j = hs.length := by simp at hj; omega
        subst j
        refine ⟨((gs ++ t1) ++ t2).length,by simp,by simp [mm],?_⟩
        simp [binary]

lemma layout_isAO2 {n : ℕ} {gs : List Gate} (out : ℕ)
    (h : Layout n gs) : IsAO2 n ⟨gs,out⟩ := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    obtain ⟨b,u,v,he,hu,hv⟩ := h i hi
    rw [he]
    cases b <;> simp [binary]
  · intro i hi w hw
    change i < gs.length at hi
    obtain ⟨b,u,v,he,hu,hv⟩ := h i hi
    simp [gateAt,List.getD,hi,he,binary] at hw
    rcases hw with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    obtain ⟨b,u,v,he,hu,hv⟩ := h i hi
    simp [he,binary]

lemma realize_output {n : ℕ} (hs : List Node) (hv : Valid n hs)
    (s : Finset ℕ) (hne : s.Nonempty) (hb : ∀ i ∈ s, i < n + hs.length) :
    ∃ C : Circuit, IsAO2 n C ∧ orCount C.gates = hs.length ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = term n hs s x) ∧
      ∀ j < hs.length, ∃ k < C.gates.length, (gateAt C k).op = .or ∧
        ∀ x : Fin n → Bool,
          (C.wires (List.ofFn x)).getD (n+k) false = wire n hs (n+j) x := by
  obtain ⟨gs,m,hgl,hgc,hgs,hgr⟩ := exists_realization n hs hv
  have hmb : ∀ i ∈ s.image m, i < n + gs.length := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact (hgs j (hb j hj)).1
  obtain ⟨tail,r,hlt,hct,hrt,het⟩ := compile_conjunction gs hgl (s.image m) (hne.image m) hmb
  refine ⟨⟨gs ++ tail,r⟩,layout_isAO2 r hlt,hct.trans hgc,?_,?_⟩
  · intro x
    change original n (gs ++ tail) r x = term n hs s x
    rw [het,conj_image]
    apply conj_congr
    intro i hi
    exact (hgs i (hb i hi)).2 x
  · intro j hj
    obtain ⟨k,hk,hm,hop⟩ := hgr j hj
    refine ⟨k,by simp; omega,?_,?_⟩
    · simp only [gateAt]
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp; omega)]
      simpa [List.getElem_append_left hk] using hop
    · intro x
      change original n (gs ++ tail) (n+k) x = wire n hs (n+j) x
      rw [original_append_old gs tail (n+k) (by omega)]
      have he := (hgs (n+j) (by omega)).2 x
      rw [hm] at he
      exact he

end H8AndFree

namespace H8OrPatch

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4970.H8AndFree

lemma getD_le {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) (i : ℕ) :
    a.getD i false ≤ b.getD i false := by
  induction h generalizing i with
  | nil => simp
  | @cons a b xs ys hab hxy ih =>
    cases i with
    | zero => simpa [List.getD] using hab
    | succ i => simpa [List.getD] using ih i

lemma bool_and_le {a b c d : Bool} (h1 : a ≤ c) (h2 : b ≤ d) :
    (a && b) ≤ (c && d) := by
  apply Bool.le_iff_imp.mpr
  intro h
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨Bool.le_iff_imp.mp h1 ha,Bool.le_iff_imp.mp h2 hb⟩

lemma bool_or_le {a b c d : Bool} (h1 : a ≤ c) (h2 : b ≤ d) :
    (a || b) ≤ (c || d) := by
  apply Bool.le_iff_imp.mpr
  intro h
  rcases Bool.or_eq_true_iff.mp h with ha | hb
  · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.le_iff_imp.mp h1 ha))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.le_iff_imp.mp h2 hb))

lemma step_binary (w : List Bool) (b : Bool) (u v : ℕ) :
    originalStep w (binary b u v) = w ++
      [if b then w.getD u false && w.getD v false else w.getD u false || w.getD v false] := by
  cases b <;> simp [originalStep,binary,GateOp.eval]

lemma step_mono {w z : List Bool} (h : List.Forall₂ (· ≤ ·) w z)
    (b : Bool) (u v : ℕ) :
    List.Forall₂ (· ≤ ·) (originalStep w (binary b u v)) (originalStep z (binary b u v)) := by
  rw [step_binary,step_binary]
  apply List.rel_append h
  apply List.Forall₂.cons
  · cases b
    · exact bool_or_le (getD_le h u) (getD_le h v)
    · exact bool_and_le (getD_le h u) (getD_le h v)
  · exact List.Forall₂.nil

lemma fold_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, ∃ b u v, g = binary b u v)
    {w z : List Bool} (h : List.Forall₂ (· ≤ ·) w z) :
    List.Forall₂ (· ≤ ·) (gs.foldl originalStep w) (gs.foldl originalStep z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨b,u,v,rfl⟩ := hg g (by simp)
    apply ih (fun g hm => hg g (by simp [hm]))
    exact step_mono h b u v

lemma replace_step_le (w : List Bool) (u v : ℕ) :
    List.Forall₂ (· ≤ ·) (originalStep w (binary true v v))
      (originalStep w (binary false u v)) := by
  rw [step_binary,step_binary]
  apply List.rel_append (List.forall₂_refl w)
  apply List.Forall₂.cons
  · cases hu : w.getD u false <;> cases hv : w.getD v false <;> decide
  · exact List.Forall₂.nil

lemma replace_step_eq (w : List Bool) (u v : ℕ)
    (h : w.getD u false ≤ w.getD v false) :
    originalStep w (binary true v v) = originalStep w (binary false u v) := by
  rw [step_binary,step_binary]
  cases hu : w.getD u false <;> cases hv : w.getD v false <;> simp_all [Bool.le_iff_imp]

lemma patch_le (n : ℕ) (pre post : List Gate) (u v i : ℕ)
    (hp : ∀ g ∈ post, ∃ b a c, g = binary b a c) (x : Fin n → Bool) :
    original n (pre ++ [binary true v v] ++ post) i x ≤
      original n (pre ++ [binary false u v] ++ post) i x := by
  have h := getD_le (fold_mono post hp
    (replace_step_le (pre.foldl originalStep (List.ofFn x)) u v)) i
  simpa only [original,List.foldl_append,List.foldl_cons,List.foldl_nil] using h

lemma patch_eq_on (n : ℕ) (pre post : List Gate) (u v i : ℕ) (x : Fin n → Bool)
    (h : original n pre u x ≤ original n pre v x) :
    original n (pre ++ [binary true v v] ++ post) i x =
      original n (pre ++ [binary false u v] ++ post) i x := by
  have he := replace_step_eq (pre.foldl originalStep (List.ofFn x)) u v h
  simp only [original,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [he]

lemma patch_count (pre post : List Gate) (u v : ℕ) :
    orCount (pre ++ [binary true v v] ++ post) + 1 =
      orCount (pre ++ [binary false u v] ++ post) := by
  simp [orCount,List.countP_append,binary]
  omega

lemma binary_only_of_layout {n : ℕ} {gs : List Gate} (hl : Layout n gs) :
    ∀ g ∈ gs, ∃ b u v, g = binary b u v := by
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
  obtain ⟨b,u,v,he,hu,hv⟩ := hl i hi
  exact ⟨b,u,v,he⟩

lemma original_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, ∃ b u v, g = binary b u v) (i : ℕ) :
    Monotone (fun x : Fin n → Bool => original n gs i x) := by
  intro x y hxy
  have hinit : List.Forall₂ (· ≤ ·) (List.ofFn x) (List.ofFn y) := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro j hj hj'
    have hjn : j < n := by simpa using hj
    simpa using hxy ⟨j,hjn⟩
  exact getD_le (fold_mono gs hg hinit) i

lemma layout_prefix {n : ℕ} (pre tail : List Gate)
    (h : Layout n (pre ++ tail)) : Layout n pre := by
  intro i hi
  obtain ⟨b,u,v,he,hu,hv⟩ := h i (by simp; omega)
  exact ⟨b,u,v,(List.getElem_append_left hi).symm.trans he,hu,hv⟩

lemma layout_replace_prefix {n : ℕ} (old new tail : List Gate)
    (hlen : old.length = new.length)
    (hold : Layout n (old ++ tail)) (hnew : Layout n new) :
    Layout n (new ++ tail) := by
  intro i hi
  by_cases hsmall : i < new.length
  · obtain ⟨b,u,v,he,hu,hv⟩ := hnew i hsmall
    exact ⟨b,u,v,by simpa [List.getElem_append_left hsmall] using he,hu,hv⟩
  · have hiold : i < (old ++ tail).length := by simpa [List.length_append,hlen] using hi
    have hbignew : new.length ≤ i := by omega
    have hbigold : old.length ≤ i := by omega
    have hgate : (new ++ tail)[i] = (old ++ tail)[i] := by
      rw [List.getElem_append_right hbignew,List.getElem_append_right hbigold]
      simp only [hlen]
    obtain ⟨b,u,v,he,hu,hv⟩ := hold i hiold
    exact ⟨b,u,v,hgate.trans he,hu,hv⟩

lemma patch_layout {n : ℕ} (pre post : List Gate) (u v : ℕ)
    (h : Layout n (pre ++ [binary false u v] ++ post))
    (hv : v < n + pre.length) :
    Layout n (pre ++ [binary true v v] ++ post) := by
  apply layout_replace_prefix (pre ++ [binary false u v]) (pre ++ [binary true v v]) post
    (by simp) h
  apply layout_append (layout_prefix pre ([binary false u v] ++ post) (by simpa [List.append_assoc] using h))
  · exact hv
  · exact hv

lemma patch_preserves_dnf_and_pure_roots {n : ℕ}
    (pre post : List Gate) (u v out : ℕ)
    (h : Layout n (pre ++ [binary false u v] ++ post))
    (hv : v < n + pre.length) (P : Finset (Finset (Fin n)))
    (hdnf : ∀ x : Fin n → Bool,
      original n (pre ++ [binary false u v] ++ post) out x = H8Active.dnf P x)
    (hdom : ∀ S ∈ P, original n pre u (H8Active.assignmentOf S) ≤
      original n pre v (H8Active.assignmentOf S))
    (hsing : ∀ a : Fin n, original n pre u (H8Active.assignmentOf {a}) ≤
      original n pre v (H8Active.assignmentOf {a})) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      D.size = (pre ++ [binary false u v] ++ post).length ∧
      orCount D.gates + 1 = orCount (pre ++ [binary false u v] ++ post) ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = H8Active.dnf P x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card →
        (∃ i < n + (pre ++ [binary false u v] ++ post).length,
          ∀ x : Fin n → Bool, original n (pre ++ [binary false u v] ++ post) i x =
            H8Active.disjunction Q x) →
        ∃ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = .or ∧
          ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n+j) false =
            H8Active.disjunction Q x := by
  let old := pre ++ [binary false u v] ++ post
  let neu := pre ++ [binary true v v] ++ post
  have hn : Layout n neu := patch_layout pre post u v h hv
  have hp : ∀ g ∈ post, ∃ b a c, g = binary b a c := by
    intro g hg
    apply binary_only_of_layout h g
    simp [hg]
  have hm (i : ℕ) : Monotone (fun x : Fin n → Bool => original n neu i x) :=
    original_mono neu (binary_only_of_layout hn) i
  have hle (i : ℕ) (x : Fin n → Bool) : original n neu i x ≤ original n old i x :=
    patch_le n pre post u v i hp x
  have he (i : ℕ) (x : Fin n → Bool) (hd : original n pre u x ≤ original n pre v x) :
      original n neu i x = original n old i x := patch_eq_on n pre post u v i x hd
  let D : Circuit := ⟨neu,out⟩
  have hD : PEqualNP.TopForm.IsAO2 n D := layout_isAO2 out hn
  refine ⟨D,hD,?_,patch_count pre post u v,?_,?_⟩
  · simp [D,neu,Circuit.size]
  · have ho := H8Active.dnf_preserved P (original n old out) (original n neu out)
      (hm out) (hle out) (fun S hS => he out _ (hdom S hS)) hdnf
    exact ho
  · intro Q hQ hw
    obtain ⟨i,hi,hiQ⟩ := hw
    have hpure := H8Active.pure_disjunction_preserved Q (original n old i) (original n neu i)
      (hm i) (hle i) (fun a _ => he i _ (hsing a)) hiQ
    have hib : i < n + D.gates.length := by simpa [D,neu] using hi
    have hfun : H8Tagged.W n D.gates i = H8Tagged.OrOf Q := by
      funext x
      apply propext
      change original n neu i x = true ↔ _
      rw [hpure]
      simp [H8Active.disjunction,H8Tagged.OrOf]
    obtain ⟨j,hj,hop,hroot⟩ := H8Roots.pure_or_root D.gates (H8Tagged.layout_of hD) Q hQ ⟨i,hib,hfun⟩
    refine ⟨j,hj,?_,?_⟩
    · simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD,hj] using hop
    · intro x
      have hr := Iff.of_eq (congrFun hroot x)
      change ((D.wires (List.ofFn x)).getD (n+j) false = true) ↔ (∃ a ∈ Q, x a = true) at hr
      have hb : ((D.wires (List.ofFn x)).getD (n+j) false = true) ↔
          H8Active.disjunction Q x = true := by
        simpa only [H8Active.disjunction,decide_eq_true_eq] using hr
      exact le_antisymm (Bool.le_iff_imp.mpr hb.mp) (Bool.le_iff_imp.mpr hb.mpr)

end H8OrPatch

namespace H8OrPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970.H8AndFree

def HasPureOr (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) : Prop :=
  ∃ j < C.gates.length, (gateAt C j).op = .or ∧
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+j) false = H8Active.disjunction Q x

def PreservesPureOr (n : ℕ) (C D : Circuit) : Prop :=
  ∀ Q : Finset (Fin n), 2 ≤ Q.card → HasPureOr n C Q → HasPureOr n D Q

def Tests {n : ℕ} (P : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  P ∪ Finset.univ.image (fun a : Fin n => {a})

lemma preserves_refl (n : ℕ) (C : Circuit) : PreservesPureOr n C C := by
  intro Q hQ hh
  exact hh

lemma preserves_trans {n : ℕ} {C D K : Circuit}
    (h1 : PreservesPureOr n C D) (h2 : PreservesPureOr n D K) : PreservesPureOr n C K := by
  intro Q hQ hh
  exact h2 Q hQ (h1 Q hQ hh)

lemma hasPureOr_of_wire {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card) (i : ℕ) (hi : i < n + C.gates.length)
    (hfun : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false = H8Active.disjunction Q x) :
    HasPureOr n C Q := by
  have hp : H8Tagged.W n C.gates i = H8Tagged.OrOf Q := by
    funext x
    apply propext
    change ((C.wires (List.ofFn x)).getD i false = true) ↔ _
    rw [hfun]
    simp [H8Active.disjunction,H8Tagged.OrOf]
  obtain ⟨j,hj,hop,hroot⟩ := H8Roots.pure_or_root C.gates (H8Tagged.layout_of hC) Q hQ ⟨i,hi,hp⟩
  refine ⟨j,hj,?_,?_⟩
  · simpa [gateAt,List.getD,hj] using hop
  · intro x
    have hr := Iff.of_eq (congrFun hroot x)
    change ((C.wires (List.ofFn x)).getD (n+j) false = true) ↔ (∃ a ∈ Q, x a = true) at hr
    have hb : ((C.wires (List.ofFn x)).getD (n+j) false = true) ↔
        H8Active.disjunction Q x = true := by
      simpa only [H8Active.disjunction,decide_eq_true_eq] using hr
    exact le_antisymm (Bool.le_iff_imp.mpr hb.mp) (Bool.le_iff_imp.mpr hb.mpr)

lemma layout_binary_bounds {n : ℕ} (pre post : List Gate) (b : Bool) (u v : ℕ)
    (h : Layout n (pre ++ [binary b u v] ++ post)) : u < n + pre.length ∧ v < n + pre.length := by
  obtain ⟨b',a,c,he,ha,hc⟩ := h pre.length (by simp)
  have hh : binary b u v = binary b' a c := by simpa using he
  have hinputs := congrArg Gate.inputs hh
  have hpair : u = a ∧ v = c := by simpa [binary] using hinputs
  rcases hpair with ⟨rfl,rfl⟩
  exact ⟨ha,hc⟩

lemma patch_circuit {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x)
    (pre post : List Gate) (u v : ℕ) (he : C.gates = pre ++ [binary false u v] ++ post)
    (hdom : ∀ S ∈ Tests P, original n pre u (H8Active.assignmentOf S) ≤
      original n pre v (H8Active.assignmentOf S)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = H8Active.dnf P x) ∧
      orCount D.gates + 1 = orCount C.gates ∧ PreservesPureOr n C D := by
  have hl : Layout n (pre ++ [binary false u v] ++ post) := by rw [← he]; exact layout_of hC
  have hv := (layout_binary_bounds pre post false u v hl).2
  have hd : ∀ x : Fin n → Bool,
      original n (pre ++ [binary false u v] ++ post) C.output x = H8Active.dnf P x := by
    intro x
    rw [← he]
    exact hF x
  obtain ⟨D,hD,hsize,hcount,hout,hroots⟩ := patch_preserves_dnf_and_pure_roots pre post u v C.output hl hv P hd
    (fun S hS => hdom S (Finset.mem_union_left _ hS))
    (fun a => hdom {a} (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))))
  refine ⟨D,hD,hout,?_,?_⟩
  · simpa [he] using hcount
  · intro Q hQ hh
    obtain ⟨j,hj,hop,hjQ⟩ := hh
    apply hroots Q hQ
    refine ⟨n+j,by rw [← he]; omega,?_⟩
    intro x
    rw [← he]
    exact hjQ x

lemma swap_original (n : ℕ) (pre post : List Gate) (u v i : ℕ) (x : Fin n → Bool) :
    original n (pre ++ [binary false u v] ++ post) i x =
      original n (pre ++ [binary false v u] ++ post) i x := by
  simp only [original,List.foldl_append,List.foldl_cons,List.foldl_nil,step_binary]
  simp only [Bool.false_eq_true,↓reduceIte,Bool.or_comm]

lemma swap_circuit {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x)
    (pre post : List Gate) (u v : ℕ) (he : C.gates = pre ++ [binary false u v] ++ post) :
    ∃ D : Circuit, D.gates = pre ++ [binary false v u] ++ post ∧
      PEqualNP.TopForm.IsAO2 n D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = H8Active.dnf P x) ∧
      orCount D.gates = orCount C.gates ∧ PreservesPureOr n C D := by
  have hl : Layout n (pre ++ [binary false u v] ++ post) := by rw [← he]; exact layout_of hC
  obtain ⟨hu,hv⟩ := layout_binary_bounds pre post false u v hl
  have hn : Layout n (pre ++ [binary false v u] ++ post) := by
    apply layout_replace_prefix (pre ++ [binary false u v]) (pre ++ [binary false v u]) post (by simp) hl
    exact layout_append (layout_prefix pre ([binary false u v] ++ post) (by simpa [List.append_assoc] using hl)) false v u hv hu
  let D : Circuit := ⟨pre ++ [binary false v u] ++ post,C.output⟩
  have hD : PEqualNP.TopForm.IsAO2 n D := layout_isAO2 C.output hn
  have hw (i : ℕ) (x : Fin n → Bool) :
      (D.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
    change original n (pre ++ [binary false v u] ++ post) i x = original n C.gates i x
    rw [he]
    exact swap_original n pre post v u i x
  refine ⟨D,rfl,hD,?_,?_,?_⟩
  · intro x
    change (D.wires (List.ofFn x)).getD C.output false = _
    rw [hw]
    exact hF x
  · simp [D,he,orCount,List.countP_append,binary]
  · intro Q hQ hh
    obtain ⟨j,hj,hop,hjQ⟩ := hh
    apply hasPureOr_of_wire D hD Q hQ (n+j)
    · simp [D,he] at hj ⊢
      omega
    · intro x
      rw [hw]
      exact hjQ x

lemma dominates_of_no_private {α : Type*} (T : Finset α) (f g : α → Bool)
    (h : ¬ ∃ a ∈ T, f a = true ∧ g a = false) : ∀ a ∈ T, f a ≤ g a := by
  intro a ha
  apply Bool.le_iff_imp.mpr
  intro hf
  cases hg : g a with
  | false => exact (h ⟨a,ha,hf,hg⟩).elim
  | true => rfl

lemma exists_private_minimum {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = H8Active.dnf P x) ∧
      PreservesPureOr n C D ∧ orCount D.gates ≤ orCount C.gates ∧
      ∀ (pre post : List Gate) (u v : ℕ), D.gates = pre ++ [binary false u v] ++ post →
        (∃ S ∈ Tests P, original n pre u (H8Active.assignmentOf S) = true ∧
          original n pre v (H8Active.assignmentOf S) = false) ∧
        (∃ S ∈ Tests P, original n pre v (H8Active.assignmentOf S) = true ∧
          original n pre u (H8Active.assignmentOf S) = false) := by
  classical
  let Good : Circuit → Prop := fun D => PEqualNP.TopForm.IsAO2 n D ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = H8Active.dnf P x) ∧ PreservesPureOr n C D
  have hgood : Good C := ⟨hC,hF,preserves_refl n C⟩
  have hex : ∃ k : ℕ, ∃ D : Circuit, Good D ∧ orCount D.gates = k :=
    ⟨orCount C.gates,C,hgood,rfl⟩
  obtain ⟨D,hD,hcount⟩ := Nat.find_spec hex
  have hmin (K : Circuit) (hK : Good K) : orCount D.gates ≤ orCount K.gates := by
    rw [hcount]
    exact Nat.find_min' hex ⟨K,hK,rfl⟩
  refine ⟨D,hD.1,hD.2.1,hD.2.2,hmin C hgood,?_⟩
  intro pre post u v he
  constructor
  · by_contra hn
    have hdom := dominates_of_no_private (Tests P)
      (fun S => original n pre u (H8Active.assignmentOf S))
      (fun S => original n pre v (H8Active.assignmentOf S)) hn
    obtain ⟨K,hK,hKF,hKcount,hKroots⟩ := patch_circuit D hD.1 P hD.2.1 pre post u v he hdom
    have hk : orCount D.gates ≤ orCount K.gates :=
      hmin K ⟨hK,hKF,preserves_trans hD.2.2 hKroots⟩
    omega
  · by_contra hn
    have hdom := dominates_of_no_private (Tests P)
      (fun S => original n pre v (H8Active.assignmentOf S))
      (fun S => original n pre u (H8Active.assignmentOf S)) hn
    obtain ⟨X,hXg,hX,hXF,hXcount,hXroots⟩ := swap_circuit D hD.1 P hD.2.1 pre post u v he
    obtain ⟨K,hK,hKF,hKcount,hKroots⟩ := patch_circuit X hX P hXF pre post v u hXg hdom
    have hk : orCount D.gates ≤ orCount K.gates :=
      hmin K ⟨hK,hKF,preserves_trans (preserves_trans hD.2.2 hXroots) hKroots⟩
    omega

end H8OrPatch

namespace H8AndFree

open PEqualNP.CircuitLowerBounds

def PrivateOriginal (n : ℕ) (gs : List Gate) (T : Set (Fin n → Bool)) : Prop :=
  ∀ j (hj : j < gs.length) u v, gs[j] = binary false u v →
    u < n+j → v < n+j →
    (∃ x ∈ T, original n gs u x = true ∧ original n gs v x = false) ∧
    (∃ x ∈ T, original n gs v x = true ∧ original n gs u x = false)

def PrivateNormal (n : ℕ) (gs : List Node) (T : Set (Fin n → Bool)) : Prop :=
  ∀ j (hj : j < gs.length),
    (∃ x ∈ T, term n gs gs[j].1 x = true ∧ term n gs gs[j].2 x = false) ∧
    (∃ x ∈ T, term n gs gs[j].2 x = true ∧ term n gs gs[j].1 x = false)

lemma private_original_prefix {n : ℕ} {gs : List Gate} (g : Gate)
    (T : Set (Fin n → Bool)) (hp : PrivateOriginal n (gs ++ [g]) T) :
    PrivateOriginal n gs T := by
  intro j hj u v he hu hv
  have hj' : j < (gs ++ [g]).length := by simp; omega
  have hej : (gs ++ [g])[j] = binary false u v := by
    simpa only [List.getElem_append_left hj] using he
  have hu' : u < n + gs.length := by omega
  have hv' : v < n + gs.length := by omega
  simpa only [old_original hu',old_original hv'] using
    hp j (by simp; omega) u v hej hu hv

lemma private_normal_append {n : ℕ} {gs : List Node}
    (T : Set (Fin n → Bool)) (hv : Valid n gs) (hp : PrivateNormal n gs T)
    (a b : Finset ℕ)
    (ha : ∀ i ∈ a, i < n + gs.length) (hb : ∀ i ∈ b, i < n + gs.length)
    (hnew : (∃ x ∈ T, term n gs a x = true ∧ term n gs b x = false) ∧
      (∃ x ∈ T, term n gs b x = true ∧ term n gs a x = false)) :
    PrivateNormal n (gs ++ [(a,b)]) T := by
  intro j hj
  by_cases hold : j < gs.length
  · have ha' : ∀ i ∈ gs[j].1, i < n + gs.length := by
      intro i hi
      have hh := (hv j hold).2.2.1 i hi
      omega
    have hb' : ∀ i ∈ gs[j].2, i < n + gs.length := by
      intro i hi
      have hh := (hv j hold).2.2.2 i hi
      omega
    simpa only [List.getElem_append_left hold,old_term ha',old_term hb'] using hp j hold
  · have he : j = gs.length := by simp at hj; omega
    subst j
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
    change (∃ x ∈ T, term n (gs ++ [(a,b)]) a x = true ∧
      term n (gs ++ [(a,b)]) b x = false) ∧
      (∃ x ∈ T, term n (gs ++ [(a,b)]) b x = true ∧
      term n (gs ++ [(a,b)]) a x = false)
    simpa only [old_term ha,old_term hb] using hnew

lemma exists_normalform_private (n : ℕ) (gs : List Gate) (T : Set (Fin n → Bool))
    (hl : Layout n gs) (hpriv : PrivateOriginal n gs T) :
    ∃ (hs : List Node) (m : ℕ → Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs T ∧ hs.length = orCount gs ∧ Sim n gs hs m ∧
      ∀ j (hj : j < gs.length), gs[j].op = .or →
        ∃ k < hs.length, m (n+j) = {n+k} := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun i => {i}, ?_, ?_, rfl, ?_, ?_⟩
    · intro j hj; simp at hj
    · intro j hj; simp at hj
    · intro i hi
      have hi' : i < n := by simpa using hi
      refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
      · intro j hj; simpa using Finset.mem_singleton.mp hj ▸ hi'
      · intro x
        simp [term,conj_singleton,wire,values,original]
    · intro j hj; simp at hj
  | append_singleton gs g ih =>
    have hp : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := hl j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    have hpp := private_original_prefix g T hpriv
    obtain ⟨hs,m,hvalid,hprivate,hcount,hsim,hroots⟩ := ih hp hpp
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst g
    obtain ⟨hune,hub,husim⟩ := hsim u hu
    obtain ⟨hvne,hvb,hvsim⟩ := hsim v hv
    cases b
    · let mm : ℕ → Finset ℕ := fun i =>
        if i = n + gs.length then {n + hs.length} else m i
      have hnew : (∃ x ∈ T, term n hs (m u) x = true ∧ term n hs (m v) x = false) ∧
          (∃ x ∈ T, term n hs (m v) x = true ∧ term n hs (m u) x = false) := by
        simpa only [husim,hvsim,old_original hu,old_original hv] using
          hpriv gs.length (by simp) u v (by simp) hu hv
      refine ⟨hs ++ [(m u,m v)], mm, valid_append hvalid _ _ hune hvne hub hvb,
        private_normal_append T hvalid hprivate _ _ hub hvb hnew, ?_, ?_, ?_⟩
      · simp [orCount,List.countP_append,binary] at hcount ⊢
        omega
      · intro i hi
        by_cases hold : i < n + gs.length
        · have hne : i ≠ n + gs.length := Nat.ne_of_lt hold
          obtain ⟨hne',hb,heq⟩ := hsim i hold
          simp only [mm,ite_eq_right hne]
          refine ⟨hne', ?_, ?_⟩
          · intro j hj; have hh := hb j hj; simp; omega
          · intro x
            rw [old_term hb,old_original hold]
            exact heq x
        · have hei : i = n + gs.length := by simp at hi; omega
          subst i
          simp only [mm,ite_eq_left rfl]
          refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
          · intro j hj
            have heq := Finset.mem_singleton.mp hj
            simp; omega
          · intro x
            simp only [term,conj_singleton]
            rw [new_wire,new_original]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [husim,hvsim]
      · intro j hj hor
        by_cases hold : j < gs.length
        · have hop : gs[j].op = .or := by simpa [List.getElem_append_left hold] using hor
          obtain ⟨k,hk,hm⟩ := hroots j hold hop
          refine ⟨k, by simp; omega, ?_⟩
          have hne : n+j ≠ n+gs.length := by omega
          simpa only [mm,ite_eq_right hne] using hm
        · have hei : j = gs.length := by simp at hj; omega
          subst j
          exact ⟨hs.length,by simp,by simp [mm]⟩
    · let mm : ℕ → Finset ℕ := fun i =>
        if i = n + gs.length then m u ∪ m v else m i
      refine ⟨hs,mm,hvalid,hprivate,?_,?_,?_⟩
      · simpa [orCount,List.countP_append,binary] using hcount
      · intro i hi
        by_cases hold : i < n + gs.length
        · have hne : i ≠ n + gs.length := Nat.ne_of_lt hold
          obtain ⟨hne',hb,heq⟩ := hsim i hold
          simp only [mm,ite_eq_right hne]
          refine ⟨hne',hb,?_⟩
          intro x
          rw [old_original hold]
          exact heq x
        · have hei : i = n + gs.length := by simp at hi; omega
          subst i
          simp only [mm,ite_eq_left rfl]
          refine ⟨hune.mono Finset.subset_union_left,?_,?_⟩
          · intro j hj
            rcases Finset.mem_union.mp hj with hj | hj
            · exact hub j hj
            · exact hvb j hj
          · intro x
            simp only [term,conj_union]
            rw [new_original]
            simp only [↓reduceIte]
            exact congrArg₂ (fun a b : Bool => a && b) (husim x) (hvsim x)
      · intro j hj hor
        have hold : j < gs.length := by
          by_contra hn
          have hei : j = gs.length := by simp at hj; omega
          subst j
          simp [binary] at hor
        have hop : gs[j].op = .or := by simpa [List.getElem_append_left hold] using hor
        obtain ⟨k,hk,hm⟩ := hroots j hold hop
        refine ⟨k,hk,?_⟩
        have hne : n+j ≠ n+gs.length := by omega
        simpa only [mm,ite_eq_right hne] using hm

lemma ao2_flatten_output_private {n : ℕ} (C : Circuit)
    (T : Set (Fin n → Bool)) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hpriv : PrivateOriginal n C.gates T) :
    ∃ (hs : List Node) (s : Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs T ∧ hs.length = orCount C.gates ∧
      s.Nonempty ∧ (∀ i ∈ s, i < n + hs.length) ∧
      (∀ x : Fin n → Bool, term n hs s x = C.eval (List.ofFn x)) ∧
      ∀ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .or →
        ∃ k < hs.length, ∀ x : Fin n → Bool,
          wire n hs (n+k) x = (C.wires (List.ofFn x)).getD (n+j) false := by
  obtain ⟨hs,m,hvalid,hprivate,hcount,hsim,hroots⟩ :=
    exists_normalform_private n C.gates T (layout_of hC) hpriv
  obtain ⟨hne,hb,he⟩ := hsim C.output (output_bound_of_true hpos)
  refine ⟨hs,m C.output,hvalid,hprivate,hcount,hne,hb,he,?_⟩
  intro j hj hop
  have hat : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD,hj]
  rw [hat] at hop
  obtain ⟨k,hk,hm⟩ := hroots j hj hop
  refine ⟨k,hk,?_⟩
  intro x
  have he := (hsim (n+j) (by omega)).2.2 x
  rw [hm] at he
  calc
    wire n hs (n+k) x = original n C.gates (n+j) x := by
      simpa only [term,conj_singleton] using he
    _ = (C.wires (List.ofFn x)).getD (n+j) false := rfl

lemma private_original_of_decomposition {n : ℕ} (gs : List Gate)
    (T : Set (Fin n → Bool))
    (hp : ∀ (pre post : List Gate) (u v : ℕ),
      gs = pre ++ [binary false u v] ++ post → u < n + pre.length → v < n + pre.length →
      (∃ x ∈ T, original n pre u x = true ∧ original n pre v x = false) ∧
      (∃ x ∈ T, original n pre v x = true ∧ original n pre u x = false)) :
    PrivateOriginal n gs T := by
  intro j hj u v hgate hu hv
  let pre := gs.take j
  let post := gs.drop (j+1)
  have hlen : pre.length = j := by
    simp [pre,List.length_take,Nat.min_eq_left (Nat.le_of_lt hj)]
  have he : gs = pre ++ [binary false u v] ++ post := by
    calc
      gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
      _ = pre ++ [binary false u v] ++ post := by
        rw [List.drop_eq_getElem_cons hj,hgate]
        simp [pre,post]
  have hup : u < n + pre.length := by simpa only [hlen] using hu
  have hvp : v < n + pre.length := by simpa only [hlen] using hv
  have hou : ∀ x : Fin n → Bool, original n gs u x = original n pre u x := by
    intro x
    rw [he,List.append_assoc]
    exact original_append_old pre ([binary false u v] ++ post) u hup x
  have hov : ∀ x : Fin n → Bool, original n gs v x = original n pre v x := by
    intro x
    rw [he,List.append_assoc]
    exact original_append_old pre ([binary false u v] ++ post) v hvp x
  simpa only [hou,hov] using hp pre post u v he hup hvp

end H8AndFree

namespace H8OrPatch

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4970.H8AndFree

def TestInputs {n : ℕ} (P : Finset (Finset (Fin n))) : Set (Fin n → Bool) :=
  {x | ∃ S ∈ Tests P, x = H8Active.assignmentOf S}

lemma exists_private_normalization {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x)
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    ∃ (hs : List Node) (s : Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs (TestInputs P) ∧ hs.length ≤ orCount C.gates ∧
      s.Nonempty ∧ (∀ i ∈ s, i < n + hs.length) ∧
      (∀ x : Fin n → Bool, term n hs s x = H8Active.dnf P x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card → HasPureOr n C Q →
        ∃ j < hs.length, ∀ x : Fin n → Bool, wire n hs (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨D,hD,hDF,hDR,hcount,hprivate⟩ := exists_private_minimum C hC P hF
  have hposD : ∃ x : Fin n → Bool, D.eval (List.ofFn x) = true := by
    obtain ⟨x,hx⟩ := hpos
    refine ⟨x,?_⟩
    rw [hDF,← hF]
    exact hx
  have hprivD : PrivateOriginal n D.gates (TestInputs P) := by
    apply private_original_of_decomposition
    intro pre post u v he hu hv
    obtain ⟨⟨S,hS,huS,hvS⟩,⟨R,hR,hvR,huR⟩⟩ := hprivate pre post u v he
    exact ⟨⟨H8Active.assignmentOf S,⟨S,hS,rfl⟩,huS,hvS⟩,
      ⟨H8Active.assignmentOf R,⟨R,hR,rfl⟩,hvR,huR⟩⟩
  obtain ⟨hs,s,hvalid,hpriv,hcnt,hne,hb,hout,hroots⟩ :=
    ao2_flatten_output_private D (TestInputs P) hD hposD hprivD
  refine ⟨hs,s,hvalid,hpriv,hcnt.trans_le hcount,hne,hb,?_,?_⟩
  · intro x
    exact (hout x).trans (hDF x)
  · intro Q hQ hQC
    obtain ⟨j,hj,hjop,hjQ⟩ := hDR Q hQ hQC
    obtain ⟨k,hk,hkQ⟩ := hroots j hj hjop
    exact ⟨k,hk,fun x => (hkQ x).trans (hjQ x)⟩

end H8OrPatch

namespace H8AndFree

lemma normal_getD_le {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) (i : ℕ) :
    a.getD i false ≤ b.getD i false := by
  induction h generalizing i with
  | nil => simp
  | @cons a b xs ys hab hxy ih =>
    cases i with
    | zero => simpa [List.getD] using hab
    | succ i => simpa [List.getD] using ih i

lemma normal_conj_le {v w : ℕ → Bool} (s : Finset ℕ)
    (h : ∀ i ∈ s, v i ≤ w i) : conj v s ≤ conj w s := by
  apply Bool.le_iff_imp.mpr
  intro hv
  have hv' : ∀ i ∈ s, v i = true := by simpa only [conj,decide_eq_true_eq] using hv
  simp only [conj,decide_eq_true_eq]
  intro i hi
  exact Bool.le_iff_imp.mp (h i hi) (hv' i hi)

lemma normal_step_mono {w z : List Bool} (h : List.Forall₂ (· ≤ ·) w z)
    (g : Node) : List.Forall₂ (· ≤ ·) (step w g) (step z g) := by
  unfold step
  apply List.rel_append h
  apply List.Forall₂.cons
  · apply Bool.le_iff_imp.mpr
    intro hp
    rcases Bool.or_eq_true_iff.mp hp with ha | hb
    · exact Bool.or_eq_true_iff.mpr (Or.inl
        (Bool.le_iff_imp.mp (normal_conj_le g.1 (fun i _ => normal_getD_le h i)) ha))
    · exact Bool.or_eq_true_iff.mpr (Or.inr
        (Bool.le_iff_imp.mp (normal_conj_le g.2 (fun i _ => normal_getD_le h i)) hb))
  · exact List.Forall₂.nil

lemma normal_fold_mono (gs : List Node) {w z : List Bool}
    (h : List.Forall₂ (· ≤ ·) w z) :
    List.Forall₂ (· ≤ ·) (gs.foldl step w) (gs.foldl step z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih => exact ih (normal_step_mono h g)

lemma normal_wire_mono (n : ℕ) (gs : List Node) (i : ℕ) :
    Monotone (wire n gs i) := by
  intro x y hxy
  have hinit : List.Forall₂ (· ≤ ·) (List.ofFn x) (List.ofFn y) := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro j hj hj'
    have hjn : j < n := by simpa using hj
    simpa using hxy ⟨j,hjn⟩
  exact normal_getD_le (normal_fold_mono gs hinit) i

lemma normal_wire_input (n : ℕ) (gs : List Node) (i : ℕ) (hi : i < n)
    (x : Fin n → Bool) : wire n gs i x = x ⟨i,hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil => simp [wire,values,List.getD,hi]
  | append_singleton gs g ih =>
    rw [old_wire (by omega)]
    exact ih

lemma normal_pure_term_root (n : ℕ) (gs : List Node) (s : Finset ℕ)
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (hs : ∀ i ∈ s, i < n + gs.length)
    (he : ∀ x : Fin n → Bool,
      term n gs s x = H8Active.disjunction Q x) :
    ∃ j < gs.length, ∀ x : Fin n → Bool,
      wire n gs (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨i,hi,hif⟩ := H8Active.conjunction_eq_disjunction_factor Q s
    (fun i x => wire n gs i x) (fun i _ => normal_wire_mono n gs i) he
  have hib := hs i hi
  by_cases hin : i < n
  · have hsub : Q ⊆ {⟨i,hin⟩} := by
      intro a ha
      have ht : H8Active.disjunction Q (H8Active.assignmentOf {a}) = true := by
        simp only [H8Active.disjunction,decide_eq_true_eq]
        exact ⟨a,ha,by simp [H8Active.assignmentOf]⟩
      have hw : wire n gs i (H8Active.assignmentOf {a}) = true := by
        rw [hif]
        exact ht
      rw [normal_wire_input n gs i hin] at hw
      have hae : (⟨i,hin⟩ : Fin n) = a := by simpa [H8Active.assignmentOf] using hw
      simpa only [Finset.mem_singleton] using hae.symm
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  · refine ⟨i-n,by omega,?_⟩
    have hei : n+(i-n) = i := by omega
    simpa only [hei] using hif

end H8AndFree

namespace H8AndFree

def expand (m : ℕ → Finset ℕ) (s : Finset ℕ) : Finset ℕ := s.biUnion m

def DisjointNormal (gs : List Node) : Prop :=
  ∀ j (hj : j < gs.length), Disjoint gs[j].1 gs[j].2

def NormalSim (n : ℕ) (gs hs : List Node) (m : ℕ → Finset ℕ) : Prop :=
  ∀ i < n + gs.length,
    (m i).Nonempty ∧ (∀ j ∈ m i, j < n + hs.length) ∧
    ∀ x : Fin n → Bool, term n hs (m i) x = wire n gs i x

lemma conj_expand (v : ℕ → Bool) (m : ℕ → Finset ℕ) (s : Finset ℕ) :
    conj v (expand m s) = conj (fun i => conj v (m i)) s := by
  unfold conj
  congr 1
  apply propext
  constructor
  · intro h i hi
    simp only [decide_eq_true_eq]
    intro j hj
    exact h j (Finset.mem_biUnion.mpr ⟨i,hi,hj⟩)
  · intro h j hj
    obtain ⟨i,hi,hji⟩ := Finset.mem_biUnion.mp hj
    have hh : ∀ k ∈ m i, v k = true := by simpa only [decide_eq_true_eq] using h i hi
    exact hh j hji

lemma expand_nonempty (m : ℕ → Finset ℕ) (s : Finset ℕ)
    (hs : s.Nonempty) (hm : ∀ i ∈ s, (m i).Nonempty) : (expand m s).Nonempty := by
  obtain ⟨i,hi⟩ := hs
  obtain ⟨j,hj⟩ := hm i hi
  exact ⟨j,Finset.mem_biUnion.mpr ⟨i,hi,hj⟩⟩

lemma expand_bound (m : ℕ → Finset ℕ) (s : Finset ℕ) (b : ℕ)
    (hm : ∀ i ∈ s, ∀ j ∈ m i, j < b) : ∀ j ∈ expand m s, j < b := by
  intro j hj
  obtain ⟨i,hi,hji⟩ := Finset.mem_biUnion.mp hj
  exact hm i hi j hji

lemma term_expand {n : ℕ} {gs hs : List Node} {m : ℕ → Finset ℕ}
    (h : NormalSim n gs hs m) (s : Finset ℕ) (hb : ∀ i ∈ s, i < n + gs.length)
    (x : Fin n → Bool) : term n hs (expand m s) x = term n gs s x := by
  rw [term,conj_expand]
  apply conj_congr
  intro i hi
  exact (h i (hb i hi)).2.2 x

lemma conj_subset_true (v : ℕ → Bool) (a b : Finset ℕ) (hab : a ⊆ b)
    (hb : conj v b = true) : conj v a = true := by
  simp only [conj,decide_eq_true_eq] at hb ⊢
  intro i hi
  exact hb i (hab hi)

lemma residual_private (v : ℕ → Bool) (a b : Finset ℕ)
    (ha : conj v a = true) (hb : conj v b = false) :
    conj v (a \ b) = true ∧ conj v (b \ a) = false := by
  refine ⟨conj_subset_true v _ a Finset.sdiff_subset ha,?_⟩
  cases hr : conj v (b \ a) with
  | false => rfl
  | true =>
    have hh : conj v b = true := by
      simp only [conj,decide_eq_true_eq] at ha hr ⊢
      intro i hi
      by_cases hia : i ∈ a
      · exact ha i hia
      · exact hr i (Finset.mem_sdiff.mpr ⟨hi,hia⟩)
    rw [hb] at hh
    cases hh

lemma factor_identity (v : ℕ → Bool) (a b : Finset ℕ) :
    (conj v (a ∩ b) && (conj v (a \ b) || conj v (b \ a))) =
      (conj v a || conj v b) := by
  have hA : (a ∩ b) ∪ (a \ b) = a := by ext i; simp
  have hB : (a ∩ b) ∪ (b \ a) = b := by ext i; simp; tauto
  have hCA : conj v a = (conj v (a ∩ b) && conj v (a \ b)) := by
    rw [← conj_union,hA]
  have hCB : conj v b = (conj v (a ∩ b) && conj v (b \ a)) := by
    rw [← conj_union,hB]
  rw [hCA,hCB]
  cases conj v (a ∩ b) <;> simp

lemma term_nonempty_of_false {n : ℕ} (gs : List Node) (s : Finset ℕ) (x : Fin n → Bool)
    (h : term n gs s x = false) : s.Nonempty := by
  by_contra hn
  have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [he,term,conj] at h

lemma private_normal_prefix {n : ℕ} (gs : List Node) (g : Node)
    (T : Set (Fin n → Bool)) (hv : Valid n gs)
    (hp : PrivateNormal n (gs ++ [g]) T) : PrivateNormal n gs T := by
  intro j hj
  have ha : ∀ i ∈ gs[j].1, i < n + gs.length := by
    intro i hi
    have hh := (hv j hj).2.2.1 i hi
    omega
  have hb : ∀ i ∈ gs[j].2, i < n + gs.length := by
    intro i hi
    have hh := (hv j hj).2.2.2 i hi
    omega
  have hh := hp j (by simp; omega)
  rw [List.getElem_append_left hj] at hh
  simpa only [old_term ha,old_term hb] using hh

lemma exists_disjoint_private_simulation (n : ℕ) (gs : List Node)
    (T : Set (Fin n → Bool)) (hv : Valid n gs) (hp : PrivateNormal n gs T) :
    ∃ (hs : List Node) (m : ℕ → Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs T ∧ DisjointNormal hs ∧
      hs.length = gs.length ∧ NormalSim n gs hs m := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[],fun i => {i},?_,?_,?_,rfl,?_⟩
    · intro j hj; simp at hj
    · intro j hj; simp at hj
    · intro j hj; simp at hj
    · intro i hi
      refine ⟨Finset.singleton_nonempty _,?_,?_⟩
      · intro j hj; simpa using Finset.mem_singleton.mp hj ▸ hi
      · intro x; simp [term,conj_singleton]
  | append_singleton gs g ih =>
    have hvg : Valid n gs := by
      intro j hj
      have hh := hv j (by simp; omega)
      rw [List.getElem_append_left hj] at hh
      exact hh
    have hpg := private_normal_prefix gs g T hvg hp
    obtain ⟨hs,m,hvalid,hprivate,hdisjoint,hcount,hsim⟩ := ih hvg hpg
    obtain ⟨hgane,hgbne,hga,hgb⟩ := hv gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero] at hgane hgbne hga hgb
    have hA : ∀ i ∈ expand m g.1, i < n + hs.length :=
      expand_bound m g.1 _ (fun i hi => (hsim i (hga i hi)).2.1)
    have hB : ∀ i ∈ expand m g.2, i < n + hs.length :=
      expand_bound m g.2 _ (fun i hi => (hsim i (hgb i hi)).2.1)
    let A := expand m g.1
    let B := expand m g.2
    let RA := A \ B
    let RB := B \ A
    let C := A ∩ B
    have hRA : ∀ i ∈ RA, i < n + hs.length := fun i hi => hA i (Finset.mem_sdiff.mp hi).1
    have hRB : ∀ i ∈ RB, i < n + hs.length := fun i hi => hB i (Finset.mem_sdiff.mp hi).1
    have hC : ∀ i ∈ C, i < n + hs.length := fun i hi => hA i (Finset.mem_inter.mp hi).1
    have hnew : (∃ x ∈ T, term n hs RA x = true ∧ term n hs RB x = false) ∧
        (∃ x ∈ T, term n hs RB x = true ∧ term n hs RA x = false) := by
      have hh := hp gs.length (by simp)
      simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero,
        old_term hga,old_term hgb] at hh
      obtain ⟨⟨x,hx,ha,hb⟩,⟨y,hy,hb',ha'⟩⟩ := hh
      have hxA : term n hs A x = true := (term_expand hsim g.1 hga x).trans ha
      have hxB : term n hs B x = false := (term_expand hsim g.2 hgb x).trans hb
      have hyB : term n hs B y = true := (term_expand hsim g.2 hgb y).trans hb'
      have hyA : term n hs A y = false := (term_expand hsim g.1 hga y).trans ha'
      exact ⟨⟨x,hx,residual_private _ A B hxA hxB⟩,⟨y,hy,residual_private _ B A hyB hyA⟩⟩
    have hRAn : RA.Nonempty := by
      obtain ⟨x,hx,hb,ha⟩ := hnew.2
      exact term_nonempty_of_false hs RA x ha
    have hRBn : RB.Nonempty := by
      obtain ⟨x,hx,ha,hb⟩ := hnew.1
      exact term_nonempty_of_false hs RB x hb
    let mm : ℕ → Finset ℕ := fun i =>
      if i = n + gs.length then C ∪ {n + hs.length} else m i
    refine ⟨hs ++ [(RA,RB)],mm,valid_append hvalid RA RB hRAn hRBn hRA hRB,
      private_normal_append T hvalid hprivate RA RB hRA hRB hnew,?_,by simp [hcount],?_⟩
    · intro j hj
      by_cases hold : j < hs.length
      · simpa [List.getElem_append_left hold] using hdisjoint j hold
      · have he : j = hs.length := by simp at hj; omega
        subst j
        simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
        apply Finset.disjoint_left.mpr
        intro i hiA hiB
        exact (Finset.mem_sdiff.mp hiA).2 (Finset.mem_sdiff.mp hiB).1
    · intro i hi
      by_cases hold : i < n + gs.length
      · obtain ⟨hne,hb,he⟩ := hsim i hold
        have hne' : i ≠ n + gs.length := Nat.ne_of_lt hold
        simp only [mm,ite_eq_right hne']
        refine ⟨hne,?_,?_⟩
        · intro j hj; have hh := hb j hj; simp; omega
        · intro x
          rw [old_term hb,old_wire hold]
          exact he x
      · have hei : i = n + gs.length := by simp at hi; omega
        subst i
        simp only [mm,ite_eq_left rfl]
        refine ⟨(Finset.singleton_nonempty (n + hs.length)).mono Finset.subset_union_right,?_,?_⟩
        · intro j hj
          rcases Finset.mem_union.mp hj with hj | hj
          · have hh := hC j hj; simp; omega
          · have he := Finset.mem_singleton.mp hj; simp; omega
        · intro x
          change (conj (fun i => wire n (hs ++ [(RA,RB)]) i x) (C ∪ {n+hs.length})) = _
          rw [conj_union,conj_singleton]
          change (term n (hs ++ [(RA,RB)]) C x && wire n (hs ++ [(RA,RB)]) (n+hs.length) x) = _
          rw [old_term hC,new_wire,new_wire]
          rw [← term_expand hsim g.1 hga x,← term_expand hsim g.2 hgb x]
          exact factor_identity (fun i => wire n hs i x) A B

end H8AndFree

namespace H8AndFree

lemma exists_disjoint_private_output {n : ℕ} (gs : List Node)
    (T : Set (Fin n → Bool)) (hv : Valid n gs) (hp : PrivateNormal n gs T)
    (s : Finset ℕ) (hs : s.Nonempty) (hb : ∀ i ∈ s, i < n + gs.length) :
    ∃ (ks : List Node) (t : Finset ℕ), Valid n ks ∧ PrivateNormal n ks T ∧ DisjointNormal ks ∧
      ks.length = gs.length ∧ t.Nonempty ∧ (∀ i ∈ t, i < n + ks.length) ∧
      (∀ x : Fin n → Bool, term n ks t x = term n gs s x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card →
        (∃ i < n + gs.length, ∀ x : Fin n → Bool, wire n gs i x = H8Active.disjunction Q x) →
        ∃ j < ks.length, ∀ x : Fin n → Bool, wire n ks (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨ks,m,hvalid,hprivate,hdisjoint,hcount,hsim⟩ := exists_disjoint_private_simulation n gs T hv hp
  refine ⟨ks,expand m s,hvalid,hprivate,hdisjoint,hcount,
    expand_nonempty m s hs (fun i hi => (hsim i (hb i hi)).1),
    expand_bound m s _ (fun i hi => (hsim i (hb i hi)).2.1),term_expand hsim s hb,?_⟩
  intro Q hQ hroot
  obtain ⟨i,hi,hiQ⟩ := hroot
  apply normal_pure_term_root n ks (m i) Q hQ (hsim i hi).2.1
  intro x
  exact ((hsim i hi).2.2 x).trans (hiQ x)

end H8AndFree

namespace H8OrPatch

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4970.H8AndFree

lemma exists_disjoint_private_normalization {n : ℕ}
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x)
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    ∃ (hs : List Node) (s : Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs (TestInputs P) ∧ DisjointNormal hs ∧
      hs.length ≤ orCount C.gates ∧ s.Nonempty ∧ (∀ i ∈ s, i < n + hs.length) ∧
      (∀ x : Fin n → Bool, term n hs s x = H8Active.dnf P x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card → HasPureOr n C Q →
        ∃ j < hs.length, ∀ x : Fin n → Bool, wire n hs (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨gs,t,hvalid,hprivate,hcount,ht,hb,hout,hroots⟩ := exists_private_normalization C hC P hF hpos
  obtain ⟨hs,s,hsvalid,hsprivate,hsdisjoint,hscount,hsne,hsb,hsout,hsroots⟩ :=
    exists_disjoint_private_output gs (TestInputs P) hvalid hprivate t ht hb
  refine ⟨hs,s,hsvalid,hsprivate,hsdisjoint,hscount.trans_le hcount,hsne,hsb,?_,?_⟩
  · intro x
    exact (hsout x).trans (hout x)
  · intro Q hQ hQC
    obtain ⟨j,hj,hjQ⟩ := hroots Q hQ hQC
    exact hsroots Q hQ ⟨n+j,by omega,hjQ⟩

end H8OrPatch

namespace H8AndFree

lemma normal_append_old {n : ℕ} (gs tail : List Node) (i : ℕ)
    (hi : i < n + gs.length) (x : Fin n → Bool) :
    wire n (gs ++ tail) i x = wire n gs i x := by
  induction tail using List.reverseRecOn with
  | nil => simp
  | append_singleton tail g ih =>
    rw [← List.append_assoc,old_wire (by simp; omega),ih]

lemma normal_append_term {n : ℕ} (gs tail : List Node) (s : Finset ℕ)
    (hs : ∀ i ∈ s, i < n + gs.length) (x : Fin n → Bool) :
    term n (gs ++ tail) s x = term n gs s x := by
  apply conj_congr
  intro i hi
  exact normal_append_old gs tail i (hs i hi) x

lemma disjoint_normal_append {gs : List Node} (hd : DisjointNormal gs)
    (g : Node) (hg : Disjoint g.1 g.2) : DisjointNormal (gs ++ [g]) := by
  intro j hj
  by_cases h : j < gs.length
  · simpa only [List.getElem_append_left h] using hd j h
  · have he : j = gs.length := by simp at hj; omega
    subst j
    simpa only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] using hg

lemma private_duplicate_node {n : ℕ} (gs : List Node) (T : Set (Fin n → Bool))
    (hv : Valid n gs) (hp : PrivateNormal n gs T) (hd : DisjointNormal gs)
    (j : ℕ) (hj : j < gs.length) :
    Valid n (gs ++ [gs[j]]) ∧ PrivateNormal n (gs ++ [gs[j]]) T ∧
      DisjointNormal (gs ++ [gs[j]]) := by
  have ha : ∀ i ∈ gs[j].1, i < n + gs.length := by
    intro i hi
    have hh := (hv j hj).2.2.1 i hi
    omega
  have hb : ∀ i ∈ gs[j].2, i < n + gs.length := by
    intro i hi
    have hh := (hv j hj).2.2.2 i hi
    omega
  exact ⟨valid_append hv _ _ (hv j hj).1 (hv j hj).2.1 ha hb,
    private_normal_append T hv hp _ _ ha hb (hp j hj),
    disjoint_normal_append hd _ (hd j hj)⟩

lemma private_padding_tail {n : ℕ} (gs : List Node) (T : Set (Fin n → Bool))
    (hv : Valid n gs) (hp : PrivateNormal n gs T) (hd : DisjointNormal gs)
    (hne : 0 < gs.length) : ∀ d : ℕ, ∃ tail : List Node,
      tail.length = d ∧ Valid n (gs ++ tail) ∧ PrivateNormal n (gs ++ tail) T ∧
      DisjointNormal (gs ++ tail) := by
  intro d
  induction d with
  | zero => exact ⟨[],rfl,by simpa using hv,by simpa using hp,by simpa using hd⟩
  | succ d ih =>
    obtain ⟨tail,hlen,hv',hp',hd'⟩ := ih
    have hzero : 0 < (gs ++ tail).length := by simp; omega
    let g := (gs ++ tail)[0]
    obtain ⟨hvv,hpp,hdd⟩ := private_duplicate_node (gs ++ tail) T hv' hp' hd' 0 hzero
    refine ⟨tail ++ [g],by simp [hlen],?_,?_,?_⟩
    · simpa only [List.append_assoc] using hvv
    · simpa only [List.append_assoc] using hpp
    · simpa only [List.append_assoc] using hdd

lemma private_disjoint_pad {n : ℕ} (gs : List Node) (T : Set (Fin n → Bool))
    (hv : Valid n gs) (hp : PrivateNormal n gs T) (hd : DisjointNormal gs)
    (hne : 0 < gs.length) (r : ℕ) (hr : gs.length ≤ r) :
    ∃ hs : List Node, Valid n hs ∧ PrivateNormal n hs T ∧ DisjointNormal hs ∧
      hs.length = r ∧ (∃ tail : List Node, hs = gs ++ tail) ∧
      (∀ i < n + gs.length, ∀ x : Fin n → Bool, wire n hs i x = wire n gs i x) ∧
      (∀ s : Finset ℕ, (∀ i ∈ s, i < n + gs.length) → ∀ x : Fin n → Bool,
        term n hs s x = term n gs s x) := by
  obtain ⟨tail,hlen,hv',hp',hd'⟩ := private_padding_tail gs T hv hp hd hne (r-gs.length)
  refine ⟨gs ++ tail,hv',hp',hd',?_,⟨tail,rfl⟩,?_,?_⟩
  · simp only [List.length_append,hlen]
    omega
  · intro i hi x
    exact normal_append_old gs tail i hi x
  · intro s hs x
    exact normal_append_term gs tail s hs x

end H8AndFree

namespace H8OrPatch

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4970.H8AndFree

lemma exists_exact_disjoint_private_normalization {n : ℕ}
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x)
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hwitness : ∃ Q : Finset (Fin n), 2 ≤ Q.card ∧ HasPureOr n C Q)
    (r : ℕ) (hr : orCount C.gates ≤ r) :
    ∃ (hs : List Node) (s : Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs (TestInputs P) ∧ DisjointNormal hs ∧
      hs.length = r ∧ s.Nonempty ∧ (∀ i ∈ s, i < n + hs.length) ∧
      (∀ x : Fin n → Bool, term n hs s x = H8Active.dnf P x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card → HasPureOr n C Q →
        ∃ j < hs.length, ∀ x : Fin n → Bool, wire n hs (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨gs,s,hv,hp,hd,hcnt,hs,hb,hout,hroots⟩ :=
    exists_disjoint_private_normalization C hC P hF hpos
  have hgr : gs.length ≤ r := hcnt.trans hr
  have hgn : 0 < gs.length := by
    obtain ⟨Q,hQ,hQC⟩ := hwitness
    obtain ⟨j,hj,hjQ⟩ := hroots Q hQ hQC
    omega
  obtain ⟨ks,hkv,hkp,hkd,hkcnt,hprefix,hkw,hkt⟩ :=
    private_disjoint_pad gs (TestInputs P) hv hp hd hgn r hgr
  refine ⟨ks,s,hkv,hkp,hkd,hkcnt,hs,?_,?_,?_⟩
  · intro i hi
    have hh := hb i hi
    omega
  · intro x
    exact (hkt s hb x).trans (hout x)
  · intro Q hQ hQC
    obtain ⟨j,hj,hjQ⟩ := hroots Q hQ hQC
    refine ⟨j,by omega,?_⟩
    intro x
    exact (hkw (n+j) (by omega) x).trans (hjQ x)

lemma disjunction_support_unique {n : ℕ} (Q R : Finset (Fin n))
    (h : ∀ x : Fin n → Bool, H8Active.disjunction Q x = H8Active.disjunction R x) : Q = R := by
  ext a
  constructor
  · intro ha
    have ht : H8Active.disjunction R (H8Active.assignmentOf {a}) = true := by
      rw [← h]
      simp [H8Active.disjunction,H8Active.assignmentOf,ha]
    simpa [H8Active.disjunction,H8Active.assignmentOf] using ht
  · intro ha
    have ht : H8Active.disjunction Q (H8Active.assignmentOf {a}) = true := by
      rw [h]
      simp [H8Active.disjunction,H8Active.assignmentOf,ha]
    simpa [H8Active.disjunction,H8Active.assignmentOf] using ht

lemma term_literal_support {n : ℕ} (gs : List Node) (s : Finset ℕ) (Q : Finset (Fin n))
    (ht : term n gs s (H8Active.assignmentOf Q) = true) :
    ∀ a : Fin n, a.val ∈ s → a ∈ Q := by
  simp only [term,conj,decide_eq_true_eq] at ht
  intro a ha
  have hh := ht a.val ha
  rw [normal_wire_input n gs a.val a.isLt] at hh
  simpa [H8Active.assignmentOf] using hh

lemma literal_pair_allowed_of_positive_test {n : ℕ}
    (gs : List Node) (s : Finset ℕ) (P : Finset (Finset (Fin n)))
    (R : Fin n → Fin n → Prop)
    (hP : ∀ Q ∈ P, ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → R a b)
    (ht : ∃ Q ∈ Tests P, term n gs s (H8Active.assignmentOf Q) = true)
    (a b : Fin n) (ha : a.val ∈ s) (hb : b.val ∈ s) (hne : a ≠ b) : R a b := by
  obtain ⟨Q,hQ,hQt⟩ := ht
  have haQ := term_literal_support gs s Q hQt a ha
  have hbQ := term_literal_support gs s Q hQt b hb
  rcases Finset.mem_union.mp hQ with hQP | hQS
  · exact hP Q hQP a haQ b hbQ hne
  · obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hQS
    subst Q
    have hac : a = c := Finset.mem_singleton.mp haQ
    have hbc : b = c := Finset.mem_singleton.mp hbQ
    exact (hne (hac.trans hbc.symm)).elim

end H8OrPatch

namespace H8AndFree

lemma monotone_safe_of_outside {n : ℕ} (Q : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hz : f (fun a => decide (a ∉ Q)) = false) :
    ∀ x, f x ≤ H8Active.disjunction Q x := by
  intro x
  apply Bool.le_iff_imp.mpr
  intro hx
  by_contra hd
  have hnone : ¬ ∃ a ∈ Q, x a = true := by
    simpa only [H8Active.disjunction,decide_eq_true_eq] using hd
  have hxo : x ≤ fun a => decide (a ∉ Q) := by
    intro a
    apply Bool.le_iff_imp.mpr
    intro hxa
    have ha : a ∉ Q := fun haq => hnone ⟨a,haq,hxa⟩
    simp [ha]
  have ht := Bool.le_iff_imp.mp (hf hxo) hx
  rw [hz] at ht
  cases ht

lemma safe_term_factor (n : ℕ) (gs : List Node) (A : Finset ℕ)
    (Q : Finset (Fin n))
    (hsafe : ∀ x, term n gs A x ≤ H8Active.disjunction Q x) :
    ∃ i ∈ A, ∀ x, wire n gs i x ≤ H8Active.disjunction Q x := by
  classical
  let outside : Fin n → Bool := fun a => decide (a ∉ Q)
  have hq : H8Active.disjunction Q outside = false := by
    simp [H8Active.disjunction,outside]
  have ht : term n gs A outside = false := by
    have hh := hsafe outside
    rw [hq] at hh
    cases he : term n gs A outside with
    | false => rfl
    | true => exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) (he ▸ hh))
  have hn : ¬ ∀ i ∈ A, wire n gs i outside = true := by
    simpa only [term,conj,decide_eq_false_iff_not] using ht
  push Not at hn
  obtain ⟨i,hi,hif⟩ := hn
  have hz : wire n gs i outside = false := by
    cases he : wire n gs i outside with
    | false => rfl
    | true => exact (hif he).elim
  exact ⟨i,hi,monotone_safe_of_outside Q (wire n gs i) (normal_wire_mono n gs i) hz⟩

lemma pure_or_of_no_left_private {n : ℕ} (Q : Finset (Fin n))
    (T : Set (Fin n → Bool)) (f g : (Fin n → Bool) → Bool)
    (hg : Monotone g)
    (hgsafe : ∀ x, g x ≤ H8Active.disjunction Q x)
    (hwhole : ∀ x, (f x || g x) = H8Active.disjunction Q x)
    (hT : ∀ a ∈ Q, H8Active.assignmentOf {a} ∈ T)
    (hn : ¬ ∃ x ∈ T, f x = true ∧ g x = false) :
    ∀ x, g x = H8Active.disjunction Q x := by
  intro x
  apply le_antisymm
  · exact hgsafe x
  · apply Bool.le_iff_imp.mpr
    intro hx
    obtain ⟨a,ha,hxa⟩ : ∃ a ∈ Q, x a = true := by
      simpa only [H8Active.disjunction,decide_eq_true_eq] using hx
    have ht : (f (H8Active.assignmentOf {a}) || g (H8Active.assignmentOf {a})) = true := by
      rw [hwhole]
      simp only [H8Active.disjunction,decide_eq_true_eq]
      exact ⟨a,ha,by simp [H8Active.assignmentOf]⟩
    have hga : g (H8Active.assignmentOf {a}) = true := by
      rcases Bool.or_eq_true_iff.mp ht with hf | hg'
      · cases he : g (H8Active.assignmentOf {a}) with
        | false => exact (hn ⟨H8Active.assignmentOf {a},hT a ha,hf,he⟩).elim
        | true => rfl
      · exact hg'
    have hax : H8Active.assignmentOf {a} ≤ x :=
      H8Active.assignmentOf_le (by simpa using hxa)
    exact Bool.le_iff_imp.mp (hg hax) hga

lemma pure_or_private_or_alias {n : ℕ} (Q : Finset (Fin n))
    (T : Set (Fin n → Bool)) (f g : (Fin n → Bool) → Bool)
    (hf : Monotone f) (hg : Monotone g)
    (hfsafe : ∀ x, f x ≤ H8Active.disjunction Q x)
    (hgsafe : ∀ x, g x ≤ H8Active.disjunction Q x)
    (hwhole : ∀ x, (f x || g x) = H8Active.disjunction Q x)
    (hT : ∀ a ∈ Q, H8Active.assignmentOf {a} ∈ T) :
    ((∃ x ∈ T, f x = true ∧ g x = false) ∧
      (∃ x ∈ T, g x = true ∧ f x = false)) ∨
      (∀ x, f x = H8Active.disjunction Q x) ∨
      (∀ x, g x = H8Active.disjunction Q x) := by
  classical
  by_cases hl : ∃ x ∈ T, f x = true ∧ g x = false
  · by_cases hr : ∃ x ∈ T, g x = true ∧ f x = false
    · exact Or.inl ⟨hl,hr⟩
    · right; left
      exact pure_or_of_no_left_private Q T g f hf hfsafe
        (fun x => by rw [Bool.or_comm]; exact hwhole x) hT hr
  · right; right
    exact pure_or_of_no_left_private Q T f g hg hgsafe hwhole hT hl

lemma pure_terms_choose_sources (n : ℕ) (gs : List Node) (A B : Finset ℕ)
    (Q : Finset (Fin n)) (T : Set (Fin n → Bool))
    (hA : ∀ i ∈ A, i < n + gs.length) (hB : ∀ i ∈ B, i < n + gs.length)
    (hwhole : ∀ x : Fin n → Bool,
      (term n gs A x || term n gs B x) = H8Active.disjunction Q x)
    (hT : ∀ a ∈ Q, H8Active.assignmentOf {a} ∈ T) :
    ∃ i ∈ A, ∃ j ∈ B, i < n + gs.length ∧ j < n + gs.length ∧
      (∀ x, wire n gs i x ≤ H8Active.disjunction Q x) ∧
      (∀ x, wire n gs j x ≤ H8Active.disjunction Q x) ∧
      (∀ x, (wire n gs i x || wire n gs j x) = H8Active.disjunction Q x) ∧
      (((∃ x ∈ T, wire n gs i x = true ∧ wire n gs j x = false) ∧
        (∃ x ∈ T, wire n gs j x = true ∧ wire n gs i x = false)) ∨
        (∀ x, wire n gs i x = H8Active.disjunction Q x) ∨
        (∀ x, wire n gs j x = H8Active.disjunction Q x)) := by
  have ha : ∀ x, term n gs A x ≤ H8Active.disjunction Q x := by
    intro x
    rw [← hwhole x]
    cases term n gs A x <;> cases term n gs B x <;> decide
  have hb : ∀ x, term n gs B x ≤ H8Active.disjunction Q x := by
    intro x
    rw [← hwhole x]
    cases term n gs A x <;> cases term n gs B x <;> decide
  obtain ⟨i,hi,his⟩ := safe_term_factor n gs A Q ha
  obtain ⟨j,hj,hjs⟩ := safe_term_factor n gs B Q hb
  have ht : ∀ x, (wire n gs i x || wire n gs j x) = H8Active.disjunction Q x := by
    intro x
    apply le_antisymm
    · apply Bool.le_iff_imp.mpr
      intro hx
      rcases Bool.or_eq_true_iff.mp hx with hi' | hj'
      · exact Bool.le_iff_imp.mp (his x) hi'
      · exact Bool.le_iff_imp.mp (hjs x) hj'
    · apply Bool.le_iff_imp.mpr
      intro hx
      rw [← hwhole x] at hx
      rcases Bool.or_eq_true_iff.mp hx with ha' | hb'
      · have hall : ∀ k ∈ A, wire n gs k x = true := by
          simpa only [term,conj,decide_eq_true_eq] using ha'
        exact Bool.or_eq_true_iff.mpr (Or.inl (hall i hi))
      · have hall : ∀ k ∈ B, wire n gs k x = true := by
          simpa only [term,conj,decide_eq_true_eq] using hb'
        exact Bool.or_eq_true_iff.mpr (Or.inr (hall j hj))
  refine ⟨i,hi,j,hj,hA i hi,hB j hj,his,hjs,ht,?_⟩
  exact pure_or_private_or_alias Q T (wire n gs i) (wire n gs j)
    (normal_wire_mono n gs i) (normal_wire_mono n gs j) his hjs ht hT

lemma private_pair_indices_ne {n : ℕ} (gs : List Node) (i j : ℕ)
    (T : Set (Fin n → Bool))
    (hp : ∃ x ∈ T, wire n gs i x = true ∧ wire n gs j x = false) : i ≠ j := by
  intro he
  subst j
  obtain ⟨x,hx,ht,hf⟩ := hp
  rw [ht] at hf
  cases hf

end H8AndFree

namespace H8AndFree

def FlatWitnesses (n : ℕ) (gs : List Node) : Prop :=
  ∀ j (hj : j < gs.length) (Q : Finset (Fin n)), 2 ≤ Q.card →
    (∀ x : Fin n → Bool, wire n gs (n+j) x = H8Active.disjunction Q x) →
    gs[j].1.card = 1 ∧ gs[j].2.card = 1

lemma flat_witnesses_append {n : ℕ} (gs : List Node) (a b : Finset ℕ)
    (hp : FlatWitnesses n gs)
    (hnew : ∀ (Q : Finset (Fin n)), 2 ≤ Q.card →
      (∀ x : Fin n → Bool, (term n gs a x || term n gs b x) = H8Active.disjunction Q x) →
      a.card = 1 ∧ b.card = 1) : FlatWitnesses n (gs ++ [(a,b)]) := by
  intro j hj Q hQ hfn
  by_cases hold : j < gs.length
  · have he : ∀ x : Fin n → Bool, wire n gs (n+j) x = H8Active.disjunction Q x := by
      intro x
      simpa only [old_wire (by omega : n+j < n+gs.length)] using hfn x
    simpa only [List.getElem_append_left hold] using hp j hold Q hQ he
  · have hej : j = gs.length := by simp at hj; omega
    subst j
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
    apply hnew Q hQ
    intro x
    simpa only [new_wire] using hfn x

lemma append_refactored_simulation {n : ℕ} {gs hs : List Node} {m : ℕ → Finset ℕ}
    (h : NormalSim n gs hs m) (g : Node) (a b c : Finset ℕ)
    (hc : ∀ i ∈ c, i < n + hs.length)
    (he : ∀ x : Fin n → Bool, (term n hs c x && (term n hs a x || term n hs b x)) =
      (term n gs g.1 x || term n gs g.2 x)) :
    ∃ mm : ℕ → Finset ℕ, NormalSim n (gs ++ [g]) (hs ++ [(a,b)]) mm := by
  let mm : ℕ → Finset ℕ := fun i => if i = n + gs.length then c ∪ {n + hs.length} else m i
  refine ⟨mm,?_⟩
  intro i hi
  by_cases hold : i < n + gs.length
  · obtain ⟨hne,hb,hsem⟩ := h i hold
    have hneq : i ≠ n + gs.length := Nat.ne_of_lt hold
    simp only [mm,ite_eq_right hneq]
    refine ⟨hne,?_,?_⟩
    · intro j hj; have hh := hb j hj; simp; omega
    · intro x
      rw [old_term hb,old_wire hold]
      exact hsem x
  · have hej : i = n + gs.length := by simp at hi; omega
    subst i
    simp only [mm,ite_eq_left rfl]
    refine ⟨(Finset.singleton_nonempty (n+hs.length)).mono Finset.subset_union_right,?_,?_⟩
    · intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · have hh := hc j hj; simp; omega
      · have hh := Finset.mem_singleton.mp hj; simp; omega
    · intro x
      change conj (fun i => wire n (hs ++ [(a,b)]) i x) (c ∪ {n+hs.length}) = _
      rw [conj_union,conj_singleton]
      change (term n (hs ++ [(a,b)]) c x && wire n (hs ++ [(a,b)]) (n+hs.length) x) = _
      rw [old_term hc,new_wire,new_wire]
      exact he x

lemma alias_refactored_simulation {n : ℕ} {gs hs : List Node} {m : ℕ → Finset ℕ}
    (h : NormalSim n gs hs m) (g : Node) (c : Finset ℕ) (r : ℕ)
    (hc : ∀ i ∈ c, i < n + hs.length) (hr : r < n + hs.length)
    (he : ∀ x : Fin n → Bool, (term n hs c x && wire n hs r x) =
      (term n gs g.1 x || term n gs g.2 x)) :
    ∃ mm : ℕ → Finset ℕ, NormalSim n (gs ++ [g]) hs mm := by
  let mm : ℕ → Finset ℕ := fun i => if i = n + gs.length then c ∪ {r} else m i
  refine ⟨mm,?_⟩
  intro i hi
  by_cases hold : i < n + gs.length
  · obtain ⟨hne,hb,hsem⟩ := h i hold
    have hneq : i ≠ n + gs.length := Nat.ne_of_lt hold
    simp only [mm,ite_eq_right hneq]
    refine ⟨hne,hb,?_⟩
    intro x
    rw [old_wire hold]
    exact hsem x
  · have hej : i = n + gs.length := by simp at hi; omega
    subst i
    simp only [mm,ite_eq_left rfl]
    refine ⟨(Finset.singleton_nonempty r).mono Finset.subset_union_right,?_,?_⟩
    · intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hc j hj
      · have hh := Finset.mem_singleton.mp hj; omega
    · intro x
      change conj (fun i => wire n hs i x) (c ∪ {r}) = _
      rw [conj_union,conj_singleton,new_wire]
      exact he x

lemma exists_flat_private_simulation (n : ℕ) (gs : List Node)
    (T : Set (Fin n → Bool)) (hT : ∀ a : Fin n, H8Active.assignmentOf {a} ∈ T)
    (hv : Valid n gs) (hp : PrivateNormal n gs T) :
    ∃ (hs : List Node) (m : ℕ → Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs T ∧ DisjointNormal hs ∧ FlatWitnesses n hs ∧
      hs.length ≤ gs.length ∧ NormalSim n gs hs m := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[],fun i => {i},?_,?_,?_,?_,by simp,?_⟩
    · intro j hj; simp at hj
    · intro j hj; simp at hj
    · intro j hj; simp at hj
    · intro j hj; simp at hj
    · intro i hi
      refine ⟨Finset.singleton_nonempty _,?_,?_⟩
      · intro j hj; simpa using Finset.mem_singleton.mp hj ▸ hi
      · intro x; simp [term,conj_singleton]
  | append_singleton gs g ih =>
    have hvg : Valid n gs := by
      intro j hj
      have hh := hv j (by simp; omega)
      rw [List.getElem_append_left hj] at hh
      exact hh
    have hpg := private_normal_prefix gs g T hvg hp
    obtain ⟨hs,m,hvalid,hprivate,hdisjoint,hflat,hcount,hsim⟩ := ih hvg hpg
    obtain ⟨hgane,hgbne,hga,hgb⟩ := hv gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero] at hgane hgbne hga hgb
    have hA : ∀ i ∈ expand m g.1, i < n + hs.length :=
      expand_bound m g.1 _ (fun i hi => (hsim i (hga i hi)).2.1)
    have hB : ∀ i ∈ expand m g.2, i < n + hs.length :=
      expand_bound m g.2 _ (fun i hi => (hsim i (hgb i hi)).2.1)
    let A := expand m g.1
    let B := expand m g.2
    let RA := A \ B
    let RB := B \ A
    let C := A ∩ B
    have hRA : ∀ i ∈ RA, i < n + hs.length := fun i hi => hA i (Finset.mem_sdiff.mp hi).1
    have hRB : ∀ i ∈ RB, i < n + hs.length := fun i hi => hB i (Finset.mem_sdiff.mp hi).1
    have hC : ∀ i ∈ C, i < n + hs.length := fun i hi => hA i (Finset.mem_inter.mp hi).1
    have hnew : (∃ x ∈ T, term n hs RA x = true ∧ term n hs RB x = false) ∧
        (∃ x ∈ T, term n hs RB x = true ∧ term n hs RA x = false) := by
      have hh := hp gs.length (by simp)
      simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero,
        old_term hga,old_term hgb] at hh
      obtain ⟨⟨x,hx,ha,hb⟩,⟨y,hy,hb',ha'⟩⟩ := hh
      have hxA : term n hs A x = true := (term_expand hsim g.1 hga x).trans ha
      have hxB : term n hs B x = false := (term_expand hsim g.2 hgb x).trans hb
      have hyB : term n hs B y = true := (term_expand hsim g.2 hgb y).trans hb'
      have hyA : term n hs A y = false := (term_expand hsim g.1 hga y).trans ha'
      exact ⟨⟨x,hx,residual_private _ A B hxA hxB⟩,⟨y,hy,residual_private _ B A hyB hyA⟩⟩
    have hRAn : RA.Nonempty := by
      obtain ⟨x,hx,hb,ha⟩ := hnew.2
      exact term_nonempty_of_false hs RA x ha
    have hRBn : RB.Nonempty := by
      obtain ⟨x,hx,ha,hb⟩ := hnew.1
      exact term_nonempty_of_false hs RB x hb
    have hres : ∀ x : Fin n → Bool,
        (term n hs C x && (term n hs RA x || term n hs RB x)) =
        (term n gs g.1 x || term n gs g.2 x) := by
      intro x
      rw [← term_expand hsim g.1 hga x,← term_expand hsim g.2 hgb x]
      exact factor_identity (fun i => wire n hs i x) A B
    have add (a b : Finset ℕ) (ha : a.Nonempty) (hb : b.Nonempty)
        (hba : ∀ i ∈ a, i < n+hs.length) (hbb : ∀ i ∈ b, i < n+hs.length)
        (hpr : (∃ x ∈ T, term n hs a x = true ∧ term n hs b x = false) ∧
          (∃ x ∈ T, term n hs b x = true ∧ term n hs a x = false))
        (hdis : Disjoint a b)
        (hfl : ∀ (Q : Finset (Fin n)), 2 ≤ Q.card →
          (∀ x : Fin n → Bool, (term n hs a x || term n hs b x) = H8Active.disjunction Q x) →
          a.card = 1 ∧ b.card = 1)
        (hsem : ∀ x : Fin n → Bool, (term n hs C x && (term n hs a x || term n hs b x)) =
          (term n gs g.1 x || term n gs g.2 x)) :
        ∃ (ks : List Node) (mm : ℕ → Finset ℕ),
          Valid n ks ∧ PrivateNormal n ks T ∧ DisjointNormal ks ∧ FlatWitnesses n ks ∧
          ks.length ≤ (gs ++ [g]).length ∧ NormalSim n (gs ++ [g]) ks mm := by
      obtain ⟨mm,hmm⟩ := append_refactored_simulation hsim g a b C hC hsem
      exact ⟨hs ++ [(a,b)],mm,valid_append hvalid a b ha hb hba hbb,
        private_normal_append T hvalid hprivate a b hba hbb hpr,
        disjoint_normal_append hdisjoint (a,b) hdis,flat_witnesses_append hs a b hflat hfl,
        by simp; omega,hmm⟩
    have reuse (r : ℕ) (hr : r < n+hs.length)
        (hrf : ∀ x : Fin n → Bool, wire n hs r x = (term n hs RA x || term n hs RB x)) :
        ∃ (ks : List Node) (mm : ℕ → Finset ℕ),
          Valid n ks ∧ PrivateNormal n ks T ∧ DisjointNormal ks ∧ FlatWitnesses n ks ∧
          ks.length ≤ (gs ++ [g]).length ∧ NormalSim n (gs ++ [g]) ks mm := by
      have hsem : ∀ x : Fin n → Bool, (term n hs C x && wire n hs r x) =
          (term n gs g.1 x || term n gs g.2 x) := by intro x; rw [hrf]; exact hres x
      obtain ⟨mm,hmm⟩ := alias_refactored_simulation hsim g C r hC hr hsem
      exact ⟨hs,mm,hvalid,hprivate,hdisjoint,hflat,by simp; omega,hmm⟩
    by_cases hex : ∃ Q : Finset (Fin n), 2 ≤ Q.card ∧
        ∀ x : Fin n → Bool, (term n hs RA x || term n hs RB x) = H8Active.disjunction Q x
    · obtain ⟨Q,hQ,hfn⟩ := hex
      obtain ⟨i,hi,j,hj,hib,hjb,his,hjs,hij,hchoice⟩ :=
        pure_terms_choose_sources n hs RA RB Q T hRA hRB hfn (fun a _ => hT a)
      rcases hchoice with hpv | hai | haj
      · apply add {i} {j} (Finset.singleton_nonempty _) (Finset.singleton_nonempty _)
          (by intro k hk; simpa only [Finset.mem_singleton.mp hk] using hib)
          (by intro k hk; simpa only [Finset.mem_singleton.mp hk] using hjb)
        · simpa only [term,conj_singleton] using hpv
        · exact Finset.disjoint_singleton.mpr (private_pair_indices_ne hs i j T hpv.1)
        · intro R hR hrf; simp
        · intro x
          have hh : (term n hs {i} x || term n hs {j} x) = (term n hs RA x || term n hs RB x) := by
            simp only [term,conj_singleton]
            exact (hij x).trans (hfn x).symm
          rw [hh]
          exact hres x
      · exact reuse i hib (fun x => (hai x).trans (hfn x).symm)
      · exact reuse j hjb (fun x => (haj x).trans (hfn x).symm)
    · apply add RA RB hRAn hRBn hRA hRB hnew
      · apply Finset.disjoint_left.mpr
        intro i hiA hiB
        exact (Finset.mem_sdiff.mp hiA).2 (Finset.mem_sdiff.mp hiB).1
      · intro Q hQ hf
        exact (hex ⟨Q,hQ,hf⟩).elim
      · exact hres

end H8AndFree

namespace H8AndFree

lemma private_flat_padding_tail {n : ℕ} (gs : List Node) (T : Set (Fin n → Bool))
    (hv : Valid n gs) (hp : PrivateNormal n gs T) (hd : DisjointNormal gs)
    (hf : FlatWitnesses n gs) (j : ℕ) (hj : j < gs.length)
    (ha : gs[j].1.card = 1) (hb : gs[j].2.card = 1) :
    ∀ d : ℕ, ∃ tail : List Node, tail.length = d ∧ Valid n (gs ++ tail) ∧
      PrivateNormal n (gs ++ tail) T ∧ DisjointNormal (gs ++ tail) ∧
      FlatWitnesses n (gs ++ tail) := by
  intro d
  induction d with
  | zero =>
    exact ⟨[],rfl,by simpa using hv,by simpa using hp,by simpa using hd,by simpa using hf⟩
  | succ d ih =>
    obtain ⟨tail,hlen,hv',hp',hd',hf'⟩ := ih
    have hj' : j < (gs ++ tail).length := by simp; omega
    have ha' : (gs ++ tail)[j].1.card = 1 := by
      simpa only [List.getElem_append_left hj] using ha
    have hb' : (gs ++ tail)[j].2.card = 1 := by
      simpa only [List.getElem_append_left hj] using hb
    let g := (gs ++ tail)[j]
    obtain ⟨hvv,hpp,hdd⟩ := private_duplicate_node (gs ++ tail) T hv' hp' hd' j hj'
    have hff : FlatWitnesses n ((gs ++ tail) ++ [(gs ++ tail)[j]]) :=
      flat_witnesses_append (gs ++ tail) _ _ hf' (fun _ _ _ => ⟨ha',hb'⟩)
    refine ⟨tail ++ [g],by simp [hlen],?_,?_,?_,?_⟩
    · simpa only [List.append_assoc] using hvv
    · simpa only [List.append_assoc] using hpp
    · simpa only [List.append_assoc] using hdd
    · simpa only [List.append_assoc] using hff

lemma private_disjoint_flat_pad {n : ℕ} (gs : List Node) (T : Set (Fin n → Bool))
    (hv : Valid n gs) (hp : PrivateNormal n gs T) (hd : DisjointNormal gs)
    (hf : FlatWitnesses n gs) (j : ℕ) (hj : j < gs.length)
    (ha : gs[j].1.card = 1) (hb : gs[j].2.card = 1)
    (r : ℕ) (hr : gs.length ≤ r) :
    ∃ hs : List Node, Valid n hs ∧ PrivateNormal n hs T ∧ DisjointNormal hs ∧
      FlatWitnesses n hs ∧ hs.length = r ∧ (∃ tail : List Node, hs = gs ++ tail) ∧
      (∀ i < n + gs.length, ∀ x : Fin n → Bool, wire n hs i x = wire n gs i x) ∧
      (∀ s : Finset ℕ, (∀ i ∈ s, i < n + gs.length) → ∀ x : Fin n → Bool,
        term n hs s x = term n gs s x) := by
  obtain ⟨tail,hlen,hv',hp',hd',hf'⟩ :=
    private_flat_padding_tail gs T hv hp hd hf j hj ha hb (r-gs.length)
  refine ⟨gs ++ tail,hv',hp',hd',hf',?_,⟨tail,rfl⟩,?_,?_⟩
  · simp only [List.length_append,hlen]
    omega
  · intro i hi x
    exact normal_append_old gs tail i hi x
  · intro s hs x
    exact normal_append_term gs tail s hs x

lemma pure_root_private_disjoint_flat_pad {n : ℕ} (gs : List Node)
    (T : Set (Fin n → Bool)) (hv : Valid n gs) (hp : PrivateNormal n gs T)
    (hd : DisjointNormal gs) (hf : FlatWitnesses n gs)
    (hex : ∃ j < gs.length, ∃ Q : Finset (Fin n), 2 ≤ Q.card ∧
      ∀ x : Fin n → Bool, wire n gs (n+j) x = H8Active.disjunction Q x)
    (r : ℕ) (hr : gs.length ≤ r) :
    ∃ hs : List Node, Valid n hs ∧ PrivateNormal n hs T ∧ DisjointNormal hs ∧
      FlatWitnesses n hs ∧ hs.length = r ∧ (∃ tail : List Node, hs = gs ++ tail) ∧
      (∀ i < n + gs.length, ∀ x : Fin n → Bool, wire n hs i x = wire n gs i x) ∧
      (∀ s : Finset ℕ, (∀ i ∈ s, i < n + gs.length) → ∀ x : Fin n → Bool,
        term n hs s x = term n gs s x) := by
  obtain ⟨j,hj,Q,hQ,he⟩ := hex
  obtain ⟨ha,hb⟩ := hf j hj Q hQ he
  exact private_disjoint_flat_pad gs T hv hp hd hf j hj ha hb r hr

lemma pure_term_private_disjoint_flat_pad {n : ℕ} (gs : List Node)
    (T : Set (Fin n → Bool)) (hv : Valid n gs) (hp : PrivateNormal n gs T)
    (hd : DisjointNormal gs) (hf : FlatWitnesses n gs)
    (s : Finset ℕ) (hs : ∀ i ∈ s, i < n + gs.length)
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (he : ∀ x : Fin n → Bool, term n gs s x = H8Active.disjunction Q x)
    (r : ℕ) (hr : gs.length ≤ r) :
    ∃ ks : List Node, Valid n ks ∧ PrivateNormal n ks T ∧ DisjointNormal ks ∧
      FlatWitnesses n ks ∧ ks.length = r ∧ (∃ tail : List Node, ks = gs ++ tail) ∧
      (∀ i < n + gs.length, ∀ x : Fin n → Bool, wire n ks i x = wire n gs i x) ∧
      (∀ t : Finset ℕ, (∀ i ∈ t, i < n + gs.length) → ∀ x : Fin n → Bool,
        term n ks t x = term n gs t x) := by
  obtain ⟨j,hj,hroot⟩ := normal_pure_term_root n gs s Q hQ hs he
  exact pure_root_private_disjoint_flat_pad gs T hv hp hd hf ⟨j,hj,Q,hQ,hroot⟩ r hr

end H8AndFree

namespace H8AndFree

lemma exists_flat_private_output {n : ℕ} (gs : List Node)
    (T : Set (Fin n → Bool)) (hT : ∀ a : Fin n, H8Active.assignmentOf {a} ∈ T)
    (hv : Valid n gs) (hp : PrivateNormal n gs T)
    (s : Finset ℕ) (hs : s.Nonempty) (hb : ∀ i ∈ s, i < n + gs.length) :
    ∃ (ks : List Node) (t : Finset ℕ),
      Valid n ks ∧ PrivateNormal n ks T ∧ DisjointNormal ks ∧ FlatWitnesses n ks ∧
      ks.length ≤ gs.length ∧ t.Nonempty ∧ (∀ i ∈ t, i < n + ks.length) ∧
      (∀ x : Fin n → Bool, term n ks t x = term n gs s x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card →
        (∃ i < n + gs.length, ∀ x : Fin n → Bool, wire n gs i x = H8Active.disjunction Q x) →
        ∃ j < ks.length, ∀ x : Fin n → Bool, wire n ks (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨ks,m,hvalid,hprivate,hdisjoint,hflat,hcount,hsim⟩ :=
    exists_flat_private_simulation n gs T hT hv hp
  refine ⟨ks,expand m s,hvalid,hprivate,hdisjoint,hflat,hcount,
    expand_nonempty m s hs (fun i hi => (hsim i (hb i hi)).1),
    expand_bound m s _ (fun i hi => (hsim i (hb i hi)).2.1),term_expand hsim s hb,?_⟩
  intro Q hQ hroot
  obtain ⟨i,hi,hiQ⟩ := hroot
  apply normal_pure_term_root n ks (m i) Q hQ (hsim i hi).2.1
  intro x
  exact ((hsim i hi).2.2 x).trans (hiQ x)

end H8AndFree

namespace H8OrPatch

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4970.H8AndFree

lemma singleton_mem_test_inputs {n : ℕ} (P : Finset (Finset (Fin n))) (a : Fin n) :
    H8Active.assignmentOf {a} ∈ TestInputs P := by
  classical
  refine ⟨{a},?_,rfl⟩
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)

lemma exists_flat_private_normalization {n : ℕ}
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x)
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    ∃ (hs : List Node) (s : Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs (TestInputs P) ∧ DisjointNormal hs ∧ FlatWitnesses n hs ∧
      hs.length ≤ orCount C.gates ∧ s.Nonempty ∧ (∀ i ∈ s, i < n + hs.length) ∧
      (∀ x : Fin n → Bool, term n hs s x = H8Active.dnf P x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card → HasPureOr n C Q →
        ∃ j < hs.length, ∀ x : Fin n → Bool, wire n hs (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨gs,t,hvalid,hprivate,hcount,ht,hb,hout,hroots⟩ :=
    exists_private_normalization C hC P hF hpos
  obtain ⟨hs,s,hsvalid,hsprivate,hsdisjoint,hsflat,hscount,hsne,hsb,hsout,hsroots⟩ :=
    exists_flat_private_output gs (TestInputs P) (singleton_mem_test_inputs P) hvalid hprivate t ht hb
  refine ⟨hs,s,hsvalid,hsprivate,hsdisjoint,hsflat,hscount.trans hcount,hsne,hsb,?_,?_⟩
  · intro x
    exact (hsout x).trans (hout x)
  · intro Q hQ hQC
    obtain ⟨j,hj,hjQ⟩ := hroots Q hQ hQC
    exact hsroots Q hQ ⟨n+j,by omega,hjQ⟩

lemma exists_exact_flat_private_normalization {n : ℕ}
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x)
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hwitness : ∃ Q : Finset (Fin n), 2 ≤ Q.card ∧ HasPureOr n C Q)
    (r : ℕ) (hr : orCount C.gates ≤ r) :
    ∃ (hs : List Node) (s : Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs (TestInputs P) ∧ DisjointNormal hs ∧ FlatWitnesses n hs ∧
      hs.length = r ∧ s.Nonempty ∧ (∀ i ∈ s, i < n + hs.length) ∧
      (∀ x : Fin n → Bool, term n hs s x = H8Active.dnf P x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card → HasPureOr n C Q →
        ∃ j < hs.length, ∀ x : Fin n → Bool, wire n hs (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨gs,s,hv,hp,hd,hf,hcnt,hs,hb,hout,hroots⟩ :=
    exists_flat_private_normalization C hC P hF hpos
  have hgr : gs.length ≤ r := hcnt.trans hr
  have hgw : ∃ j < gs.length, ∃ Q : Finset (Fin n), 2 ≤ Q.card ∧
      ∀ x : Fin n → Bool, wire n gs (n+j) x = H8Active.disjunction Q x := by
    obtain ⟨Q,hQ,hQC⟩ := hwitness
    obtain ⟨j,hj,hjQ⟩ := hroots Q hQ hQC
    exact ⟨j,hj,Q,hQ,hjQ⟩
  obtain ⟨ks,hkv,hkp,hkd,hkf,hkcnt,hprefix,hkw,hkt⟩ :=
    pure_root_private_disjoint_flat_pad gs (TestInputs P) hv hp hd hf hgw r hgr
  refine ⟨ks,s,hkv,hkp,hkd,hkf,hkcnt,hs,?_,?_,?_⟩
  · intro i hi
    have hh := hb i hi
    omega
  · intro x
    exact (hkt s hb x).trans (hout x)
  · intro Q hQ hQC
    obtain ⟨j,hj,hjQ⟩ := hroots Q hQ hQC
    refine ⟨j,by omega,?_⟩
    intro x
    exact (hkw (n+j) (by omega) x).trans (hjQ x)

end H8OrPatch

namespace H8AndFree

def Before (a b : Finset ℕ) : Prop :=
  ∀ j ∈ b, ∃ i ∈ a, i < j

noncomputable def orientNode (g : Node) : Node := by
  classical
  exact if Before g.1 g.2 then g else (g.2,g.1)

def Oriented (gs : List Node) : Prop :=
  ∀ j (hj : j < gs.length), Before gs[j].1 gs[j].2

lemma before_or_reverse (a b : Finset ℕ) (ha : a.Nonempty) (hb : b.Nonempty)
    (hd : Disjoint a b) : Before a b ∨ Before b a := by
  have hne : a.min' ha ≠ b.min' hb := by
    intro he
    exact Finset.disjoint_left.mp hd (Finset.min'_mem a ha)
      (he ▸ Finset.min'_mem b hb)
  rcases lt_or_gt_of_ne hne with h | h
  · left
    intro j hj
    exact ⟨a.min' ha,Finset.min'_mem a ha,lt_of_lt_of_le h (Finset.min'_le b j hj)⟩
  · right
    intro i hi
    exact ⟨b.min' hb,Finset.min'_mem b hb,lt_of_lt_of_le h (Finset.min'_le a i hi)⟩

lemma orientNode_cases (g : Node) : orientNode g = g ∨ orientNode g = (g.2,g.1) := by
  classical
  unfold orientNode
  split_ifs <;> simp

lemma orientNode_before (g : Node) (ha : g.1.Nonempty) (hb : g.2.Nonempty)
    (hd : Disjoint g.1 g.2) : Before (orientNode g).1 (orientNode g).2 := by
  classical
  unfold orientNode
  split_ifs with h
  · exact h
  · exact (before_or_reverse g.1 g.2 ha hb hd).resolve_left h

lemma step_orientNode (w : List Bool) (g : Node) : step w (orientNode g) = step w g := by
  rcases orientNode_cases g with h | h
  · rw [h]
  · simp [h,step,Bool.or_comm]

lemma fold_orientNode (gs : List Node) (w : List Bool) :
    (gs.map orientNode).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons,List.foldl_cons,step_orientNode,ih]

lemma wire_orientNode (n : ℕ) (gs : List Node) (i : ℕ) (x : Fin n → Bool) :
    wire n (gs.map orientNode) i x = wire n gs i x := by
  simp [wire,values,fold_orientNode]

lemma term_orientNode (n : ℕ) (gs : List Node) (s : Finset ℕ) (x : Fin n → Bool) :
    term n (gs.map orientNode) s x = term n gs s x := by
  unfold term
  exact conj_congr (fun _ _ => wire_orientNode n gs _ x)

lemma valid_orientNode {n : ℕ} (gs : List Node) (hv : Valid n gs) :
    Valid n (gs.map orientNode) := by
  intro j hj
  have hj' : j < gs.length := by simpa using hj
  simp only [List.getElem_map]
  rcases orientNode_cases gs[j] with h | h
  · simpa only [h] using hv j hj'
  · obtain ⟨ha,hb,hba,hbb⟩ := hv j hj'
    simpa only [h] using And.intro hb (And.intro ha (And.intro hbb hba))

lemma private_orientNode {n : ℕ} (gs : List Node) (T : Set (Fin n → Bool))
    (hp : PrivateNormal n gs T) : PrivateNormal n (gs.map orientNode) T := by
  intro j hj
  have hj' : j < gs.length := by simpa using hj
  simp only [List.getElem_map,term_orientNode]
  rcases orientNode_cases gs[j] with h | h
  · simpa only [h] using hp j hj'
  · simpa only [h] using (hp j hj').symm

lemma disjoint_orientNode (gs : List Node) (hd : DisjointNormal gs) :
    DisjointNormal (gs.map orientNode) := by
  intro j hj
  have hj' : j < gs.length := by simpa using hj
  simp only [List.getElem_map]
  rcases orientNode_cases gs[j] with h | h
  · simpa only [h] using hd j hj'
  · simpa only [h] using (hd j hj').symm

lemma oriented_orientNode {n : ℕ} (gs : List Node) (hv : Valid n gs)
    (hd : DisjointNormal gs) : Oriented (gs.map orientNode) := by
  intro j hj
  have hj' : j < gs.length := by simpa using hj
  simpa only [List.getElem_map] using
    orientNode_before gs[j] (hv j hj').1 (hv j hj').2.1 (hd j hj')

lemma flat_orientNode {n : ℕ} (gs : List Node) (hf : FlatWitnesses n gs) :
    FlatWitnesses n (gs.map orientNode) := by
  intro j hj Q hQ hfun
  have hj' : j < gs.length := by simpa using hj
  have hh : ∀ x : Fin n → Bool, wire n gs (n+j) x = H8Active.disjunction Q x := by
    intro x
    simpa only [wire_orientNode] using hfun x
  have h := hf j hj' Q hQ hh
  simp only [List.getElem_map]
  rcases orientNode_cases gs[j] with he | he
  · simpa only [he] using h
  · simpa only [he] using h.symm

end H8AndFree

namespace H8OrPatch

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4970.H8AndFree

lemma exists_exact_oriented_flat_private_normalization {n : ℕ}
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (P : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H8Active.dnf P x)
    (hpos : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hwitness : ∃ Q : Finset (Fin n), 2 ≤ Q.card ∧ HasPureOr n C Q)
    (r : ℕ) (hr : orCount C.gates ≤ r) :
    ∃ (hs : List Node) (s : Finset ℕ),
      Valid n hs ∧ PrivateNormal n hs (TestInputs P) ∧ DisjointNormal hs ∧
      FlatWitnesses n hs ∧ Oriented hs ∧ hs.length = r ∧
      s.Nonempty ∧ (∀ i ∈ s, i < n + hs.length) ∧
      (∀ x : Fin n → Bool, term n hs s x = H8Active.dnf P x) ∧
      ∀ (Q : Finset (Fin n)), 2 ≤ Q.card → HasPureOr n C Q →
        ∃ j < hs.length, ∀ x : Fin n → Bool, wire n hs (n+j) x = H8Active.disjunction Q x := by
  obtain ⟨gs,s,hv,hp,hd,hf,hcnt,hs,hb,hout,hroots⟩ :=
    exists_exact_flat_private_normalization C hC P hF hpos hwitness r hr
  refine ⟨gs.map orientNode,s,valid_orientNode gs hv,
    private_orientNode gs _ hp,disjoint_orientNode gs hd,flat_orientNode gs hf,
    oriented_orientNode gs hv hd,?_,hs,?_,?_,?_⟩
  · simpa only [List.length_map] using hcnt
  · simpa only [List.length_map] using hb
  · intro x
    exact (term_orientNode n gs s x).trans (hout x)
  · intro Q hQ hQC
    obtain ⟨j,hj,hjQ⟩ := hroots Q hQ hQC
    refine ⟨j,by simpa using hj,?_⟩
    intro x
    exact (wire_orientNode n gs (n+j) x).trans (hjQ x)

end H8OrPatch

end PEqualNP.Outside.L_meta_4970
