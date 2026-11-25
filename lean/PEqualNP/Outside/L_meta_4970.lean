import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

namespace Kernel

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

def Pool {n} (F : Test n) (R : Set (Test n)) (c : ℕ) : Prop :=
  ∃ gs : List Gate, gs.length ≤ c ∧ Layout n gs ∧ Clean F gs ∧
    ∀ p ∈ R, Dirty F p ∧ ∃ i < n + gs.length, W n gs i = p

lemma pool_append {n} {F : Test n} {R c} (h : Pool F R c) {p q}
    (hp : p ∈ R) (hq : q ∈ R) (b : Bool) (hd : Dirty F (combine b p q)) :
    Pool F (insert (combine b p q) R) (c+1) := by
  classical
  obtain ⟨gs,hc,hl,hcl,hr⟩ := h
  obtain ⟨u,hu,hpu⟩ := (hr p hp).2
  obtain ⟨v,hv,hqv⟩ := (hr q hq).2
  let g := binary b u v
  have hn : W n (gs ++ [g]) (n+gs.length) = combine b p q := by
    rw [new_wire, hpu, hqv]
  refine ⟨gs ++ [g], by simp; omega, ?_, ?_, ?_⟩
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
  · intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact ⟨hd, n+gs.length, by simp, hn⟩
    · obtain ⟨hsd,i,hi,he⟩ := hr s hs
      exact ⟨hsd,i,by simp; omega,(old_wire hi g).trans he⟩

def Hit {n} (T : Finset (Term n)) (x : Fin n → Bool) : Prop :=
  ∃ t ∈ T, t.1 x ∧ t.2 x

def Covers {n} (T : Finset (Term n)) (f p : Test n) : Prop :=
  ∀ x, f x → Hit T x ∨ p x

def Repr {n} (R : Set (Test n)) (P T : Finset (Term n)) (f : Test n) : Prop :=
  (∃ p ∈ R, (∀ x, p x → f x) ∧ Covers T f p) ∨
  ∃ t ∈ P, Covers T f (fun x => t.1 x ∧ t.2 x)

def Sound {n} (F : Test n) (R : Set (Test n)) (P : Finset (Term n)) : Prop :=
  ∀ t ∈ P, t.1 ∈ R ∧ t.2 ∈ R ∧ ∀ x, t.1 x → t.2 x → F x

def Model {n} (F : Test n) (S : Set (Test n)) (k : ℕ) : Prop :=
  ∃ R P T c, Pool F R c ∧ Sound F R P ∧ T ⊆ P ∧
    c + P.card + T.card ≤ k ∧ ∀ f ∈ S, Repr R P T f

lemma hit_mono {n} {T U : Finset (Term n)} (h : T ⊆ U) {x} :
    Hit T x → Hit U x := fun ⟨t,ht,ha⟩ => ⟨t,h ht,ha⟩

lemma repr_mono {n} {R R' : Set (Test n)} {P P' T T' : Finset (Term n)} {f}
    (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T') (h : Repr R P T f) :
    Repr R' P' T' f := by
  have liftCov {a : Test n} (hc : Covers T f a) : Covers T' f a :=
    fun x hx => (hc x hx).imp (hit_mono ht) id
  rcases h with ⟨p,hm,hl,hc⟩ | ⟨t,hm,hc⟩
  · exact Or.inl ⟨p,hr hm,hl,liftCov hc⟩
  · exact Or.inr ⟨t,hp hm,liftCov hc⟩

lemma combine_comm {n} (b) (f g : Test n) :
    combine b f g = combine b g f := by
  funext x
  cases b <;> simp [combine, and_comm, or_comm]

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

lemma model_add {n} {F : Test n} {S k} (h : Model F S k)
    {f g} (hf : f ∈ S) (hg : g ∈ S) (b) :
    Model F (insert (combine b f g) S) (k+1) := by
  classical
  obtain ⟨R,P,T,c,pool,sound,sub,budget,reps⟩ := h
  have finish {s : Test n} {R' P' T' c'}
      (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T')
      (pl : Pool F R' c') (so : Sound F R' P') (su : T' ⊆ P')
      (bu : c'+P'.card+T'.card ≤ k+1) (rep : Repr R' P' T' s) :
      Model F (insert s S) (k+1) := by
    refine ⟨R',P',T',c',pl,so,su,bu,?_⟩
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact rep
    · exact repr_mono hr hp ht (reps a ha)
  have virtual {a d : Test n} {t} (ht : t ∈ P)
      (hc : Covers T a (fun x => t.1 x ∧ t.2 x)) (hd : Repr R P T d) :
      Model F (insert (combine b a d) S) (k+1) := by
    cases b
    · let U := insert t T
      have incl : T ⊆ U := Finset.subset_insert t T
      have cover {s : Test n} (cs : Covers T d s) : Covers U (combine false a d) s := by
        intro x hx
        rcases hx with ha | hd'
        · rcases hc x ha with hh | hh
          · exact Or.inl (hit_mono incl hh)
          · exact Or.inl ⟨t,Finset.mem_insert_self _ _,hh⟩
        · exact (cs x hd').imp (hit_mono incl) id
      apply finish (Set.Subset.rfl) (Finset.Subset.refl _) incl pool sound
        (Finset.insert_subset ht sub) (by have := Finset.card_insert_le t T; dsimp [U]; omega)
      rcases hd with ⟨q,hq,hlo,hcov⟩ | ⟨s,hs,hcov⟩
      · exact Or.inl ⟨q,hq,fun x hx => Or.inr (hlo x hx),cover hcov⟩
      · exact Or.inr ⟨s,hs,cover hcov⟩
    · exact finish (Set.Subset.rfl) (Finset.Subset.refl _) (Finset.Subset.refl _) pool sound sub (by omega)
        (Or.inr ⟨t,ht,fun x hx => hc x hx.1⟩)
  have rf := reps f hf
  have rg := reps g hg
  rcases rf with ⟨p,hp,lp,cp⟩ | ⟨t,ht,ct⟩
  · rcases rg with ⟨q,hq,lq,cq⟩ | ⟨t,ht,ct⟩
    · have cov := cov_combine b cp cq
      by_cases dirty : Dirty F (combine b p q)
      · have hr : R ⊆ insert (combine b p q) R := Set.subset_insert _ _
        refine finish hr (Finset.Subset.refl _) (Finset.Subset.refl _) (pool_append pool hp hq b dirty) ?_ sub (by omega) ?_
        · intro t ht
          obtain ⟨ha,hb,hf⟩ := sound t ht
          exact ⟨hr ha,hr hb,hf⟩
        · refine Or.inl ⟨combine b p q, Set.mem_insert _ _, ?_,cov⟩
          intro x hx
          cases b
          · exact hx.elim (fun h => Or.inl (lp x h)) (fun h => Or.inr (lq x h))
          · exact ⟨lp x hx.1,lq x hx.2⟩
      · cases b
        · obtain ⟨gs,-,-,-,hr⟩ := pool
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
    · rw [combine_comm b f g]
      exact virtual ht ct (Or.inl ⟨p,hp,lp,cp⟩)
  · exact virtual ht ct rg

def Signals (n : ℕ) (gs : List Gate) : Set (Test n) :=
  {p | ∃ i < n + gs.length, W n gs i = p}

lemma simulate {n} (F : Test n) (inputs : ∀ i < n, Dirty F (W n [] i))
    (gs : List Gate) (hl : Layout n gs) : Model F (Signals n gs) gs.length := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Signals n [], ∅, ∅, 0, ?_, by simp [Sound], by simp, by simp, ?_⟩
    · refine ⟨[],by simp,by simp [Layout],by simp [Clean],?_⟩
      intro p hp
      obtain ⟨i,hi,rfl⟩ := hp
      exact ⟨inputs i (by simpa using hi), i,hi,rfl⟩
    · intro p hp
      exact Or.inl ⟨p,hp,fun _ => id, fun _ hx => Or.inr hx⟩
  | append_singleton gs last ih =>
    have layout : Layout n gs := by
      intro i hi
      obtain ⟨b,u,v,he,hu,hv⟩ := hl i (by simp; omega)
      exact ⟨b,u,v, (List.getElem_append_left hi).symm.trans he,hu,hv⟩
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst last
    have h := model_add (ih layout) (f := W n gs u) (g := W n gs v)
      ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩ b
    obtain ⟨R,P,T,c,hp,hs,ht,hb,hr⟩ := h
    refine ⟨R,P,T,c,hp,hs,ht,by simpa using hb,?_⟩
    intro p hm
    obtain ⟨i,hi,rfl⟩ := hm
    by_cases hj : i < n + gs.length
    · rw [old_wire hj]
      exact hr _ (Set.mem_insert_of_mem _ ⟨i,hj,rfl⟩)
    · have : i = n+gs.length := by simp at hi; omega
      subst i
      rw [new_wire]
      exact hr _ (Set.mem_insert _ _)


def Edge {n m} (E : Finset (Fin n × Fin m)) : Test (n+m) :=
  fun x => ∃ p l, (p,l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true

lemma input_dirty {n m} (E : Finset (Fin n × Fin m)) (i : ℕ) (hi : i < n+m) :
    Dirty (Edge E) (W (n+m) [] i) := by
  let x (j : Fin (n+m)) := decide (j.val = i)
  refine ⟨x,by simp [W, List.getD, hi, x],?_⟩
  rintro ⟨p,l,-,hp,hh⟩
  simp [x] at hp hh
  have := p.isLt
  omega

lemma wire_mono {n} (gs : List Gate) (hl : Layout n gs) (i : ℕ)
    (hi : i < n + gs.length) (x y : Fin n → Bool)
    (hxy : ∀ j, x j = true → y j = true) : W n gs i x → W n gs i y := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    have hn : i < n := by simpa using hi
    simpa [W, List.getD, hn] using hxy ⟨i, hn⟩
  | append_singleton gs last ih =>
    have layout : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := hl j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst last
    by_cases hj : i < n + gs.length
    · rw [old_wire hj]
      exact ih layout i hj
    · have heq : i = n + gs.length := by simp at hi; omega
      subst i
      rw [new_wire]
      have hlu := ih layout u hu
      have hlv := ih layout v hv
      cases b
      · exact fun h => h.elim (fun h => Or.inl (hlu h)) (fun h => Or.inr (hlv h))
      · exact fun h => ⟨hlu h.1, hlv h.2⟩

def disjunction {n : ℕ} (Q : Finset (Fin n)) : Test n :=
  fun x => ∃ q ∈ Q, x q = true

def singletonInput {n : ℕ} (q : Fin n) : Fin n → Bool :=
  fun j => decide (j = q)

lemma pure_repr {n} (F : Test n) (R : Set (Test n)) (P T : Finset (Term n))
    (gs : List Gate) (hl : Layout n gs)
    (hr : ∀ p ∈ R, ∃ i < n + gs.length, W n gs i = p)
    (hs : Sound F R P) (ht : T ⊆ P)
    (hf : ∀ q, ¬ F (singletonInput q))
    (Q : Finset (Fin n)) (hne : Q.Nonempty)
    (hrep : Repr R P T (disjunction Q)) :
    ∃ i < n + gs.length, W n gs i = disjunction Q := by
  have single_disj (q : Fin n) (hq : q ∈ Q) :
      disjunction Q (singletonInput q) := ⟨q,hq,by simp [singletonInput]⟩
  have single_not_hit (q : Fin n) : ¬ Hit T (singletonInput q) := by
    rintro ⟨t,hm,ha,hb⟩
    exact hf q ((hs t (ht hm)).2.2 _ ha hb)
  rcases hrep with ⟨p,hp,hlo,hcov⟩ | ⟨t,htp,hcov⟩
  · obtain ⟨i,hi,hpi⟩ := hr p hp
    refine ⟨i,hi,?_⟩
    funext x
    apply propext
    constructor
    · rw [hpi]
      exact hlo x
    · rintro ⟨q,hq,hx⟩
      have hpq : p (singletonInput q) :=
        (hcov _ (single_disj q hq)).resolve_left (single_not_hit q)
      rw [← hpi] at hpq
      apply wire_mono gs hl i hi (singletonInput q) x _ hpq
      intro j hj
      have : j = q := by simpa [singletonInput] using hj
      simpa [this] using hx
  · obtain ⟨q,hq⟩ := hne
    have hpair := (hcov _ (single_disj q hq)).resolve_left (single_not_hit q)
    exact (hf q ((hs t htp).2.2 _ hpair.1 hpair.2)).elim

lemma extract_preserving {n} (F : Test n) (inputs : ∀ i < n, Dirty F (W n [] i))
    (C : Circuit) (hl : IsAO2 n C) (hne : ∃ x, F x)
    (ho : W n C.gates C.output = F)
    (hf : ∀ q, ¬ F (singletonInput q)) :
    ∃ (gs : List Gate) (U : Finset (ℕ × ℕ)), Layout n gs ∧ Clean F gs ∧
      (∀ t ∈ U, ∀ x, W n gs t.1 x → W n gs t.2 x → F x) ∧
      (∀ x, F x → ∃ t ∈ U, W n gs t.1 x ∧ W n gs t.2 x) ∧
      gs.length + 2 * U.card ≤ C.size + 1 ∧
      ∀ i < n + C.gates.length, ∀ Q : Finset (Fin n), Q.Nonempty →
        W n C.gates i = disjunction Q →
        ∃ j < n + gs.length, W n gs j = disjunction Q := by
  classical
  obtain ⟨R,P,T,c,pool,sound,sub,budget,reps⟩ :=
    simulate F inputs C.gates (layout_of hl)
  have hout : C.output < n+C.gates.length := by
    by_contra! h
    obtain ⟨x,hx⟩ := hne
    rw [← ho] at hx
    have hlen := length_fold C.gates (List.ofFn x)
    simp only [List.length_ofFn] at hlen
    simp [W, List.getD, List.getElem?_eq_none (hlen ▸ h :
        (C.gates.foldl step (List.ofFn x)).length ≤ C.output)] at hx
  obtain ⟨gs,hc,hg,hclean,real⟩ := pool
  have rep := reps F ⟨C.output,hout,ho⟩
  rcases rep with ⟨p,hp,hlo,-⟩ | ⟨t,ht,hcov⟩
  · obtain ⟨x,hx,hn⟩ := (real p hp).1
    exact (hn (hlo x hx)).elim
  · let U := insert t T
    have hu : U ⊆ P := Finset.insert_subset ht sub
    have cu := Finset.card_le_card hu
    have ct : U.card ≤ T.card + 1 := Finset.card_insert_le t T
    let index (p : Test n) : ℕ := if hp : p ∈ R then ((real p hp).2).choose else 0
    have idx {p : Test n} (hp : p ∈ R) : W n gs (index p) = p := by
      simpa [index,hp] using ((real p hp).2).choose_spec.2
    let enc (s : Term n) := (index s.1, index s.2)
    refine ⟨gs,U.image enc,hg,hclean,?_,?_,?_,?_⟩
    · intro v hv
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨ha,hb,hsafe⟩ := sound s (hu hs)
      simpa only [enc, idx ha, idx hb] using hsafe
    · intro x hx
      have hit : Hit U x := by
        rcases hcov x hx with hh | hh
        · exact hit_mono (Finset.subset_insert t T) hh
        · exact ⟨t, Finset.mem_insert_self _ _, hh⟩
      obtain ⟨s,hs,ha,hb⟩ := hit
      obtain ⟨hm,hn,-⟩ := sound s (hu hs)
      exact ⟨enc s,Finset.mem_image_of_mem enc hs, by simpa only [enc,idx hm] using ha,
        by simpa only [enc,idx hn] using hb⟩
    · have h := Finset.card_image_le (s := U) (f := enc)
      unfold Circuit.size
      omega
    · intro i hi Q hneQ hQ
      have hrep : Repr R P T (disjunction Q) := by
        rw [← hQ]
        exact reps _ ⟨i,hi,rfl⟩
      exact pure_repr F R P T gs hg (fun p hp => (real p hp).2)
        sound sub hf Q hneQ hrep

lemma edge_singleton_false {p l : ℕ} (E : Finset (Fin p × Fin l))
    (q : Fin (p+l)) : ¬ Edge E (singletonInput q) := by
  rintro ⟨a,b,he,ha,hb⟩
  have hqa : Fin.castAdd l a = q := by simpa [singletonInput] using ha
  have hqb : Fin.natAdd p b = q := by simpa [singletonInput] using hb
  have hval := congrArg Fin.val (hqa.trans hqb.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  have := a.isLt
  omega

lemma graph_extract_preserving (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hne : E.Nonempty) (hao : IsAO2 (p+l) C)
    (hfun : ∀ x : Fin (p+l) → Bool,
      circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ (D : Circuit) (U : Finset (ℕ × ℕ)),
      IsAO2 (p+l) D ∧
      (∀ j < D.gates.length, (gateAt D j).op = .and →
        ∃ x : Fin (p+l) → Bool,
          (D.wires (List.ofFn x)).getD (p+l+j) false = true ∧ ¬ Edge E x) ∧
      (∀ t ∈ U, ∀ x : Fin (p+l) → Bool,
        (D.wires (List.ofFn x)).getD t.1 false = true →
        (D.wires (List.ofFn x)).getD t.2 false = true → Edge E x) ∧
      (∀ x : Fin (p+l) → Bool, Edge E x → ∃ t ∈ U,
        (D.wires (List.ofFn x)).getD t.1 false = true ∧
        (D.wires (List.ofFn x)).getD t.2 false = true) ∧
      D.size + 2 * U.card ≤ C.size + 1 ∧
      ∀ i < p+l+C.gates.length, ∀ Q : Finset (Fin (p+l)), Q.Nonempty →
        (∀ x : Fin (p+l) → Bool,
          (C.wires (List.ofFn x)).getD i false = decide (∃ q ∈ Q, x q = true)) →
        ∃ j < p+l+D.gates.length, ∀ x : Fin (p+l) → Bool,
          (D.wires (List.ofFn x)).getD j false = decide (∃ q ∈ Q, x q = true) := by
  have hn : ∃ x, Edge E x := by
    obtain ⟨⟨a,b⟩,he⟩ := hne
    exact ⟨fun _ => true,a,b,he,rfl,rfl⟩
  have ho : W (p+l) C.gates C.output = Edge E := by
    funext x
    change (circuitFun (p+l) C x = true) = _
    rw [hfun]
    simp [Edge]
  obtain ⟨gs,U,hl,hclean,hs,hcov,hbudget,hpres⟩ :=
    extract_preserving (Edge E) (input_dirty E) C hao hn ho (edge_singleton_false E)
  refine ⟨⟨gs,0⟩,U,layout_ao hl,?_,hs,hcov,hbudget,?_⟩
  · intro j hj hand
    apply hclean j hj
    simpa [gateAt, List.getD, hj] using hand
  · intro i hi Q hneQ hQ
    have hQ' : W (p+l) C.gates i = disjunction Q := by
      funext x
      change ((C.wires (List.ofFn x)).getD i false = true) = _
      rw [hQ]
      simp [disjunction]
    obtain ⟨j,hj,hjQ⟩ := hpres i hi Q hneQ hQ'
    refine ⟨j,hj,?_⟩
    intro x
    apply Bool.eq_iff_iff.mpr
    change W (p+l) gs j x ↔ decide (∃ q ∈ Q, x q = true) = true
    rw [hjQ]
    simp [disjunction]

lemma factor_eq_disjunction {n} (Q : Finset (Fin n)) (f : Test n)
    (hm : ∀ x y, (∀ j, x j = true → y j = true) → f x → f y)
    (hcontains : ∀ x, disjunction Q x → f x)
    (hz : ¬ f (fun j => decide (j ∉ Q))) : f = disjunction Q := by
  funext x
  apply propext
  refine ⟨?_,hcontains x⟩
  intro hfx
  by_contra hn
  apply hz
  apply hm x (fun j => decide (j ∉ Q)) _ hfx
  intro j hj
  have hjn : j ∉ Q := fun hjQ => hn ⟨j,hjQ,hj⟩
  simp [hjn]

lemma and_eq_disjunction {n} (Q : Finset (Fin n)) (f g : Test n)
    (hf : ∀ x y, (∀ j, x j = true → y j = true) → f x → f y)
    (hg : ∀ x y, (∀ j, x j = true → y j = true) → g x → g y)
    (h : combine true f g = disjunction Q) :
    f = disjunction Q ∨ g = disjunction Q := by
  have hcontains x : disjunction Q x → f x ∧ g x := by
    rw [← h]
    exact id
  have hz : ¬ disjunction Q (fun j => decide (j ∉ Q)) := by
    rintro ⟨q,hq,h⟩
    simp [hq] at h
  have hneg : ¬ (f (fun j => decide (j ∉ Q)) ∧ g (fun j => decide (j ∉ Q))) := by
    intro hh
    apply hz
    rw [← h]
    exact hh
  rcases not_and_or.mp hneg with hzf | hzg
  · exact Or.inl (factor_eq_disjunction Q f hf (fun x hx => (hcontains x hx).1) hzf)
  · exact Or.inr (factor_eq_disjunction Q g hg (fun x hx => (hcontains x hx).2) hzg)

lemma input_wire {n} (gs : List Gate) (i : ℕ) (hi : i < n) :
    W n gs i = fun x => x ⟨i,hi⟩ = true := by
  induction gs using List.reverseRecOn with
  | nil => funext x; simp [W, List.getD, hi]
  | append_singleton gs last ih => rw [old_wire (by omega),ih]

lemma wire_decompose {n} (gs : List Gate) (hl : Layout n gs) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gs.length) :
    ∃ j b u v, ∃ hj : j < gs.length,
      w = n+j ∧ gs[j] = binary b u v ∧ u < w ∧ v < w ∧
      W n gs w = combine b (W n gs u) (W n gs v) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hw; omega
  | append_singleton gs last ih =>
    have layout : Layout n gs := by
      intro j hj
      obtain ⟨b,u,v,he,hu,hv⟩ := hl j (by simp; omega)
      exact ⟨b,u,v,(List.getElem_append_left hj).symm.trans he,hu,hv⟩
    by_cases hlt : w < n + gs.length
    · obtain ⟨j,b,u,v,hj,heq,hgate,hu,hv,hsem⟩ := ih layout hlt
      refine ⟨j,b,u,v,by simp; omega,heq,?_,hu,hv,?_⟩
      · simpa [List.getElem_append_left hj] using hgate
      · rw [old_wire hlt,old_wire (by omega : u < n + gs.length),
          old_wire (by omega : v < n + gs.length)]
        exact hsem
    · have hw' : w = n + gs.length := by simp at hw; omega
      obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
      have hg : last = binary b u v := by simpa using he
      subst last
      refine ⟨gs.length,b,u,v,by simp,hw',by simp,by omega,by omega,?_⟩
      rw [hw',new_wire,old_wire hu,old_wire hv]

lemma pure_or_root {n} (gs : List Gate) (hl : Layout n gs) (w : ℕ)
    (hw : w < n + gs.length) (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (heq : W n gs w = disjunction Q) :
    ∃ j < gs.length, (gateAt ⟨gs,0⟩ j).op = .or ∧
      W n gs (n+j) = disjunction Q := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · have hQsub : Q ⊆ {⟨w,hn⟩} := by
        intro q hq
        have ht : W n gs w (singletonInput q) := by
          rw [heq]
          exact ⟨q,hq,by simp [singletonInput]⟩
        rw [input_wire gs w hn] at ht
        simpa [singletonInput, eq_comm] using ht
      have := Finset.card_le_card hQsub
      simp only [Finset.card_singleton] at this
      omega
    · obtain ⟨j,b,u,v,hj,hwj,hgate,hu,hv,hsem⟩ :=
        wire_decompose gs hl w (by omega) hw
      cases b
      · refine ⟨j,hj,?_,?_⟩
        · simp [gateAt,List.getD,hj,hgate,binary]
        · simpa [← hwj] using heq
      · have hf := wire_mono gs hl u (by omega)
        have hg := wire_mono gs hl v (by omega)
        rcases and_eq_disjunction Q (W n gs u) (W n gs v) hf hg (hsem.symm.trans heq) with he | he
        · exact ih u hu (by omega) he
        · exact ih v hv (by omega) he

lemma dirty_repr {n} (F : Test n) (R : Set (Test n)) (P T : Finset (Term n))
    (hs : Sound F R P) (ht : T ⊆ P) (f : Test n) (hd : Dirty F f)
    (hrep : Repr R P T f) :
    ∃ p ∈ R, (∀ x, p x → f x) ∧ ∀ x, ¬ F x → (p x ↔ f x) := by
  have no_hit (x : Fin n → Bool) (hx : ¬ F x) : ¬ Hit T x := by
    rintro ⟨t,hm,ha,hb⟩
    exact hx ((hs t (ht hm)).2.2 x ha hb)
  rcases hrep with ⟨p,hp,hlo,hcov⟩ | ⟨t,htp,hcov⟩
  · refine ⟨p,hp,hlo,?_⟩
    intro x hx
    exact ⟨hlo x,fun hfx => (hcov x hfx).resolve_left (no_hit x hx)⟩
  · obtain ⟨x,hfx,hx⟩ := hd
    have hh := (hcov x hfx).resolve_left (no_hit x hx)
    exact (hx ((hs t htp).2.2 x hh.1 hh.2)).elim

lemma circuit_pure_or_root {n : ℕ} (C : Circuit) (hao : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length) (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (heq : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD w false = decide (∃ q ∈ Q, x q = true)) :
    ∃ j < C.gates.length, (gateAt C j).op = .or ∧
      ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n+j) false = decide (∃ q ∈ Q, x q = true) := by
  have hW : W n C.gates w = disjunction Q := by
    funext x
    change ((C.wires (List.ofFn x)).getD w false = true) = _
    rw [heq]
    simp [disjunction]
  obtain ⟨j,hj,hop,hsem⟩ := pure_or_root C.gates (layout_of hao) w hw Q hQ hW
  refine ⟨j,hj,hop,?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  change W n C.gates (n+j) x ↔ decide (∃ q ∈ Q, x q = true) = true
  rw [hsem]
  simp [disjunction]

lemma graph_extract_star_witnesses (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hne : E.Nonempty) (hao : IsAO2 (p+l) C)
    (hfun : ∀ x : Fin (p+l) → Bool,
      circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ (D : Circuit) (U : Finset (ℕ × ℕ)),
      IsAO2 (p+l) D ∧
      (∀ j < D.gates.length, (gateAt D j).op = .and →
        ∃ x : Fin (p+l) → Bool,
          (D.wires (List.ofFn x)).getD (p+l+j) false = true ∧ ¬ Edge E x) ∧
      (∀ t ∈ U, ∀ x : Fin (p+l) → Bool,
        (D.wires (List.ofFn x)).getD t.1 false = true →
        (D.wires (List.ofFn x)).getD t.2 false = true → Edge E x) ∧
      (∀ x : Fin (p+l) → Bool, Edge E x → ∃ t ∈ U,
        (D.wires (List.ofFn x)).getD t.1 false = true ∧
        (D.wires (List.ofFn x)).getD t.2 false = true) ∧
      D.size + 2 * U.card ≤ C.size + 1 ∧
      ∀ i < p+l+C.gates.length, ∀ Q : Finset (Fin (p+l)), 2 ≤ Q.card →
        (∀ x : Fin (p+l) → Bool,
          (C.wires (List.ofFn x)).getD i false = decide (∃ q ∈ Q, x q = true)) →
        ∃ j < D.gates.length, (gateAt D j).op = .or ∧
          ∀ x : Fin (p+l) → Bool,
            (D.wires (List.ofFn x)).getD (p+l+j) false = decide (∃ q ∈ Q, x q = true) := by
  obtain ⟨D,U,hD,hd,hs,hcov,hbudget,hpres⟩ :=
    graph_extract_preserving p l E C hne hao hfun
  refine ⟨D,U,hD,hd,hs,hcov,hbudget,?_⟩
  intro i hi Q hQ heq
  have hneQ : Q.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w,hw,hsem⟩ := hpres i hi Q hneQ heq
  exact circuit_pure_or_root D hD w hw Q hQ hsem

def StarServed (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true)))

lemma star_served_transfer (p l : ℕ) (E : Finset (Fin p × Fin l)) (C D : Circuit)
    (hpres : ∀ i < p+l+C.gates.length, ∀ Q : Finset (Fin (p+l)), 2 ≤ Q.card →
      (∀ x : Fin (p+l) → Bool,
        (C.wires (List.ofFn x)).getD i false = decide (∃ q ∈ Q, x q = true)) →
      ∃ j < D.gates.length, (gateAt D j).op = .or ∧
        ∀ x : Fin (p+l) → Bool,
          (D.wires (List.ofFn x)).getD (p+l+j) false = decide (∃ q ∈ Q, x q = true))
    (hserved : StarServed p l E C) : StarServed p l E D := by
  intro a b he
  rcases hserved a b he with ⟨j,Q,hj,hop,hQ,hb,hadj,hsem⟩ | ⟨j,P,hj,hop,hP,ha,hadj,hsem⟩
  · have hinj : Function.Injective (Fin.natAdd p : Fin l → Fin (p+l)) := by
      intro a b hab
      apply Fin.ext
      have hv := congrArg Fin.val hab
      simp only [Fin.val_natAdd] at hv
      omega
    have hcard : (Q.image (Fin.natAdd p)).card = Q.card :=
      Finset.card_image_of_injective Q hinj
    have hbig : 2 ≤ (Q.image (Fin.natAdd p)).card := by rw [hcard]; exact hQ
    have hsem' : ∀ x : Fin (p+l) → Bool,
        (C.wires (List.ofFn x)).getD (p+l+j) false =
          decide (∃ q ∈ Q.image (Fin.natAdd p), x q = true) := by
      intro x
      simpa only [Finset.exists_mem_image] using hsem x
    obtain ⟨k,hk,hkop,hksem⟩ := hpres (p+l+j) (by omega) (Q.image (Fin.natAdd p)) hbig hsem'
    refine Or.inl ⟨k,Q,hk,hkop,hQ,hb,hadj,?_⟩
    intro x
    simpa only [Finset.exists_mem_image] using hksem x
  · have hinj : Function.Injective (Fin.castAdd l : Fin p → Fin (p+l)) := by
      intro a b hab
      apply Fin.ext
      simpa only [Fin.val_castAdd] using congrArg Fin.val hab
    have hcard : (P.image (Fin.castAdd l)).card = P.card :=
      Finset.card_image_of_injective P hinj
    have hbig : 2 ≤ (P.image (Fin.castAdd l)).card := by rw [hcard]; exact hP
    have hsem' : ∀ x : Fin (p+l) → Bool,
        (C.wires (List.ofFn x)).getD (p+l+j) false =
          decide (∃ q ∈ P.image (Fin.castAdd l), x q = true) := by
      intro x
      simpa only [Finset.exists_mem_image] using hsem x
    obtain ⟨k,hk,hkop,hksem⟩ := hpres (p+l+j) (by omega) (P.image (Fin.castAdd l)) hbig hsem'
    refine Or.inr ⟨k,P,hk,hkop,hP,ha,hadj,?_⟩
    intro x
    simpa only [Finset.exists_mem_image] using hksem x

lemma graph_extract_served (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hne : E.Nonempty) (hao : IsAO2 (p+l) C)
    (hfun : ∀ x : Fin (p+l) → Bool,
      circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hserved : StarServed p l E C) :
    ∃ (D : Circuit) (U : Finset (ℕ × ℕ)),
      IsAO2 (p+l) D ∧
      (∀ j < D.gates.length, (gateAt D j).op = .and →
        ∃ x : Fin (p+l) → Bool,
          (D.wires (List.ofFn x)).getD (p+l+j) false = true ∧ ¬ Edge E x) ∧
      (∀ t ∈ U, ∀ x : Fin (p+l) → Bool,
        (D.wires (List.ofFn x)).getD t.1 false = true →
        (D.wires (List.ofFn x)).getD t.2 false = true → Edge E x) ∧
      (∀ x : Fin (p+l) → Bool, Edge E x → ∃ t ∈ U,
        (D.wires (List.ofFn x)).getD t.1 false = true ∧
        (D.wires (List.ofFn x)).getD t.2 false = true) ∧
      D.size + 2 * U.card ≤ C.size + 1 ∧ StarServed p l E D := by
  obtain ⟨D,U,hD,hd,hs,hcov,hbudget,hpres⟩ :=
    graph_extract_star_witnesses p l E C hne hao hfun
  exact ⟨D,U,hD,hd,hs,hcov,hbudget,star_served_transfer p l E C D hpres hserved⟩

lemma safe_leaf_budget {α : Type*} [DecidableEq α] (safe paid : ℕ → Prop)
    [DecidablePred paid] (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a < w, safe a ∧ T w ⊆ T a) ∨
      (paid w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b)) :
    ∀ M (W : Finset ℕ), (∀ w ∈ W, w < M ∧ safe w) →
      (W.biUnion T).card ≤ W.card + ((Finset.range M).filter paid).card := by
  intro M
  induction M with
  | zero =>
    intro W hW
    have hnil : W = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have := (hW w hw).1
      omega
    simp [hnil]
  | succ M ih =>
    intro W hW
    have hbudget : ((Finset.range M).filter paid).card ≤
        ((Finset.range (M+1)).filter paid).card := by
      apply Finset.card_le_card
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_range] at hw ⊢
      exact ⟨by omega,hw.2⟩
    by_cases hM : M ∈ W
    · have hW' : ∀ w ∈ W.erase M, w < M ∧ safe w := by
        intro w hw
        have he := Finset.mem_erase.mp hw
        have hh := hW w he.2
        exact ⟨by omega,hh.2⟩
      have hcard : W.card = (W.erase M).card + 1 := by
        rw [Finset.card_erase_of_mem hM]
        have := Finset.card_pos.mpr ⟨M,hM⟩
        omega
      have hU : W.biUnion T = T M ∪ (W.erase M).biUnion T := by
        conv_lhs => rw [← Finset.insert_erase hM]
        rw [Finset.biUnion_insert]
      rcases h M (hW M hM).2 with hsmall | ⟨a,ha,hsa,hsub⟩ | ⟨hpaid,a,b,ha,hb,hsa,hsb,hsub⟩
      · have hrec := ih (W.erase M) hW'
        have hunion := Finset.card_union_le (T M) ((W.erase M).biUnion T)
        rw [hU]
        omega
      · let W' := insert a (W.erase M)
        have hvalid : ∀ w ∈ W', w < M ∧ safe w := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact ⟨ha,hsa⟩
          · exact hW' w hw
        have hrec := ih W' hvalid
        have hsub' : W.biUnion T ⊆ W'.biUnion T := by
          rw [hU]
          change T M ∪ (W.erase M).biUnion T ⊆ (insert a (W.erase M)).biUnion T
          rw [Finset.biUnion_insert]
          exact Finset.union_subset_union hsub (Finset.Subset.refl _)
        have hcount := Finset.card_le_card hsub'
        have hcount' : W'.card ≤ (W.erase M).card + 1 := Finset.card_insert_le _ _
        omega
      · let W' := insert a (insert b (W.erase M))
        have hvalid : ∀ w ∈ W', w < M ∧ safe w := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact ⟨ha,hsa⟩
          · rcases Finset.mem_insert.mp hw with rfl | hw
            · exact ⟨hb,hsb⟩
            · exact hW' w hw
        have hrec := ih W' hvalid
        have hsub' : W.biUnion T ⊆ W'.biUnion T := by
          rw [hU]
          change T M ∪ (W.erase M).biUnion T ⊆
            (insert a (insert b (W.erase M))).biUnion T
          rw [Finset.biUnion_insert,Finset.biUnion_insert,← Finset.union_assoc]
          exact Finset.union_subset_union hsub (Finset.Subset.refl _)
        have hcount := Finset.card_le_card hsub'
        have hcount' : W'.card ≤ (W.erase M).card + 2 := by
          have h1 := Finset.card_insert_le a (insert b (W.erase M))
          have h2 := Finset.card_insert_le b (W.erase M)
          dsimp [W']
          omega
        have hsplit : ((Finset.range (M+1)).filter paid).card =
            ((Finset.range M).filter paid).card + 1 := by
          rw [Finset.range_add_one,Finset.filter_insert,ite_eq_left hpaid,
            Finset.card_insert_of_notMem (by simp)]
        omega
    · have hvalid : ∀ w ∈ W, w < M ∧ safe w := by
        intro w hw
        have hh := hW w hw
        have hwne : w ≠ M := fun hh => hM (hh ▸ hw)
        exact ⟨by omega,hh.2⟩
      have hrec := ih W hvalid
      omega

def complementInput {m : ℕ} (Q : Finset (Fin m)) : Fin m → Bool :=
  fun q => decide (q ∉ Q)

def restrictedSupport {n m : ℕ} (C : Circuit)
    (R : (Fin m → Bool) → Fin n → Bool) (Q : Finset (Fin m)) (w : ℕ) : Finset (Fin m) :=
  Q.filter fun q => (C.wires (List.ofFn (R (singletonInput q)))).getD w false = true

noncomputable def restrictedSafeOr {n m : ℕ} (C : Circuit)
    (R : (Fin m → Bool) → Fin n → Bool) (Q : Finset (Fin m)) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = .or ∧
      (C.wires (List.ofFn (R (complementInput Q)))).getD (n+j) false = false ∧
      2 ≤ (restrictedSupport C R Q (n+j)).card

lemma restrictedSupport_mem {n m : ℕ} (C : Circuit)
    (R : (Fin m → Bool) → Fin n → Bool) (Q : Finset (Fin m)) (w : ℕ) (q : Fin m) :
    q ∈ restrictedSupport C R Q w ↔ q ∈ Q ∧ W n C.gates w (R (singletonInput q)) := by
  simp only [restrictedSupport,Finset.mem_filter]
  rfl

lemma restricted_or_budget {n m : ℕ} (C : Circuit) (hao : IsAO2 n C)
    (R : (Fin m → Bool) → Fin n → Bool) (Q : Finset (Fin m))
    (hinput : ∀ i : Fin n, R (complementInput Q) i = false →
      (Q.filter fun q => R (singletonInput q) i = true).card ≤ 1)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hfun : ∀ x : Fin m → Bool,
      (C.wires (List.ofFn (R x))).getD w false = decide (∃ q ∈ Q, x q = true)) :
    Q.card ≤ 1 + (restrictedSafeOr C R Q).card := by
  classical
  let T := restrictedSupport C R Q
  let A := restrictedSafeOr C R Q
  let paid := fun w => w ∈ A.image (fun j => n+j)
  let safe := fun w => w < n + C.gates.length ∧ ¬ W n C.gates w (R (complementInput Q))
  have hsafe_root : safe w := by
    refine ⟨hw,?_⟩
    change ¬ (C.wires (List.ofFn (R (complementInput Q)))).getD w false = true
    rw [hfun]
    simp [complementInput]
  have hTroot : T w = Q := by
    ext q
    rw [restrictedSupport_mem]
    change (q ∈ Q ∧ (C.wires (List.ofFn (R (singletonInput q)))).getD w false = true) ↔ q ∈ Q
    rw [hfun]
    simp [singletonInput]
  have hstep : ∀ v, safe v → (T v).card ≤ 1 ∨
      (∃ a < v, safe a ∧ T v ⊆ T a) ∨
      (paid v ∧ ∃ a b, a < v ∧ b < v ∧ safe a ∧ safe b ∧ T v ⊆ T a ∪ T b) := by
    intro v hv
    by_cases hsmall : (T v).card ≤ 1
    · exact Or.inl hsmall
    by_cases hn : v < n
    · left
      have hvfalse : R (complementInput Q) ⟨v,hn⟩ = false := by
        have hh := hv.2
        rw [input_wire C.gates v hn] at hh
        simpa only [Bool.not_eq_true] using hh
      have hTinput : T v = Q.filter (fun q => R (singletonInput q) ⟨v,hn⟩ = true) := by
        ext q
        rw [restrictedSupport_mem]
        rw [input_wire C.gates v hn]
        simp
      rw [hTinput]
      exact hinput ⟨v,hn⟩ hvfalse
    · obtain ⟨j,b,a,d,hj,hvj,hgate,ha,hd,hsem⟩ :=
        wire_decompose C.gates (layout_of hao) v (by omega) hv.1
      have hnot : ¬ combine b (W n C.gates a) (W n C.gates d) (R (complementInput Q)) := by
        rw [← hsem]
        exact hv.2
      cases b
      · have hsides : ¬ W n C.gates a (R (complementInput Q)) ∧
            ¬ W n C.gates d (R (complementInput Q)) := by
          exact not_or.mp hnot
        right
        right
        refine ⟨?_,a,d,ha,hd,⟨by omega,hsides.1⟩,⟨by omega,hsides.2⟩,?_⟩
        · apply Finset.mem_image.mpr
          refine ⟨j,?_,hvj.symm⟩
          simp only [A,restrictedSafeOr,Finset.mem_filter,Finset.mem_range]
          refine ⟨hj,?_,?_,?_⟩
          · simp [gateAt,List.getD,hj,hgate,binary]
          · have hvf : (C.wires (List.ofFn (R (complementInput Q)))).getD v false = false := by
              have hh : ¬ (C.wires (List.ofFn (R (complementInput Q)))).getD v false = true := hv.2
              simpa only [Bool.not_eq_true] using hh
            simpa [hvj] using hvf
          · change 2 ≤ (T (n+j)).card
            rw [← hvj]
            omega
        · intro q hq
          have hh := (restrictedSupport_mem C R Q v q).mp hq
          rw [hsem] at hh
          rcases hh.2 with hh | hh
          · exact Finset.mem_union_left _ ((restrictedSupport_mem C R Q a q).mpr ⟨(restrictedSupport_mem C R Q v q).mp hq |>.1,hh⟩)
          · exact Finset.mem_union_right _ ((restrictedSupport_mem C R Q d q).mpr ⟨(restrictedSupport_mem C R Q v q).mp hq |>.1,hh⟩)
      · have hsides : ¬ W n C.gates a (R (complementInput Q)) ∨
            ¬ W n C.gates d (R (complementInput Q)) := not_and_or.mp hnot
        right
        left
        rcases hsides with hs | hs
        · refine ⟨a,ha,⟨by omega,hs⟩,?_⟩
          intro q hq
          have hh := (restrictedSupport_mem C R Q v q).mp hq
          rw [hsem] at hh
          exact (restrictedSupport_mem C R Q a q).mpr ⟨hh.1,hh.2.1⟩
        · refine ⟨d,hd,⟨by omega,hs⟩,?_⟩
          intro q hq
          have hh := (restrictedSupport_mem C R Q v q).mp hq
          rw [hsem] at hh
          exact (restrictedSupport_mem C R Q d q).mpr ⟨hh.1,hh.2.2⟩
  have hcount := safe_leaf_budget safe paid T hstep (n+C.gates.length) {w}
    (by intro v hv; simp only [Finset.mem_singleton] at hv; subst v; exact ⟨hw,hsafe_root⟩)
  have hfilter : (Finset.range (n+C.gates.length)).filter paid = A.image (fun j => n+j) := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_range,paid]
    constructor
    · exact fun h => h.2
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      have hj' : j < C.gates.length := (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
      exact ⟨by omega,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩
  have himage : (A.image (fun j => n+j)).card = A.card :=
    Finset.card_image_of_injective A (fun a b h => by omega)
  have hsing : ({w} : Finset ℕ).biUnion T = T w := by simp
  rw [hsing,hTroot,Finset.card_singleton,hfilter,himage] at hcount
  exact hcount

def rightTrueInput {p l : ℕ} (x : Fin p → Bool) : Fin (p+l) → Bool :=
  Fin.addCases x (fun _ => true)

lemma rightTrue_input_support {p l : ℕ} (Q : Finset (Fin p)) (i : Fin (p+l))
    (hi : rightTrueInput (l := l) (complementInput Q) i = false) :
    (Q.filter fun q => rightTrueInput (l := l) (singletonInput q) i = true).card ≤ 1 := by
  induction i using Fin.addCases with
  | left i =>
    have hsub : (Q.filter fun q => rightTrueInput (l := l) (singletonInput q) (Fin.castAdd l i) = true) ⊆ {i} := by
      intro q hq
      have hh := (Finset.mem_filter.mp hq).2
      simpa [rightTrueInput,singletonInput,eq_comm] using hh
    exact (Finset.card_le_card hsub).trans (by simp)
  | right i => simp [rightTrueInput] at hi

noncomputable def restrictedSafeOrWires {n m : ℕ} (C : Circuit)
    (R : (Fin m → Bool) → Fin n → Bool) (Q : Finset (Fin m)) : Finset ℕ :=
  (restrictedSafeOr C R Q).image (fun j => n+j)

lemma restrictedSafeOrWires_mem {n m : ℕ} (C : Circuit)
    (R : (Fin m → Bool) → Fin n → Bool) (Q : Finset (Fin m)) (w : ℕ) :
    w ∈ restrictedSafeOrWires C R Q ↔ ∃ j < C.gates.length,
      w = n+j ∧ (gateAt C j).op = .or ∧
      (C.wires (List.ofFn (R (complementInput Q)))).getD w false = false ∧
      2 ≤ (restrictedSupport C R Q w).card := by
  classical
  simp only [restrictedSafeOrWires,Finset.mem_image,restrictedSafeOr,
    Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨j,⟨hj,hop,hfalse,hcard⟩,rfl⟩
    exact ⟨j,hj,rfl,hop,hfalse,hcard⟩
  · rintro ⟨j,hj,rfl,hop,hfalse,hcard⟩
    exact ⟨j,⟨hj,hop,hfalse,hcard⟩,rfl⟩

lemma restrictedSafeOrWires_card {n m : ℕ} (C : Circuit)
    (R : (Fin m → Bool) → Fin n → Bool) (Q : Finset (Fin m)) :
    (restrictedSafeOrWires C R Q).card = (restrictedSafeOr C R Q).card := by
  classical
  exact Finset.card_image_of_injective _ (fun a b h => by omega)

lemma rightTrue_or_budget {p l : ℕ} (C : Circuit) (hao : IsAO2 (p+l) C)
    (Q : Finset (Fin p)) (w : ℕ) (hw : w < p+l+C.gates.length)
    (hfun : ∀ x : Fin p → Bool,
      (C.wires (List.ofFn (rightTrueInput (l := l) x))).getD w false =
        decide (∃ q ∈ Q, x q = true)) :
    Q.card ≤ 1 + (restrictedSafeOrWires C (rightTrueInput (l := l)) Q).card := by
  rw [restrictedSafeOrWires_card]
  exact restricted_or_budget C hao (rightTrueInput (l := l)) Q
    (rightTrue_input_support Q) w hw hfun

noncomputable def sampleRestriction {n m : ℕ}
    (z : Fin n → Bool) (sample : Fin m → Fin n → Bool)
    (x : Fin m → Bool) : Fin n → Bool :=
  if h : ∃ q, x q = true then sample (Classical.choose h) else z

lemma sampleRestriction_zero {n m : ℕ}
    (z : Fin n → Bool) (sample : Fin m → Fin n → Bool) :
    sampleRestriction z sample (complementInput Finset.univ) = z := by
  simp [sampleRestriction, complementInput]

lemma sampleRestriction_singleton {n m : ℕ}
    (z : Fin n → Bool) (sample : Fin m → Fin n → Bool) (q : Fin m) :
    sampleRestriction z sample (singletonInput q) = sample q := by
  classical
  have hex : ∃ r : Fin m, singletonInput q r = true := ⟨q, by simp [singletonInput]⟩
  have heq : Classical.choose hex = q := by
    simpa [singletonInput] using Classical.choose_spec hex
  simp only [sampleRestriction, dite_eq_left hex, heq]

lemma sample_or_budget_restriction {n m : ℕ} (C : Circuit) (hao : IsAO2 n C)
    (z : Fin n → Bool) (sample : Fin m → Fin n → Bool)
    (hinput : ∀ i : Fin n, z i = false →
      (Finset.univ.filter fun q => sample q i = true).card ≤ 1)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hz : (C.wires (List.ofFn z)).getD w false = false)
    (hsample : ∀ q, (C.wires (List.ofFn (sample q))).getD w false = true) :
    m ≤ 1 + (restrictedSafeOr C (sampleRestriction z sample) Finset.univ).card := by
  classical
  have hfun : ∀ x : Fin m → Bool,
      (C.wires (List.ofFn (sampleRestriction z sample x))).getD w false =
        decide (∃ q ∈ (Finset.univ : Finset (Fin m)), x q = true) := by
    intro x
    by_cases hx : ∃ q, x q = true
    · simp only [sampleRestriction, dite_eq_left hx]
      rw [hsample]
      simp [hx]
    · simp only [sampleRestriction, dite_eq_right hx]
      rw [hz]
      simp [hx]
  have hsmall : ∀ i : Fin n, sampleRestriction z sample (complementInput Finset.univ) i = false →
      (Finset.univ.filter fun q => sampleRestriction z sample (singletonInput q) i = true).card ≤ 1 := by
    intro i hi
    rw [sampleRestriction_zero] at hi
    simpa only [sampleRestriction_singleton] using hinput i hi
  simpa using restricted_or_budget C hao (sampleRestriction z sample) Finset.univ hsmall w hw hfun

noncomputable def sampleSafeOr {n m : ℕ} (C : Circuit)
    (z : Fin n → Bool) (sample : Fin m → Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = .or ∧
      (C.wires (List.ofFn z)).getD (n+j) false = false ∧
      2 ≤ (Finset.univ.filter fun q =>
        (C.wires (List.ofFn (sample q))).getD (n+j) false = true).card

lemma sampleSafeOr_eq_restricted {n m : ℕ} (C : Circuit)
    (z : Fin n → Bool) (sample : Fin m → Fin n → Bool) :
    sampleSafeOr C z sample =
      restrictedSafeOr C (sampleRestriction z sample) Finset.univ := by
  classical
  simp only [sampleSafeOr, restrictedSafeOr, restrictedSupport,
    sampleRestriction_zero, sampleRestriction_singleton]

lemma sample_or_budget {n m : ℕ} (C : Circuit) (hao : IsAO2 n C)
    (z : Fin n → Bool) (sample : Fin m → Fin n → Bool)
    (hinput : ∀ i : Fin n, z i = false →
      (Finset.univ.filter fun q => sample q i = true).card ≤ 1)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hz : (C.wires (List.ofFn z)).getD w false = false)
    (hsample : ∀ q, (C.wires (List.ofFn (sample q))).getD w false = true) :
    m ≤ 1 + (sampleSafeOr C z sample).card := by
  rw [sampleSafeOr_eq_restricted]
  exact sample_or_budget_restriction C hao z sample hinput w hw hz hsample

end Kernel

namespace Boundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : Finset (Fin 2 × Fin 2) := {(0, 0), (1, 0), (1, 1)}

def kernel : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.and, [1, 1]⟩, ⟨.or, [2, 7]⟩], 8⟩

def pairs : Finset (ℕ × ℕ) := {(6, 8)}

def edgeFun (x : Fin 4 → Bool) : Bool :=
  decide (∃ a b : Fin 2, (a, b) ∈ edges ∧
    x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true)

def wire (w : ℕ) (x : Fin 4 → Bool) : Bool :=
  (kernel.wires (List.ofFn x)).getD w false

def covers (S : Finset (Fin 4)) : Prop :=
  ∀ a b : Fin 2, (a, b) ∈ edges →
    Fin.castAdd 2 a ∈ S ∨ Fin.natAdd 2 b ∈ S

lemma no_four_cycle : ∀ a a' b b' : Fin 2,
    a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧ (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide +kernel

lemma kernel_ao2 : PEqualNP.TopForm.IsAO2 4 kernel := by
  decide +kernel

lemma kernel_tCount :
    PEqualNP.TwoColour.tCount 4 kernel (fun i => decide (2 ≤ i)) = 0 := by
  decide +kernel

lemma kernel_dirty : ∀ j : Fin kernel.gates.length,
    ∃ x : Fin 4 → Bool, wire (4 + j.val) x = true ∧ edgeFun x = false := by
  decide +kernel

lemma pair_exact : ∀ x : Fin 4 → Bool, (wire 6 x && wire 8 x) = edgeFun x := by
  decide +kernel

lemma pairs_valid : ∀ u ∈ pairs, u.1 < 4 + kernel.size ∧ u.2 < 4 + kernel.size := by
  decide +kernel

lemma pairs_safe : ∀ u ∈ pairs, ∀ x : Fin 4 → Bool,
    wire u.1 x = true → wire u.2 x = true → edgeFun x = true := by
  intro u hu x ha hb
  have he : u = (6, 8) := by simpa [pairs] using hu
  subst u
  have hh := pair_exact x
  simpa [ha, hb] using hh.symm

lemma pairs_cover : ∀ x : Fin 4 → Bool, edgeFun x = true →
    ∃ u ∈ pairs, wire u.1 x = true ∧ wire u.2 x = true := by
  intro x hx
  refine ⟨(6, 8), by simp [pairs], ?_⟩
  have hh := pair_exact x
  rw [hx] at hh
  simpa only [Bool.and_eq_true] using hh

lemma left_star : (NestedCover.gateAt kernel 0).op = GateOp.or ∧
    ∀ x : Fin 4 → Bool, wire 4 x =
      decide (∃ a ∈ (Finset.univ : Finset (Fin 2)), x (Fin.castAdd 2 a) = true) := by
  constructor
  · rfl
  · decide +kernel

lemma right_star : (NestedCover.gateAt kernel 1).op = GateOp.or ∧
    ∀ x : Fin 4 → Bool, wire 5 x =
      decide (∃ b ∈ (Finset.univ : Finset (Fin 2)), x (Fin.natAdd 2 b) = true) := by
  constructor
  · rfl
  · decide +kernel

lemma stars_serve : ∀ a b : Fin 2, (a, b) ∈ edges →
    (∃ (j : ℕ) (Q : Finset (Fin 2)),
      j < kernel.gates.length ∧ (NestedCover.gateAt kernel j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ edges) ∧
      ∀ x : Fin 4 → Bool, wire (4 + j) x =
        decide (∃ b' ∈ Q, x (Fin.natAdd 2 b') = true)) ∨
    (∃ (j : ℕ) (P : Finset (Fin 2)),
      j < kernel.gates.length ∧ (NestedCover.gateAt kernel j).op = GateOp.or ∧
      2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ edges) ∧
      ∀ x : Fin 4 → Bool, wire (4 + j) x =
        decide (∃ a' ∈ P, x (Fin.castAdd 2 a') = true)) := by
  intro a b hab
  by_cases hb : b = 0
  · subst b
    right
    refine ⟨0, Finset.univ, by decide, left_star.1, by decide, Finset.mem_univ a, ?_, ?_⟩
    · decide +kernel
    · exact left_star.2
  · have ha : a = 1 := by
      fin_cases a <;> fin_cases b <;> simp [edges] at hab hb ⊢
    subst a
    left
    refine ⟨1, Finset.univ, by decide, right_star.1, by decide, Finset.mem_univ b, ?_, ?_⟩
    · decide +kernel
    · exact right_star.2

lemma cover_lower : ∀ S : Finset (Fin 4), covers S → 2 ≤ S.card := by
  unfold covers
  decide +kernel

lemma cover_two : covers ({0, 1} : Finset (Fin 4)) ∧
    ({0, 1} : Finset (Fin 4)).card = 2 := by
  unfold covers
  decide +kernel

lemma pair_count_too_small : ∀ S : Finset (Fin 4), covers S → pairs.card < S.card := by
  intro S hs
  have h := cover_lower S hs
  have hp : pairs.card = 1 := by decide
  omega

lemma combined_budget_still_holds : edges.card + 2 ≤ kernel.size + 2 * pairs.card := by
  decide +kernel

end Boundary

namespace OneSided

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj



open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wireFn (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireFn_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (w : ℕ) :
    Monotone (wireFn n C w) := by
  intro x y hxy
  have hm : wireFn n C w x = true → wireFn n C w y = true := by
    apply wiresFrom_mono C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp)
    intro i hi
    by_cases hin : i < n
    · have hi' : x ⟨i, hin⟩ = true := by
        rw [List.getD_eq_getElem _ _ (by simpa using hin)] at hi
        simpa only [List.getElem_ofFn] using hi
      have hle := hxy ⟨i, hin⟩
      rw [List.getD_eq_getElem _ _ (by simpa using hin)]
      simpa only [List.getElem_ofFn] using (Bool.le_iff_imp.mp hle hi')
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hin)] at hi
      cases hi
  exact Bool.le_iff_imp.mpr hm

lemma wireFn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireFn n C w x = x ⟨w, hw⟩ := by
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma binary_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < n + j ∧ b < n + j ∧
      (gateAt C j).inputs = [a, b] ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ x, wireFn n C (n + j) x =
        (gateAt C j).op.eval [wireFn n C a x, wireFn n C b x] := by
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt_get C j hj]
    exact List.getElem_mem hj
  have hlen := hC.2.2 _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha : a < n + j := hC.2.1 j hj a (by simp [hab])
  have hb : b < n + j := hC.2.1 j hj b (by simp [hab])
  refine ⟨a, b, ha, hb, hab, hC.1 _ hmem, ?_⟩
  intro x
  unfold wireFn
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = _
  have he := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at he
  rw [he, ← gateAt_get C j hj, hab]
  simp [ha, hb, wiresFrom, Circuit.wires]

lemma safe_leaf_count {α : Type*} [DecidableEq α]
    (safe split : ℕ → Prop) [DecidablePred safe] [DecidablePred split]
    (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b)) :
    ∀ M (W : Finset ℕ), (∀ w ∈ W, w < M ∧ safe w) →
      (W.biUnion T).card ≤ W.card +
        ((Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)).card := by
  intro M
  induction M with
  | zero =>
    intro W hW
    have : W = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      exact Nat.not_lt_zero w (hW w hw).1
    subst W
    simp
  | succ M ih =>
    intro W hW
    let B := (Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)
    let B' := (Finset.range (M + 1)).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)
    have hmono : B.card ≤ B'.card := by
      apply Finset.card_le_card
      intro k hk
      simp only [B, B', Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2⟩
    change (W.biUnion T).card ≤ W.card + B'.card
    by_cases hM : M ∈ W
    · have hWe : W = insert M (W.erase M) := (Finset.insert_erase hM).symm
      have hW' : ∀ w ∈ W.erase M, w < M ∧ safe w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hcard : W.card = (W.erase M).card + 1 := by
        rw [Finset.card_erase_of_mem hM]
        have := Finset.card_pos.mpr ⟨M, hM⟩
        omega
      have hU : W.biUnion T = T M ∪ (W.erase M).biUnion T := by
        conv_lhs => rw [hWe]
        rw [Finset.biUnion_insert]
      by_cases hsmall : (T M).card ≤ 1
      · have ih1 := ih (W.erase M) hW'
        have hu := Finset.card_union_le (T M) ((W.erase M).biUnion T)
        rw [hU]
        change _ ≤ (W.erase M).card + B.card at ih1
        omega
      · rcases h M (hW M hM).2 with hs | hb | ⟨hsplit, a, b, ha, hb, hsa, hsb, hsub⟩
        · exact (hsmall hs).elim
        · obtain ⟨a, ha, hsa, hsub⟩ := hb
          let W2 := insert a (W.erase M)
          have hW2 : ∀ w ∈ W2, w < M ∧ safe w := by
            intro w hw
            simp only [W2, Finset.mem_insert] at hw
            rcases hw with rfl | hw
            · exact ⟨ha, hsa⟩
            · exact hW' w hw
          have hU2 : W.biUnion T ⊆ W2.biUnion T := by
            rw [hU]
            simp only [W2, Finset.biUnion_insert]
            exact Finset.union_subset_union_left hsub
          have hc2 : W2.card ≤ (W.erase M).card + 1 := Finset.card_insert_le ..
          have ih2 := ih W2 hW2
          change _ ≤ W2.card + B.card at ih2
          have hu2 := Finset.card_le_card hU2
          omega
        · let W2 := insert a (insert b (W.erase M))
          have hW2 : ∀ w ∈ W2, w < M ∧ safe w := by
            intro w hw
            simp only [W2, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨ha, hsa⟩
            · exact ⟨hb, hsb⟩
            · exact hW' w hw
          have hU2 : W.biUnion T ⊆ W2.biUnion T := by
            rw [hU]
            simp only [W2, Finset.biUnion_insert]
            rw [← Finset.union_assoc]
            exact Finset.union_subset_union_left hsub
          have hc2 : W2.card ≤ (W.erase M).card + 2 := by
            have e1 := Finset.card_insert_le a (insert b (W.erase M))
            have e2 := Finset.card_insert_le b (W.erase M)
            dsimp [W2]
            omega
          have ih2 := ih W2 hW2
          change _ ≤ W2.card + B.card at ih2
          have hu2 := Finset.card_le_card hU2
          have hB : B' = insert M B := by
            dsimp [B', B]
            rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left]
            exact ⟨(hW M hM).2, hsplit, by omega⟩
          have hBc : B'.card = B.card + 1 := by
            rw [hB, Finset.card_insert_of_notMem]
            simp [B]
          omega
    · have hW' : ∀ w ∈ W, w < M ∧ safe w := by
        intro w hw
        have := hW w hw
        have hne : w ≠ M := fun he => hM (he ▸ hw)
        exact ⟨by omega, this.2⟩
      have hi := ih W hW'
      change _ ≤ W.card + B.card at hi
      omega

end OneSided

namespace OneSided.SemanticSafe

variable {α : Type*} [DecidableEq α]

def outsideInput (S : Finset α) : α → Bool := fun i => decide (i ∉ S)

def Safe (S : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ i ∈ S, x i = true

def PureOr (S : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x, f x = true ↔ ∃ i ∈ S, x i = true

lemma safe_at_outside {S : Finset α} {f : (α → Bool) → Bool}
    (h : Safe S f) : f (outsideInput S) = false := by
  cases hf : f (outsideInput S)
  · rfl
  · obtain ⟨i, hi, hxi⟩ := h (outsideInput S) hf
    simp [outsideInput, hi] at hxi

lemma le_outside_of_no_member {S : Finset α} {x : α → Bool}
    (h : ¬ ∃ i ∈ S, x i = true) : x ≤ outsideInput S := by
  intro i
  by_cases hi : i ∈ S
  · have hx : x i = false := by
      cases hxi : x i
      · rfl
      · exact False.elim (h ⟨i, hi, hxi⟩)
    simp [outsideInput, hi, hx]
  · simp [outsideInput, hi]

lemma safe_of_outside {S : Finset α} {f : (α → Bool) → Bool}
    (hf : Monotone f) (h : f (outsideInput S) = false) : Safe S f := by
  intro x hx
  by_contra hnone
  have hle := hf (le_outside_of_no_member hnone)
  have hz : f (outsideInput S) = true := Bool.le_iff_imp.mp hle hx
  simp [h] at hz

lemma safe_iff_outside {S : Finset α} {f : (α → Bool) → Bool}
    (hf : Monotone f) : Safe S f ↔ f (outsideInput S) = false :=
  ⟨safe_at_outside, safe_of_outside hf⟩

lemma safe_and {S : Finset α} {f g : (α → Bool) → Bool}
    (hf : Monotone f) (hg : Monotone g)
    (h : Safe S (fun x => f x && g x)) : Safe S f ∨ Safe S g := by
  have hz := safe_at_outside h
  cases hfv : f (outsideInput S)
  · exact Or.inl (safe_of_outside hf hfv)
  · cases hgv : g (outsideInput S)
    · exact Or.inr (safe_of_outside hg hgv)
    · simp [hfv, hgv] at hz

lemma safe_or_iff {S : Finset α} {f g : (α → Bool) → Bool} :
    Safe S (fun x => f x || g x) ↔ Safe S f ∧ Safe S g := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by simp [hx])
    · intro x hx
      exact h x (by simp [hx])
  · rintro ⟨hf, hg⟩ x hx
    cases hfv : f x
    · apply hg x
      simpa [hfv] using hx
    · exact hf x hfv

lemma pureOr_and_redundant {S : Finset α} {f g : (α → Bool) → Bool}
    (hf : Monotone f) (hg : Monotone g)
    (h : PureOr S (fun x => f x && g x)) : PureOr S f ∨ PureOr S g := by
  have hs : Safe S (fun x => f x && g x) := fun x hx => (h x).mp hx
  rcases safe_and hf hg hs with hsf | hsg
  · left
    intro x
    refine ⟨hsf x, ?_⟩
    intro hx
    have hfg := (h x).mpr hx
    cases hfx : f x
    · simp [hfx] at hfg
    · rfl
  · right
    intro x
    refine ⟨hsg x, ?_⟩
    intro hx
    have hfg := (h x).mpr hx
    cases hgx : g x
    · simp [hgx] at hfg
    · rfl

end OneSided.SemanticSafe

namespace OneSided

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.OneSided.SemanticSafe

def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => wireFn n C w (fun k => decide (k = i)) = true

lemma mem_singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ singletonSupport n C w ↔ wireFn n C w (fun k => decide (k = i)) = true := by
  simp [singletonSupport]

lemma singletonSupport_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    singletonSupport n C w = {⟨w, hw⟩} := by
  ext i
  simp [mem_singletonSupport, wireFn_input n C w hw, eq_comm]

lemma singletonSupport_safe_subset (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (hs : Safe Q (wireFn n C w)) : singletonSupport n C w ⊆ Q := by
  intro i hi
  have hv := (mem_singletonSupport n C w i).mp hi
  obtain ⟨k, hk, hki⟩ := hs _ hv
  have : k = i := by simpa using hki
  exact this ▸ hk

lemma singletonSupport_pure (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (hp : PureOr Q (wireFn n C w)) : singletonSupport n C w = Q := by
  ext i
  rw [mem_singletonSupport, hp]
  simp

lemma safe_singleton_structure (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) :
    ∀ w, (w < n + C.gates.length ∧ Safe Q (wireFn n C w)) →
      (singletonSupport n C w).card ≤ 1 ∨
      (∃ a, a < w ∧ (a < n + C.gates.length ∧ Safe Q (wireFn n C a)) ∧
        singletonSupport n C w ⊆ singletonSupport n C a) ∨
      ((n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or) ∧
        ∃ a b, a < w ∧ b < w ∧
          (a < n + C.gates.length ∧ Safe Q (wireFn n C a)) ∧
          (b < n + C.gates.length ∧ Safe Q (wireFn n C b)) ∧
          singletonSupport n C w ⊆ singletonSupport n C a ∪ singletonSupport n C b) := by
  intro w ⟨hw, hs⟩
  by_cases hi : w < n
  · left
    rw [singletonSupport_input n C w hi]
    simp
  · have hn : n ≤ w := Nat.le_of_not_lt hi
    have hj : w - n < C.gates.length := by omega
    have heq : n + (w - n) = w := by omega
    obtain ⟨a, b, ha, hb, hab, hop, he⟩ := binary_gate n C hC (w - n) hj
    rw [heq] at ha hb he
    rcases hop with hand | hor
    · have hv : ∀ x, wireFn n C w x = (wireFn n C a x && wireFn n C b x) := by
        intro x
        rw [he, hand]
        simp [GateOp.eval]
      have hs' : Safe Q (fun x => wireFn n C a x && wireFn n C b x) := by
        simpa only [← hv] using hs
      have hbypass := safe_and (wireFn_mono n C hC a) (wireFn_mono n C hC b) hs'
      right; left
      rcases hbypass with hsa | hsb
      · refine ⟨a, ha, ⟨by omega, hsa⟩, ?_⟩
        intro i hi
        rw [mem_singletonSupport] at hi ⊢
        rw [hv] at hi
        exact (Bool.and_eq_true_iff.mp hi).1
      · refine ⟨b, hb, ⟨by omega, hsb⟩, ?_⟩
        intro i hi
        rw [mem_singletonSupport] at hi ⊢
        rw [hv] at hi
        exact (Bool.and_eq_true_iff.mp hi).2
    · have hv : ∀ x, wireFn n C w x = (wireFn n C a x || wireFn n C b x) := by
        intro x
        rw [he, hor]
        simp [GateOp.eval]
      have hs' : Safe Q (fun x => wireFn n C a x || wireFn n C b x) := by
        simpa only [← hv] using hs
      obtain ⟨hsa, hsb⟩ := safe_or_iff.mp hs'
      right; right
      refine ⟨⟨hn, hor⟩, a, b, ha, hb, ⟨by omega, hsa⟩, ⟨by omega, hsb⟩, ?_⟩
      intro i hi
      rw [mem_singletonSupport, hv, Bool.or_eq_true] at hi
      simp only [Finset.mem_union, mem_singletonSupport]
      exact hi

noncomputable def chargedOr (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter fun k =>
    (k < n + C.gates.length ∧ Safe Q (wireFn n C k)) ∧
    (n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or) ∧
    2 ≤ (singletonSupport n C k).card

lemma pure_disjunction_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w < n + C.gates.length)
    (hp : PureOr Q (wireFn n C w)) :
    Q.card ≤ 1 + (chargedOr n C Q).card := by
  classical
  have hs : Safe Q (wireFn n C w) := fun x hx => (hp x).mp hx
  have hh := safe_leaf_count
    (fun k => k < n + C.gates.length ∧ Safe Q (wireFn n C k))
    (fun k => n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or)
    (singletonSupport n C) (safe_singleton_structure n C hC Q)
    (n + C.gates.length) {w} (by simpa using And.intro hw (And.intro hw hs))
  simpa [chargedOr, singletonSupport_pure n C w Q hp] using hh

lemma frontier_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ Safe Q (wireFn n C w)) :
    (W.biUnion (singletonSupport n C)).card ≤ W.card + (chargedOr n C Q).card := by
  classical
  apply safe_leaf_count
    (fun k => k < n + C.gates.length ∧ Safe Q (wireFn n C k))
    (fun k => n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or)
    (singletonSupport n C) (safe_singleton_structure n C hC Q)
  intro w hw
  exact ⟨(hW w hw).1, hW w hw⟩

lemma chargedOr_disjoint (n : ℕ) (C : Circuit) (Q R : Finset (Fin n))
    (hQR : (Q ∩ R).card ≤ 1) : Disjoint (chargedOr n C Q) (chargedOr n C R) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hk hr
  simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hk hr
  have hsub : singletonSupport n C k ⊆ Q ∩ R :=
    Finset.subset_inter
      (singletonSupport_safe_subset n C k Q hk.2.1.2)
      (singletonSupport_safe_subset n C k R hr.2.1.2)
  have hsmall := (Finset.card_le_card hsub).trans hQR
  have hlarge := hk.2.2.2
  omega

noncomputable def allOrWires (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.gates.length)).filter fun k =>
    (gateAt C (k - n)).op = GateOp.or

lemma allOrWires_card_le (n : ℕ) (C : Circuit) : (allOrWires n C).card ≤ C.size := by
  classical
  have hc := Finset.card_filter_le (s := Finset.Ico n (n + C.gates.length))
    (p := fun k => (gateAt C (k - n)).op = GateOp.or)
  simpa [allOrWires, Circuit.size] using hc

lemma frontier_family_or_count_strong {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hQ : ∀ i ∈ I, Q i = (W i).biUnion (singletonSupport n C))
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤ (∑ i ∈ I, (W i).card) + (allOrWires n C).card := by
  classical
  have hlocal : ∑ i ∈ I, (Q i).card ≤
      ∑ i ∈ I, ((W i).card + (chargedOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    conv_lhs => rw [hQ i hi]
    exact frontier_or_count n C hC (Q i) (W i) (hW i hi)
  have hd : (I : Set ι).PairwiseDisjoint (fun i => chargedOr n C (Q i)) := by
    intro i hi j hj hij
    exact chargedOr_disjoint n C (Q i) (Q j) (hinter i hi j hj hij)
  have hsub : I.biUnion (fun i => chargedOr n C (Q i)) ⊆
      allOrWires n C := by
    intro k hk
    obtain ⟨i, hi, hk⟩ := Finset.mem_biUnion.mp hk
    simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hk.2.2.1.1, hk.1⟩, hk.2.2.1.2⟩
  have hsum : (∑ i ∈ I, (chargedOr n C (Q i)).card) ≤ (allOrWires n C).card := by
    rw [← Finset.card_biUnion hd]
    exact Finset.card_le_card hsub
  rw [Finset.sum_add_distrib] at hlocal
  omega

lemma frontier_family_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hQ : ∀ i ∈ I, Q i = (W i).biUnion (singletonSupport n C))
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤ (∑ i ∈ I, (W i).card) + C.size := by
  classical
  have hlocal : ∑ i ∈ I, (Q i).card ≤
      ∑ i ∈ I, ((W i).card + (chargedOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    conv_lhs => rw [hQ i hi]
    exact frontier_or_count n C hC (Q i) (W i) (hW i hi)
  have hd : (I : Set ι).PairwiseDisjoint (fun i => chargedOr n C (Q i)) := by
    intro i hi j hj hij
    exact chargedOr_disjoint n C (Q i) (Q j) (hinter i hi j hj hij)
  have hsub : I.biUnion (fun i => chargedOr n C (Q i)) ⊆
      Finset.Ico n (n + C.gates.length) := by
    intro k hk
    obtain ⟨i, hi, hk⟩ := Finset.mem_biUnion.mp hk
    simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_Ico.mpr ⟨hk.2.2.1.1, hk.1⟩
  have hsum : (∑ i ∈ I, (chargedOr n C (Q i)).card) ≤ C.size := by
    rw [← Finset.card_biUnion hd]
    have hc := Finset.card_le_card hsub
    simpa [Circuit.size] using hc
  rw [Finset.sum_add_distrib] at hlocal
  omega

lemma common_neighbours_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (a a' : Fin p) (haa : a ≠ a') (Q Q' : Finset (Fin l))
    (hQ : ∀ b ∈ Q, (a, b) ∈ E) (hQ' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  by_contra hbb
  exact hno a a' b b' haa hbb
    ⟨hQ b (Finset.mem_inter.mp hb).1, hQ b' (Finset.mem_inter.mp hb').1,
      hQ' b (Finset.mem_inter.mp hb).2, hQ' b' (Finset.mem_inter.mp hb').2⟩

lemma family_plus_residual_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n))
    (hwitness : ∀ i ∈ I, ∃ w < n + C.gates.length, PureOr (Q i) (wireFn n C w))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1)
    (R : Finset ℕ) (hR : R ⊆ allOrWires n C)
    (hdis : ∀ i ∈ I, Disjoint (chargedOr n C (Q i)) R)
    (hcount : I.card ≤ R.card + 1) :
    (∑ i ∈ I, (Q i).card) ≤ (allOrWires n C).card + 1 := by
  classical
  have hlocal : (∑ i ∈ I, (Q i).card) ≤
      ∑ i ∈ I, (1 + (chargedOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨w,hw,hpure⟩ := hwitness i hi
    exact pure_disjunction_or_count n C hC (Q i) w hw hpure
  have hd : (I : Set ι).PairwiseDisjoint (fun i => chargedOr n C (Q i)) := by
    intro i hi j hj hij
    exact chargedOr_disjoint n C (Q i) (Q j) (hinter i hi j hj hij)
  have hsub : I.biUnion (fun i => chargedOr n C (Q i)) ⊆ allOrWires n C := by
    intro k hk
    obtain ⟨i,hi,hk⟩ := Finset.mem_biUnion.mp hk
    simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hk.2.2.1.1,hk.1⟩,hk.2.2.1.2⟩
  have hdR : Disjoint (I.biUnion (fun i => chargedOr n C (Q i))) R := by
    apply Finset.disjoint_left.mpr
    intro k hk hr
    obtain ⟨i,hi,hk⟩ := Finset.mem_biUnion.mp hk
    exact Finset.disjoint_left.mp (hdis i hi) hk hr
  have hc : (I.biUnion (fun i => chargedOr n C (Q i))).card + R.card ≤
      (allOrWires n C).card := by
    rw [← Finset.card_union_of_disjoint hdR]
    exact Finset.card_le_card (Finset.union_subset hsub hR)
  rw [Finset.card_biUnion hd] at hc
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hlocal
  omega

lemma chargedOr_true (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (x : Fin n → Bool)
    (hQ : ∀ q ∈ Q, x q = true) (w : ℕ) (hw : w ∈ chargedOr n C Q) :
    wireFn n C w x = true := by
  classical
  have hmem := hw
  simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hmem
  have hne : (singletonSupport n C w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,hq⟩ := hne
  have hqQ := singletonSupport_safe_subset n C w Q hmem.2.1.2 hq
  have hle : (fun j : Fin n => decide (j = q)) ≤ x := by
    intro j
    by_cases hj : j = q
    · subst j
      simp [hQ q hqQ]
    · simp [hj]
  exact Bool.le_iff_imp.mp (wireFn_mono n C hC w hle)
    ((mem_singletonSupport n C w q).mp hq)

lemma family_plus_false_residual_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n))
    (hwitness : ∀ i ∈ I, ∃ w < n + C.gates.length, PureOr (Q i) (wireFn n C w))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1)
    (x : Fin n → Bool) (hQ : ∀ i ∈ I, ∀ q ∈ Q i, x q = true)
    (R : Finset ℕ) (hR : R ⊆ allOrWires n C)
    (hfalse : ∀ w ∈ R, wireFn n C w x = false)
    (hcount : I.card ≤ R.card + 1) :
    (∑ i ∈ I, (Q i).card) ≤ (allOrWires n C).card + 1 := by
  apply family_plus_residual_or_count n C hC I Q hwitness hinter R hR _ hcount
  intro i hi
  apply Finset.disjoint_left.mpr
  intro w hw hr
  have ht := chargedOr_true n C hC (Q i) x (hQ i hi) w hw
  rw [hfalse w hr] at ht
  cases ht

def activeLeft {p l : ℕ} (E : Finset (Fin p × Fin l)) : Finset (Fin p) :=
  E.image Prod.fst

def leftNeighbors {p l : ℕ} (E : Finset (Fin p × Fin l)) (a : Fin p) :
    Finset (Fin (p+l)) :=
  (E.filter fun e => e.1 = a).image fun e => Fin.natAdd p e.2

lemma mem_activeLeft {p l : ℕ} (E : Finset (Fin p × Fin l)) (a : Fin p) :
    a ∈ activeLeft E ↔ ∃ b, (a,b) ∈ E := by
  constructor
  · intro ha
    obtain ⟨⟨a',b⟩,he,haa⟩ := Finset.mem_image.mp ha
    subst a
    exact ⟨b,he⟩
  · rintro ⟨b,hb⟩
    exact Finset.mem_image_of_mem Prod.fst hb

lemma mem_leftNeighbors {p l : ℕ} (E : Finset (Fin p × Fin l)) (a : Fin p)
    (q : Fin (p+l)) : q ∈ leftNeighbors E a ↔ ∃ b, (a,b) ∈ E ∧ Fin.natAdd p b = q := by
  constructor
  · intro hq
    obtain ⟨⟨a',b⟩,he,hb⟩ := Finset.mem_image.mp hq
    obtain ⟨he,ha⟩ := Finset.mem_filter.mp he
    dsimp at ha
    subst a'
    exact ⟨b,he,hb⟩
  · rintro ⟨b,he,rfl⟩
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_filter.mpr ⟨he,rfl⟩,rfl⟩

lemma leftNeighbors_card {p l : ℕ} (E : Finset (Fin p × Fin l)) (a : Fin p) :
    (leftNeighbors E a).card = (E.filter fun e => e.1 = a).card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf hef
  apply Prod.ext
  · exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
  · apply Fin.ext
    have h := congrArg Fin.val hef
    simp only [Fin.val_natAdd] at h
    omega

lemma sum_leftNeighbors_card {p l : ℕ} (E : Finset (Fin p × Fin l)) :
    (∑ a ∈ activeLeft E, (leftNeighbors E a).card) = E.card := by
  simp only [leftNeighbors_card]
  exact (Finset.card_eq_sum_card_image Prod.fst E).symm

lemma leftNeighbors_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (a a' : Fin p) (haa : a ≠ a') :
    (leftNeighbors E a ∩ leftNeighbors E a').card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq r hr
  obtain ⟨b,hab,hbq⟩ := (mem_leftNeighbors E a q).mp (Finset.mem_inter.mp hq).1
  obtain ⟨b',hab',hb'r⟩ := (mem_leftNeighbors E a r).mp (Finset.mem_inter.mp hr).1
  obtain ⟨c,hac,hcq⟩ := (mem_leftNeighbors E a' q).mp (Finset.mem_inter.mp hq).2
  obtain ⟨c',hac',hc'r⟩ := (mem_leftNeighbors E a' r).mp (Finset.mem_inter.mp hr).2
  have hc : c = b := by
    apply Fin.ext
    have h := congrArg Fin.val (hcq.trans hbq.symm)
    simp only [Fin.val_natAdd] at h
    omega
  have hc' : c' = b' := by
    apply Fin.ext
    have h := congrArg Fin.val (hc'r.trans hb'r.symm)
    simp only [Fin.val_natAdd] at h
    omega
  subst c
  subst c'
  have hbb : b = b' := by
    by_contra hne
    exact hno a a' b b' haa hne ⟨hab,hab',hac,hac'⟩
  exact hbq.symm.trans (hbb ▸ hb'r)

lemma wireFn_out_of_range (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : n + C.gates.length ≤ w) (x : Fin n → Bool) : wireFn n C w x = false := by
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = false
  apply List.getD_eq_default
  simpa only [length_wiresFrom, List.length_ofFn] using hw

lemma full_left_neighborhood_or_count {p l : ℕ}
    (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hC : IsAO2 (p+l) C)
    (hF : ∀ x : Fin (p+l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p+l) C x =
        decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
          x (Fin.natAdd p b) = true))
    (hfull : ∀ a : Fin p, (∃ b, (a,b) ∈ E) →
      ∃ w < p+l+C.gates.length, ∀ x : Fin (p+l) → Bool,
        (C.wires (List.ofFn x)).getD w false =
          decide (∃ b, (a,b) ∈ E ∧ x (Fin.natAdd p b) = true)) :
    E.card ≤ (allOrWires (p+l) C).card + 1 := by
  classical
  by_cases hE : E.Nonempty
  · have hout : C.output < p+l+C.gates.length := by
      by_contra hn
      obtain ⟨⟨a,b⟩,he⟩ := hE
      have htrue : wireFn (p+l) C C.output (fun _ => true) = true := by
        change PEqualNP.MetaComplexity.circuitFun (p+l) C (fun _ => true) = true
        rw [hF,decide_eq_true_eq]
        exact ⟨a,b,he,rfl,rfl⟩
      rw [wireFn_out_of_range (p+l) C C.output (by omega)] at htrue
      cases htrue
    have hcofactor : ∀ x : Fin p → Bool,
        (C.wires (List.ofFn (Kernel.rightTrueInput (l := l) x))).getD C.output false =
          decide (∃ a ∈ activeLeft E, x a = true) := by
      intro x
      change PEqualNP.MetaComplexity.circuitFun (p+l) C (Kernel.rightTrueInput x) = _
      rw [hF]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      simp only [Kernel.rightTrueInput, Fin.addCases_left, Fin.addCases_right, and_true]
      constructor
      · rintro ⟨a,b,he,hx⟩
        exact ⟨a,(mem_activeLeft E a).mpr ⟨b,he⟩,hx⟩
      · rintro ⟨a,ha,hx⟩
        obtain ⟨b,he⟩ := (mem_activeLeft E a).mp ha
        exact ⟨a,b,he,hx⟩
    have hcount := Kernel.rightTrue_or_budget C hC (activeLeft E) C.output hout hcofactor
    let R := Kernel.restrictedSafeOrWires C (Kernel.rightTrueInput (l := l)) (activeLeft E)
    have hR : R ⊆ allOrWires (p+l) C := by
      intro w hw
      obtain ⟨j,hj,rfl,hop,hfalse,hcard⟩ :=
        (Kernel.restrictedSafeOrWires_mem C (Kernel.rightTrueInput (l := l)) (activeLeft E) w).mp hw
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,by simpa using hop⟩
    have hfalse : ∀ w ∈ R, wireFn (p+l) C w
        (Kernel.rightTrueInput (l := l) (Kernel.complementInput (activeLeft E))) = false := by
      intro w hw
      obtain ⟨j,hj,heq,hop,hfalse,hcard⟩ :=
        (Kernel.restrictedSafeOrWires_mem C (Kernel.rightTrueInput (l := l)) (activeLeft E) w).mp hw
      exact hfalse
    have hbound := family_plus_false_residual_or_count (p+l) C hC
      (activeLeft E) (leftNeighbors E) ?_ ?_
      (Kernel.rightTrueInput (l := l) (Kernel.complementInput (activeLeft E))) ?_
      R hR hfalse (by simpa [R,Nat.add_comm] using hcount)
    · simpa [sum_leftNeighbors_card] using hbound
    · intro a ha
      obtain ⟨w,hw,hsem⟩ := hfull a ((mem_activeLeft E a).mp ha)
      refine ⟨w,hw,?_⟩
      intro x
      rw [show wireFn (p+l) C w x = _ from hsem x,decide_eq_true_eq]
      constructor
      · rintro ⟨b,he,hx⟩
        exact ⟨Fin.natAdd p b,(mem_leftNeighbors E a _).mpr ⟨b,he,rfl⟩,hx⟩
      · rintro ⟨q,hq,hx⟩
        obtain ⟨b,he,rfl⟩ := (mem_leftNeighbors E a q).mp hq
        exact ⟨b,he,hx⟩
    · intro a ha a' ha' haa
      exact leftNeighbors_inter_card_le_one E hno a a' haa
    · intro a ha q hq
      obtain ⟨b,he,rfl⟩ := (mem_leftNeighbors E a q).mp hq
      simp [Kernel.rightTrueInput]
  · have : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    simp [this]

end OneSided

end PEqualNP.Outside.L_meta_4970
