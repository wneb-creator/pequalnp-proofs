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

end PEqualNP.Outside.L_meta_4970
