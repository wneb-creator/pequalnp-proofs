import PEqualNP.Defs

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
