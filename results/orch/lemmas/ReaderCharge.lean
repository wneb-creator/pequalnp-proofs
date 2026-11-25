import ReaderDeletion

namespace PEqualNP.Outside.L_meta_2592.ReaderCharge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ReaderDeletion Sum List

def reads (ks : List Nat) (g : Gate) : Bool :=
  let xs := match g.op with | .not => g.inputs.take 1 | _ => g.inputs
  xs.any fun i => ks.contains i

def Known (ks : List Nat) (e : List S) : Prop :=
  ∀ i ∈ ks, i < e.length ∧ ∃ b : Bool, e.getD i F = inl b

lemma known_append (ks : List Nat) (e : List S) (v : S) (h : Known ks e) :
    Known ks (e ++ [v]) := by
  intro i hi
  obtain ⟨hl,b,hb⟩ := h i hi
  refine ⟨by simp;omega,b,?_⟩
  rw [gl _ _ _ _ hl]
  exact hb

abbrev IvK (ks : List Nat) (e : List S) (d : List Gate)
    (wC : I9 → List Bool) (g : Gate) (s : List S × List Gate) : Prop :=
  s.1.length = e.length+1 ∧ Known ks s.1 ∧
  s.2.length + (if reads ks g then 1 else 0) ≤ d.length+1 ∧
  (∀ g' ∈ s.2,ok g') ∧ (∀ i,sb s.2.length (s.1.getD i F)) ∧
  (∀ y i,es (wf s.2 y) (s.1.getD i F) = (ws (wC y) g).getD i false)

lemma compile_known (ks : List Nat) (gs : List Gate) (e : List S) (d : List Gate) (wC : I9 -> List Bool)
 (hfg : ∀ g ∈ gs,ok g) (hd : ∀ g ∈ d,ok g) (hknown : Known ks e)
 (hwl : ∀ y,(wC y).length = e.length) (hbd : ∀ i,sb d.length (e.getD i F))
 (heq : ∀ y i,es (wf d y) (e.getD i F) = (wC y).getD i false) :
 let r := gs.foldl cs (e,d)
 r.2.length+gs.countP (reads ks) <= d.length+gs.length/\(∀ g ∈ r.2,ok g)/\(∀ y i,es (wf r.2 y) (r.1.getD i F) = (gs.foldl ws (wC y)).getD i false)/\Known ks r.1/\(∀ i,sb r.2.length (r.1.getD i F))/\r.1.length=e.length+gs.length := by
 induction gs generalizing e d wC with
 | nil=>exact ⟨by simp,hd,heq,hknown,hbd,by simp⟩
 | cons g rest ih=>
  have hgf := hfg g mem_cons_self
  have hno : ∀ v : S,cs (e,d) g = (e++[v],d) -> sb d.length v ->
    (∀ y,es (wf d y) v = g.op.eval (g.inputs.map fun i=>(wC y).getD i false)) -> IvK ks e d wC g (cs (e,d) g) := by
   intro v hst hv hve; rw [hst]
   refine ⟨by simp,known_append ks e _ hknown,by cases reads ks g <;> simp,hd,?_,?_⟩
   · intro i; rcases lt_trichotomy i e.length with hi|rfl|hi
     · rw [gl _ _ _ _ hi]; exact hbd i
     · rw [ge]; exact hv
     · rw [gg _ _ _ _ hi]; trivial
   · intro y i; rcases lt_trichotomy i e.length with hi|rfl|hi
     · rw [gl _ _ _ _ hi,ws,gl _ _ _ _ (by rw [hwl y]; exact hi)]; exact heq y i
     · rw [ge,ws,← hwl y,ge]; exact hve y
     · rw [gg _ _ _ _ hi,ws,gg _ _ _ _ (by rw [hwl y]; exact hi)]; rfl
  have hem : ∀ ng : Gate,cs (e,d) g = (e++[inr (9+d.length)],d++[ng]) -> ok ng -> reads ks g = false ->
    (∀ y,ng.op.eval (ng.inputs.map fun i=>(wf d y).getD i false) = g.op.eval (g.inputs.map fun i=>(wC y).getD i false)) ->
    IvK ks e d wC g (cs (e,d) g) := by
   intro ng hst hng hnr hne; rw [hst]
   refine ⟨by simp,known_append ks e _ hknown,by simp [hnr],?_,?_,?_⟩
   · intro g' hg'; rcases mem_append.mp hg' with hg'|hg'
     · exact hd g' hg'
     · simp only [mem_singleton] at hg'; exact hg'▸hng
   · intro i; rcases lt_trichotomy i e.length with hi|rfl|hi
     · rw [gl _ _ _ _ hi]; have hbi := hbd i; cases hvi : e.getD i F with
       | inl _=>trivial | inr k=>rw [hvi] at hbi; simp only [sb,length_append,length_singleton] at hbi ⊢; omega
     · rw [ge]; simp [sb]
     · rw [gg _ _ _ _ hi]; trivial
   · intro y i
     have hfl : wf (d++[ng]) y = ws (wf d y) ng := by simp only [wf,foldl_append]; rfl
     have hdl : (wf d y).length = 9+d.length := by rw [wf,wl]; simp
     rcases lt_trichotomy i e.length with hi|rfl|hi
     · rw [gl _ _ _ _ hi,ws,gl _ _ _ _ (by rw [hwl y]; exact hi),← heq y i,hfl]
       have hbi := hbd i; cases hvi : e.getD i F with
       | inl _=>rfl | inr k=>rw [hvi] at hbi; exact gl _ _ _ _ (by rw [hdl]; exact hbi)
     · rw [ge,ws,← hwl y,ge,hfl,es,ws,← hdl,ge]; exact hne y
     · rw [gg _ _ _ _ hi,ws,gg _ _ _ _ (by rw [hwl y]; exact hi)]; rfl
  have hne : ∀ a k,e.getD a F = inr k -> a ∉ ks := by
   intro a k ha hm
   obtain ⟨_,b,hb⟩ := hknown a hm
   rw [hb] at ha
   cases ha
  have hst : IvK ks e d wC g (cs (e,d) g) := by
   rcases g with ⟨op,ins⟩
   have hg : op = .and\/op = .or\/op = .not := by simpa [ok,Set.mem_insert_iff,Set.mem_singleton_iff] using hgf.1
   have hl : ins.length <= 2 := hgf.2
   rcases hg with rfl|rfl|rfl
   · match ins,hl with
     | [],_=>exact hno (inl true) rfl trivial (fun _=>rfl)
     | [a],_=>exact hno (e.getD a F) rfl (hbd a) (fun y=>by rw [eA1]; exact heq y a)
     | [a,b],_=>cases ha : e.getD a F with
       | inl ba=>cases ba with
         | false=>exact hno F (by dsimp only [cs]; rw [ha]) trivial (fun y=>by rw [eA2,← heq y a,ha]; rfl)
         | true=>exact hno (e.getD b F) (by dsimp only [cs]; rw [ha]) (hbd b) (fun y=>by rw [eA2,← heq y a,ha,es,Bool.true_and]; exact heq y b)
       | inr ka=>cases hb : e.getD b F with
         | inl bb=>cases bb with
           | false=>exact hno F (by dsimp only [cs]; rw [ha,hb]) trivial (fun y=>by rw [eA2,← heq y b,hb,es,Bool.and_false])
           | true=>exact hno (inr ka) (by dsimp only [cs]; rw [ha,hb]) (by rw [← ha]; exact hbd a) (fun y=>by rw [eA2,← heq y a,← heq y b,ha,hb,es,Bool.and_true])
         | inr kb=>
           have a0 := hne a ka ha; have b0 := hne b kb hb
           exact hem ⟨.and,[ka,kb]⟩ (by dsimp only [cs]; rw [ha,hb]) ⟨by simp,by simp⟩
             (by simp [reads,a0,b0]) (fun y=>by rw [eA2,eA2,← heq y a,← heq y b,ha,hb]; rfl)
   · match ins,hl with
     | [],_=>exact hno F rfl trivial (fun _=>rfl)
     | [a],_=>exact hno (e.getD a F) rfl (hbd a) (fun y=>by rw [eO1]; exact heq y a)
     | [a,b],_=>cases ha : e.getD a F with
       | inl ba=>cases ba with
         | true=>exact hno (inl true) (by dsimp only [cs]; rw [ha]) trivial (fun y=>by rw [eO2,← heq y a,ha]; rfl)
         | false=>exact hno (e.getD b F) (by dsimp only [cs]; rw [ha]) (hbd b) (fun y=>by rw [eO2,← heq y a,ha,es,Bool.false_or]; exact heq y b)
       | inr ka=>cases hb : e.getD b F with
         | inl bb=>cases bb with
           | true=>exact hno (inl true) (by dsimp only [cs]; rw [ha,hb]) trivial (fun y=>by rw [eO2,← heq y b,hb,es,Bool.or_true])
           | false=>exact hno (inr ka) (by dsimp only [cs]; rw [ha,hb]) (by rw [← ha]; exact hbd a) (fun y=>by rw [eO2,← heq y a,← heq y b,ha,hb,es,Bool.or_false])
         | inr kb=>
           have a0 := hne a ka ha; have b0 := hne b kb hb
           exact hem ⟨.or,[ka,kb]⟩ (by dsimp only [cs]; rw [ha,hb]) ⟨by simp,by simp⟩
             (by simp [reads,a0,b0]) (fun y=>by rw [eO2,eO2,← heq y a,← heq y b,ha,hb]; rfl)
   · cases ins with
     | nil=>exact hno (inl true) rfl trivial (fun _=>rfl)
     | cons a tl=>cases ha : e.getD a F with
       | inl ba=>exact hno (inl (!ba)) (by dsimp only [cs]; rw [ha]) trivial (fun y=>by rw [eN,← heq y a,ha]; rfl)
       | inr ka=>
         have a0 := hne a ka ha
         exact hem ⟨.not,[ka]⟩ (by dsimp only [cs]; rw [ha]) ⟨by simp,by simp⟩
           (by simp [reads,a0]) (fun y=>by rw [eN,eN,← heq y a,ha]; rfl)
  rcases hst with ⟨hsl,hsk,hss,hsf,hsb,hsq⟩
  obtain ⟨hsz',hfn',heq',hknown',hbound',hlen'⟩ := ih (cs (e,d) g).1 (cs (e,d) g).2 (fun y=>ws (wC y) g)
    (fun g' hg'=>hfg g' (mem_cons_of_mem _ hg')) hsf hsk (fun y=>by simp [ws,hwl y,hsl]) hsb hsq
  refine ⟨?_,hfn',heq',hknown',hbound',?_⟩
  ·
   simp only [foldl_cons,countP_cons,length_cons,Prod.mk.eta] at hsz' ⊢
   cases hr : reads ks g <;> simp [hr] at hss ⊢ <;> omega
  · simpa only [foldl_cons,length_cons,Prod.mk.eta] using hlen'.trans (by omega)

end PEqualNP.Outside.L_meta_2592.ReaderCharge
