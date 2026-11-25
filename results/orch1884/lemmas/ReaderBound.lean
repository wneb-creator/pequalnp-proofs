import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.ReaderBound
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Sum List
abbrev ok (g : Gate) : Prop := g.op ∈ ({.and,.or} : Set GateOp) /\ g.inputs.length <= 2
abbrev S := Bool ⊕ Nat
abbrev F : S := inl false
abbrev I9 := Fin 9 -> Bool
def p10 (x : Fin 10 -> Bool) : Bool :=
 x 0&&x 1||x 1&&x 2||x 2&&x 3||x 3&&x 4||x 4&&x 0||x 0&&x 5||x 1&&x 6||x 2&&x 7||x 3&&x 8||x 4&&x 9||x 5&&x 7||x 7&&x 9||x 9&&x 6||x 6&&x 8||x 8&&x 5
def p9 (x : I9) : Bool := [(1 : Nat),12,23,34,40,5,16,27,38,57,68,85].any fun n=>x (Fin.ofNat 9 (n / 10))&&x (Fin.ofNat 9 (n % 10))
def lft (y : I9) (i : Fin 10) : Bool := ([false,y 4,y 0,y 1,y 6,y 7,y 3,y 5,y 2,y 8] : List Bool).getD i.val false
lemma iso (y : I9) : p10 (lft y) = p9 y := by
 have h : ∀ a b c d e f g h k : Bool,
  (false&&e||e&&a||a&&b||b&&g||g&&false||false&&h||e&&d||a&&f||b&&c||g&&k||h&&f||f&&k||k&&d||d&&c||c&&h)=
  (a&&b||(b&&c||(c&&d||(d&&e||(e&&a||(a&&f||(b&&g||(c&&h||(d&&k||(f&&h||(g&&k||(k&&f||false)))))))))))) := by
  intro a b c d e f g h k; simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
  rw [Bool.and_comm e d,Bool.and_comm h f,Bool.and_comm f k,Bool.and_comm k d,Bool.and_comm d c]; ac_rfl
 exact h (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
def r0 (g : Gate) : Bool :=
 let xs : List Nat := match g.op with | .not => take 1 g.inputs | _ => g.inputs
 xs.contains 0 || xs.contains 10
lemma r0_eq (g : Gate) :
 r0 g = (have x5 : List Nat := GateOp.rec g.inputs g.inputs (take 1 g.inputs) (fun _=>g.inputs) g.inputs g.op; x5.contains 0||x5.contains 10) := by
 rcases g with ⟨op,ins⟩; cases op <;> rfl
def ws (w : List Bool) (g : Gate) : List Bool := w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
def wf (d : List Gate) (y : I9) : List Bool := d.foldl ws (ofFn y)
def es (w : List Bool) : S -> Bool | inl b=>b | inr k=>w.getD k false
def sb (m : Nat) : S -> Prop | inl _=>True | inr k=>k < 9+m
def cs : (List S × List Gate) -> Gate -> List S × List Gate
 | (e,d),⟨.not,[]⟩=>(e++[inl true],d)
 | (e,d),⟨.not,a::_⟩=>match e.getD a F with | inl b=>(e++[inl (!b)],d) | inr k=>(e++[inr (9+d.length)],d++[⟨.not,[k]⟩])
 | (e,d),⟨.and,[]⟩=>(e++[inl true],d)
 | (e,d),⟨.and,[a]⟩=>(e++[e.getD a F],d)
 | (e,d),⟨.and,[a,b]⟩=>match e.getD a F,e.getD b F with
   | inl false,_=>(e++[F],d) | inl true,eb=>(e++[eb],d) | _,inl false=>(e++[F],d)
   | ea,inl true=>(e++[ea],d) | inr ka,inr kb=>(e++[inr (9+d.length)],d++[⟨.and,[ka,kb]⟩])
 | (e,d),⟨.or,[]⟩=>(e++[F],d)
 | (e,d),⟨.or,[a]⟩=>(e++[e.getD a F],d)
 | (e,d),⟨.or,[a,b]⟩=>match e.getD a F,e.getD b F with
   | inl true,_=>(e++[inl true],d) | inl false,eb=>(e++[eb],d) | _,inl true=>(e++[inl true],d)
   | ea,inl false=>(e++[ea],d) | inr ka,inr kb=>(e++[inr (9+d.length)],d++[⟨.or,[ka,kb]⟩])
 | (e,d),_=>(e++[F],d)
lemma wl (gs : List Gate) (w : List Bool) : (gs.foldl ws w).length = w.length+gs.length := by
 induction gs generalizing w with | nil=>simp | cons g r ih=>rw [foldl_cons,ih]; simp [ws]; omega
lemma gl {α : Type} (l1 l2 : List α) (d : α) (i : Nat) (h : i < l1.length) : (l1++l2).getD i d = l1.getD i d := by
 simp [getD_eq_getElem?_getD,getElem?_append_left h]
lemma ge {α : Type} (l : List α) (v d : α) : (l++[v]).getD l.length d = v := by simp [getD_eq_getElem?_getD]
lemma gg {α : Type} (l : List α) (v d : α) (i : Nat) (h : l.length < i) : (l++[v]).getD i d = d := by rw [getD_eq_default]; simp; omega
lemma eA1 (f : Nat -> Bool) (a : Nat) : GateOp.and.eval ([a].map f) = f a := by simp [GateOp.eval]
lemma eO1 (f : Nat -> Bool) (a : Nat) : GateOp.or.eval ([a].map f) = f a := by simp [GateOp.eval]
lemma eA2 (f : Nat -> Bool) (a b : Nat) : GateOp.and.eval ([a,b].map f) = (f a&&f b) := by simp [GateOp.eval]
lemma eO2 (f : Nat -> Bool) (a b : Nat) : GateOp.or.eval ([a,b].map f) = (f a||f b) := by simp [GateOp.eval]
lemma eN (f : Nat -> Bool) (a : Nat) (t : List Nat) : GateOp.not.eval ((a::t).map f) = !(f a) := rfl
abbrev Iv (e : List S) (d : List Gate) (wC : I9 -> List Bool) (g : Gate) (s : List S × List Gate) : Prop :=
 s.1.length = e.length+1/\s.1.getD 0 F = F/\s.1.getD 10 F = inl true/\s.2.length+(if r0 g then 1 else 0) <= d.length+1/\
 (∀ g' ∈ s.2,ok g')/\(∀ i,sb s.2.length (s.1.getD i F))/\(∀ y i,es (wf s.2 y) (s.1.getD i F) = (ws (wC y) g).getD i false)
lemma cind (gs : List Gate) (e : List S) (d : List Gate) (wC : I9 -> List Bool)
 (hfg : ∀ g ∈ gs,ok g) (hd : ∀ g ∈ d,ok g) (h11 : 11 <= e.length) (h0 : e.getD 0 F = F) (h10 : e.getD 10 F = inl true)
 (hwl : ∀ y,(wC y).length = e.length) (hbd : ∀ i,sb d.length (e.getD i F))
 (heq : ∀ y i,es (wf d y) (e.getD i F) = (wC y).getD i false) :
 let r := gs.foldl cs (e,d)
 r.2.length+gs.countP r0 <= d.length+gs.length/\(∀ g ∈ r.2,ok g)/\(∀ y i,es (wf r.2 y) (r.1.getD i F) = (gs.foldl ws (wC y)).getD i false) := by
 induction gs generalizing e d wC with
 | nil=>exact ⟨by simp,hd,heq⟩
 | cons g rest ih=>
  have hgf := hfg g mem_cons_self
  have hno : ∀ v : S,cs (e,d) g = (e++[v],d) -> sb d.length v ->
    (∀ y,es (wf d y) v = g.op.eval (g.inputs.map fun i=>(wC y).getD i false)) -> Iv e d wC g (cs (e,d) g) := by
   intro v hst hv hve; rw [hst]
   refine ⟨by simp,(gl _ _ _ _ (by omega)).trans h0,(gl _ _ _ _ (by omega)).trans h10,by cases r0 g <;> simp,hd,?_,?_⟩
   · intro i; rcases lt_trichotomy i e.length with hi|rfl|hi
     · rw [gl _ _ _ _ hi]; exact hbd i
     · rw [ge]; exact hv
     · rw [gg _ _ _ _ hi]; trivial
   · intro y i; rcases lt_trichotomy i e.length with hi|rfl|hi
     · rw [gl _ _ _ _ hi,ws,gl _ _ _ _ (by rw [hwl y]; exact hi)]; exact heq y i
     · rw [ge,ws,← hwl y,ge]; exact hve y
     · rw [gg _ _ _ _ hi,ws,gg _ _ _ _ (by rw [hwl y]; exact hi)]; rfl
  have hem : ∀ ng : Gate,cs (e,d) g = (e++[inr (9+d.length)],d++[ng]) -> ok ng -> r0 g = false ->
    (∀ y,ng.op.eval (ng.inputs.map fun i=>(wf d y).getD i false) = g.op.eval (g.inputs.map fun i=>(wC y).getD i false)) ->
    Iv e d wC g (cs (e,d) g) := by
   intro ng hst hng hnr hne; rw [hst]
   refine ⟨by simp,(gl _ _ _ _ (by omega)).trans h0,(gl _ _ _ _ (by omega)).trans h10,by simp [hnr],?_,?_,?_⟩
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
  have hne : ∀ a k,e.getD a F = inr k -> a ≠ 0/\a ≠ 10 := by
   intro a k ha; refine ⟨?_,?_⟩
   · intro h; subst h; rw [h0] at ha; cases ha
   · intro h; subst h; rw [h10] at ha; cases ha
  have hst : Iv e d wC g (cs (e,d) g) := by
   rcases g with ⟨op,ins⟩
   have hg : op = .and\/op = .or := by simpa [ok,Set.mem_insert_iff,Set.mem_singleton_iff] using hgf.1
   have hl : ins.length <= 2 := hgf.2
   rcases hg with rfl|rfl
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
           obtain ⟨a0,a1⟩ := hne a ka ha; obtain ⟨b0,b1⟩ := hne b kb hb
           exact hem ⟨.and,[ka,kb]⟩ (by dsimp only [cs]; rw [ha,hb]) ⟨by simp,by simp⟩
             (by simp [r0]; exact ⟨⟨a0.symm,b0.symm⟩,a1.symm,b1.symm⟩) (fun y=>by rw [eA2,eA2,← heq y a,← heq y b,ha,hb]; rfl)
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
           obtain ⟨a0,a1⟩ := hne a ka ha; obtain ⟨b0,b1⟩ := hne b kb hb
           exact hem ⟨.or,[ka,kb]⟩ (by dsimp only [cs]; rw [ha,hb]) ⟨by simp,by simp⟩
             (by simp [r0]; exact ⟨⟨a0.symm,b0.symm⟩,a1.symm,b1.symm⟩) (fun y=>by rw [eO2,eO2,← heq y a,← heq y b,ha,hb]; rfl)
  rcases hst with ⟨hsl,hs0,hs10,hss,hsf,hsb,hsq⟩
  obtain ⟨hsz',hfn',heq'⟩ := ih (cs (e,d) g).1 (cs (e,d) g).2 (fun y=>ws (wC y) g)
    (fun g' hg'=>hfg g' (mem_cons_of_mem _ hg')) hsf (by omega) hs0 hs10 (fun y=>by simp [ws,hwl y,hsl]) hsb hsq
  refine ⟨?_,hfn',heq'⟩
  simp only [foldl_cons,countP_cons,length_cons,Prod.mk.eta] at hsz' ⊢
  cases hr : r0 g <;> simp [hr] at hss ⊢ <;> omega
lemma main
 (lower : ∀ D : Circuit, Monotone2 D →
   (∀ y : I9, D.eval (ofFn y) = p9 y) → 16 ≤ D.size)
 (C : Circuit) (hmono : Monotone2 C)
 (hcomp : ∀ x : Fin 10 -> Bool,C.eval (ofFn x++[!x 0]) = p10 x) :
 16 + countP r0 C.gates <= C.size := by
 by_contra hlt
 let e0 : List S := [F,inr 4,inr 0,inr 1,inr 6,inr 7,inr 3,inr 5,inr 2,inr 8,inl true]
 obtain ⟨hsz,hfD,hqD⟩ := cind C.gates e0 [] (fun y=>ofFn (lft y)++[!lft y 0])
  hmono (by simp) (by decide) (by decide) (by decide) (fun _=>by simp [e0])
  (fun i=>by by_cases hi : i < 11
             · interval_cases i <;> simp [e0,sb]
             · rw [getD_eq_default _ _ (by simp [e0]; omega)]; trivial)
  (fun y i=>by by_cases hi : i < 11
               · interval_cases i <;> simp [e0,es,wf,lft,getD_eq_getElem?_getD]
               · rw [getD_eq_default _ _ (by simp [e0]; omega),getD_eq_default _ _ (by simp; omega)]; rfl)
 let r := C.gates.foldl cs (e0,[])
 have hO : ∀ y,es (wf r.2 y) (r.1.getD C.output F) = p9 y := fun y=>(hqD y C.output).trans ((hcomp (lft y)).trans (iso y))
 cases ho : r.1.getD C.output F with
 | inl b=>
  have h0' := hO (fun _=>false); have h1' := hO (fun _=>true); rw [ho] at h0' h1'
  have p0 : p9 (fun _=>false) = false := by decide
  have p1 : p9 (fun _=>true) = true := by decide
  simp only [es,p0,p1] at h0' h1'; exact Bool.false_ne_true (h0'.symm.trans h1')
 | inr oD=>
  have hbound := lower ⟨r.2,oD⟩ hfD (fun y=>by have h := hO y; rw [ho] at h; exact h)
  change 16 ≤ r.2.length at hbound
  dsimp only [r] at hbound
  change ¬ (16+countP r0 C.gates <= C.gates.length) at hlt
  simp only [length_nil,Nat.zero_add] at hsz
  omega

end PEqualNP.Outside.L_meta_1884.ReaderBound
