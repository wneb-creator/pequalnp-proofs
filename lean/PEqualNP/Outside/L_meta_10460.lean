import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10460
abbrev zj:=Nat → Nat × Nat
def z3 (kV qV index : Nat) : Nat :=
 (kV>>>(qV*index))&&&((1<<<qV) - 1)
def qE (start qQ : Nat) (yV : Nat → Bool) : Bool :=
 (Nat.rec (motive:=fun _=>Nat → Bool) (fun _=>true)
  (fun _ next i=>yV i&&next (i+1)) qQ) start
theorem zN {start qQ i : Nat} {yV : Nat → Bool}
 (h : qE start qQ yV=true) (lo : start ≤ i) (hi : i < start+qQ) :
 yV i=true:=by
 induction qQ generalizing start with
 | zero=>omega
 | succ qQ ih =>
  change (yV start&&qE (start+1) qQ yV)=true at h
  rcases Bool.and_eq_true_iff.mp h with ⟨here,rest⟩
  by_cases eq : i=start
  · simpa [eq] using here
  · exact ih rest (by omega) (by omega)
theorem vX {start left right : Nat} {yV : Nat → Bool}
  (a : qE start left yV=true)
  (b : qE (start+left) right yV=true) :
  qE start (left+right) yV=true:=by
 induction left generalizing start with
 | zero=>simpa using b
 | succ left ih =>
  rw [Nat.succ_add]
  change (yV start&&qE (start+1) (left+right) yV)=true
  change (yV start&&qE (start+1) left yV)=true at a
  rcases Bool.and_eq_true_iff.mp a with ⟨here,rest⟩
  exact Bool.and_eq_true_iff.mpr ⟨here,ih rest (by
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b)⟩
abbrev Word:=Nat
def yW (base : List Word) (q5 : Nat) : List Word :=
 List.rec (motive:=fun _=>Nat → List Word) (fun _=>[])
  (fun word _ next bits =>
   let tail:=next (bits>>>1)
   if bits&&&1==0 then tail else word :: tail) base q5
def qB (w : Word) (ws : List Word) : List Word :=
 List.rec [w] (fun a tail next=>if w ≤ a then w :: a :: tail else a :: next) ws
def zl (a b op keep : Nat) : Nat:=((a*64+b)*3+op)*4+keep
def zv (mask : Nat) (stock : List Word) (needed : List Word) (word : Word) : List Word :=
 let v:=word&&&mask
 if v==0||v==mask||stock.contains v||needed.contains v then needed
 else v :: needed
def zC (mask : Nat) (stock words : List Word) : List Word :=
 (List.rec (motive:=fun _=>List Word → List Word) id
  (fun word _ next seen=>next (zv mask stock seen word)) words) []
def zc (mask : Nat) (stock : List Word) (history : List (Word × Word × Word))
  (start : List Word) : List Word :=
 List.rec (motive:=fun _=>List Word → List Word) id
  (fun (out,a,b) _ next seen =>
   next (if seen.contains (out&&&mask) then zv mask stock (zv mask stock seen a) b else seen))
  history start
def qW (mask word : Nat) : Bool :=
 let v:=word&&&mask
 v==0||v==mask
def z5 (mask : Nat) (words : List Word) : Nat :=
 List.rec 0 (fun word _ qQ=>if qW mask word then qQ+1 else qQ) words
def qC (mask : Nat) (bank : List Word) (w : Word) : Bool :=
 w==0||w==mask||bank.contains w
def z4 (mask : Nat) (bank : List Word) (word : Word) : Prop :=
 word=0 ∨ word=mask ∨ word ∈ bank
def q59 (mask : Nat) (bank : List Word) (out : Word) : Prop :=
 (∃ a,z4 mask bank a ∧ out=mask^^^a) ∨
 (∃ a b,z4 mask bank a ∧ z4 mask bank b ∧
  (out=a&&&b ∨ out=a|||b))
theorem q7o {mask cut : Nat} (submask : mask&&&cut=cut)
 {roots : List Word} {out : Word} (gate : q59 mask roots out) :
 q59 cut (roots.map (· &&& cut)) (out&&&cut):=by
 have av {word : Word} (ha : z4 mask roots word) :
  z4 cut (roots.map (· &&& cut)) (word&&&cut):=by
  rcases ha with rfl | rfl | hm
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl submask)
  · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
 rcases gate with ⟨a,ha,rfl⟩ | ⟨a,b,ha,hb,eq | eq⟩
 · refine Or.inl ⟨a&&&cut,av ha, ?_⟩
   apply Nat.eq_of_testBit_eq
   intro i
   have cutAt:=congrArg (fun n : Nat=>n.testBit i) submask
   simp only [Nat.testBit_and,Nat.testBit_xor] at cutAt ⊢
   cases h : cut.testBit i
   · simp
   · simp [h] at cutAt
     simp [cutAt]
 · subst out
   refine Or.inr ⟨a&&&cut,b&&&cut,av ha,av hb,Or.inl ?_⟩
   apply Nat.eq_of_testBit_eq
   intro i
   simp only [Nat.testBit_and]
   cases cut.testBit i <;> simp
 · subst out
   refine Or.inr ⟨a&&&cut,b&&&cut,av ha,av hb,Or.inr ?_⟩
   apply Nat.eq_of_testBit_eq
   intro i
   simp only [Nat.testBit_and,Nat.testBit_or]
   cases cut.testBit i <;> simp
def jV (i j : Nat) (word : Word) : Prop :=
 word.testBit i=word.testBit j
def qi (mask word : Word) : Prop:=word ≠ 0 ∧ word ≠ mask
def qj (isOr : Bool) (a b : Word) : Word :=
 if isOr then a|||b else a&&&b
theorem uk (d : Bool) (a b : Word) : qj d a b=qj d b a:=by
 cases d <;> simp [qj,Nat.land_comm,Nat.lor_comm]
variable {mask : Nat} {target : Word}
def qf (mask : Nat) (target : Word) : Nat → Nat → Finset (Word) → Prop
 | 0,t,S=>t=0 ∧ S={target} ∧ qi mask target
 | k+1,t,S =>
  (∃ (u : Nat) (U : Finset (Word)) (a : Word),t=u+1 ∧ S=insert a U ∧ qi mask a ∧
   (mask^^^a) ∉ insert a U ∧ qf mask target k u (insert ((mask^^^a)) U)) ∨
  (∃ (U : Finset (Word)) (a b : Word) (d : Bool),S=insert a (insert b U) ∧ qi mask a ∧ qi mask b ∧ a ≠ b ∧
   qj d a b ∉ insert a (insert b U) ∧ qf mask target k t (insert (qj d a b) U))
theorem qf.stop {target : Word} (hp : qi mask target) : qf mask target 0 0 {target}:=⟨rfl,rfl,hp⟩
theorem qf.unary {target : Word} {k t : Nat} {U : Finset (Word)} {a : Word} (ha : qi mask a)
  (hfresh : (mask^^^a) ∉ insert a U) (tail : qf mask target k t (insert ((mask^^^a)) U)) :
  qf mask target (k+1) (t+1) (insert a U) :=
 Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem qf.binary {target : Word} {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
  (ha : qi mask a) (hb : qi mask b) (hab : a ≠ b)
  (hfresh : qj d a b ∉ insert a (insert b U)) (tail : qf mask target k t (insert (qj d a b) U)) :
  qf mask target (k+1) t (insert a (insert b U)) :=
 Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem qf.ind {target : Word} {motive : ∀ (k t : Nat) (S : Finset (Word)),qf mask target k t S → Prop}
 (stop : ∀ (hp : qi mask target),motive 0 0 {target} (qf.stop hp))
 (unary : ∀ {k t : Nat} {U : Finset (Word)} {a : Word} (ha : qi mask a)
  (hfresh : (mask^^^a) ∉ insert a U) (tail : qf mask target k t (insert ((mask^^^a)) U)),
  motive k t (insert ((mask^^^a)) U) tail → motive (k+1) (t+1) (insert a U) (qf.unary ha hfresh tail))
 (binary : ∀ {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
  (ha : qi mask a) (hb : qi mask b) (hab : a ≠ b)
  (hfresh : qj d a b ∉ insert a (insert b U)) (tail : qf mask target k t (insert (qj d a b) U)),
  motive k t (insert (qj d a b) U) tail →
  motive (k+1) t (insert a (insert b U)) (qf.binary ha hb hab hfresh tail))
 {k t : Nat} {S : Finset (Word)} (h : qf mask target k t S) : motive k t S h:=by
 induction k generalizing t S with
 | zero =>
  obtain ⟨rfl,rfl,hp⟩:=h
  exact stop hp
 | succ k ih =>
  rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
  · exact unary ha hf tail (ih tail)
  · exact binary ha hb hab hf tail (ih tail)
theorem jK {k t S} (h : qf mask target k t S) : ∀ a ∈ S,qi mask a:=by
 induction h using qf.ind with
 | stop hp=>simpa using hp
 | unary ha hf _ ih=>simpa using And.intro ha (fun a h=>ih a (Finset.mem_insert_of_mem h))
 | binary ha hb hab hf _ ih =>
  simp only [Finset.forall_mem_insert]
  exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩
theorem wF {k t S} (h : qf mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1:=by
 induction h using qf.ind with
 | stop hp=>simp
 | @unary k t U a ha hf _ ih =>
  have hu : (mask^^^a) ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem hm)
  rw [Finset.card_insert_of_notMem hu] at ih
  have hc:=Finset.card_insert_le a U
  exact ⟨by omega,by omega⟩
 | @binary k t U a b d ha hb hab hf _ ih =>
  have hu : qj d a b ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  rw [Finset.card_insert_of_notMem hu] at ih
  have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
  have h2:=Finset.card_insert_le (a:=b) (s:=U)
  exact ⟨by omega,by omega⟩
def zB (mask : Nat) (ws : List Word) (w : Word) : Prop :=
 w ∈ ws ∨ ¬qi mask w
def qm (mask word : Nat) : Prop:=word&&&mask=word
theorem zX {bank : List Word} {word : Word}
 (all : ∀ w ∈ bank,qm mask w) (aw : z4 mask bank word) :
 qm mask word:=by
 rcases aw with rfl | rfl | hw
 · simp [qm]
 · simp [qm]
 · exact all _ hw
theorem ux {bank : List Word} {out : Word}
 (all : ∀ w ∈ bank,qm mask w) (g : q59 mask bank out) :
 qm mask out:=by
 rcases g with ⟨a,ha,rfl⟩ | ⟨a,b,ha,hb,ea | ea⟩
 · have h:=q7o (mask:=mask) (cut:=mask) (by simp)
    (roots:=bank) (out:=mask^^^a) (Or.inl ⟨a,ha,rfl⟩)
   have ma:=zX all ha
   unfold qm at ma ⊢
   apply Nat.eq_of_testBit_eq
   intro i
   have bit:=congrArg (fun n : Nat=>n.testBit i) ma
   simp only [Nat.testBit_and,Nat.testBit_xor] at bit ⊢
   cases hm : mask.testBit i <;> simp_all
 · subst out
   have ma:=zX all ha
   have mb:=zX all hb
   simp only [qm] at ma mb ⊢
   rw [Nat.land_assoc,mb]
 · subst out
   have ma:=zX all ha
   have mb:=zX all hb
   unfold qm at ma mb ⊢
   apply Nat.eq_of_testBit_eq
   intro i
   have bitA:=congrArg (fun n : Nat=>n.testBit i) ma
   have bitB:=congrArg (fun n : Nat=>n.testBit i) mb
   simp only [Nat.testBit_and,Nat.testBit_or] at bitA bitB ⊢
   cases hm : mask.testBit i <;> simp_all
def vJ (mask : Nat) (bank : List Word) (out : Word) : Prop :=
 ∃ d a b,a ∈ bank ∧ b ∈ bank ∧ qi mask a ∧ qi mask b ∧
  a ≠ b ∧ out=qj d a b
theorem vq {bank : List Word}
 (all : ∀ w ∈ bank,qm mask w) (d : Bool) {a b : Word}
 (ha : z4 mask bank a) (hb : z4 mask bank b) :
 zB mask bank (qj d a b) ∨ vJ mask bank (qj d a b):=by
 have c0 : zB mask bank 0:=Or.inr fun h=>h.1 rfl
 have cm : zB mask bank mask:=Or.inr fun h=>h.2 rfl
 have classify {w : Word} (hw : z4 mask bank w) :
  w=0 ∨ w=mask ∨ w ∈ bank ∧ qi mask w:=by
  by_cases zh : w=0
  · exact Or.inl zh
  by_cases mh : w=mask
  · exact Or.inr (Or.inl mh)
  exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh,zh,mh⟩)
 have ma : a&&&mask=a:=zX all ha
 have mb : b&&&mask=b:=zX all hb
 have absorbA : a|||mask=mask:=by
  apply Nat.eq_of_testBit_eq
  intro i
  have h:=congrArg (fun n : Nat=>n.testBit i) ma
  simp only [Nat.testBit_and,Nat.testBit_or] at h ⊢
  cases hm : mask.testBit i <;> simp_all
 have absorbB : b|||mask=mask:=by
  apply Nat.eq_of_testBit_eq
  intro i
  have h:=congrArg (fun n : Nat=>n.testBit i) mb
  simp only [Nat.testBit_and,Nat.testBit_or] at h ⊢
  cases hm : mask.testBit i <;> simp_all
 rcases classify ha with rfl | hma | ⟨ha',pa⟩
 · rw [uk]
   cases d
   · exact Or.inl (by simpa [qj] using c0)
   · rcases hb with hz | hm | hv
     · exact Or.inl (by simpa [qj,hz] using c0)
     · exact Or.inl (by simpa [qj,hm] using cm)
     · exact Or.inl (by simpa [qj,zB] using
        (Or.inl hv : zB mask bank b))
 · rw [hma,uk]
   cases d
   · rcases hb with hz | hm | hv
     · exact Or.inl (by simpa [qj,hz] using c0)
     · exact Or.inl (by simpa [qj,hm] using cm)
     · exact Or.inl (by simpa [qj,mb,zB] using
        (Or.inl hv : zB mask bank b))
   · exact Or.inl (by simpa [qj,absorbB] using cm)
 rcases classify hb with rfl | hmb | ⟨hb',pb⟩
 · cases d
   · exact Or.inl (by simpa [qj] using c0)
   · exact Or.inl (by simpa [qj,zB] using
      (Or.inl ha' : zB mask bank a))
 · rw [hmb]
   cases d
   · exact Or.inl (by simpa [qj,ma,zB] using
      (Or.inl ha' : zB mask bank a))
   · exact Or.inl (by simpa [qj,absorbA] using cm)
 by_cases eq : a=b
 · subst b
   cases d <;> exact Or.inl (by simpa [qj,zB] using
    (Or.inl ha' : zB mask bank a))
 exact Or.inr ⟨d,a,b,ha',hb',pa,pb,eq,rfl⟩
theorem vF {x w : Word} {ws : List Word} :
  x ∈ qB w ws ↔ x=w ∨ x ∈ ws:=by
 induction ws with
 | nil=>simp [qB]
 | cons a tail ih =>
  change x ∈ (if w ≤ a then w :: a :: tail else a :: qB w tail) ↔ _
  split <;> simp [ih,or_assoc,or_left_comm]
theorem q09 {w : Word} {ws : List Word} (nd : ws.Nodup) (jB : w ∉ ws) :
 (qB w ws).Nodup:=by
 induction ws with
 | nil=>simp [qB]
 | cons a tail ih =>
  change (if w ≤ a then w :: a :: tail else a :: qB w tail).Nodup
  split
  · exact List.nodup_cons.mpr ⟨jB,nd⟩
  have hn:=List.nodup_cons.mp nd
  have hnot : w ≠ a ∧ w ∉ tail:=by simpa using jB
  exact List.nodup_cons.mpr ⟨by simp [vF,hnot.1.symm,hn.1],ih hn.2 hnot.2⟩
theorem w8 (w : Word) (ws : List Word) :
  (qB w ws).toFinset=insert w ws.toFinset:=by
 ext x
 simp [vF]
theorem q7a {ws : List Word} (nd : ws.Nodup) (w : Word) :
  (ws.erase w).toFinset=ws.toFinset.erase w:=by
 ext x
 simp [nd.mem_erase_iff,and_comm]
theorem u5 {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
  zl a b op keep % 4=keep ∧
  zl a b op keep / 4 % 3=op ∧
  zl a b op keep / (4*3*64)=a ∧
  zl a b op keep / (4*3) % 64=b:=by
 unfold zl
 omega
def zu (save : Bool) (w : Word) (ws : List Word) : List Word :=
 if save then ws else ws.erase w
theorem wg {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
 (zu save w ws).Nodup:=by
 cases save
 · exact nd.erase _
 · exact nd
theorem uy (save : Bool) (w : Word) (ws : List Word) :
 ∀ v ∈ zu save w ws,v ∈ ws:=by
 cases save
 · exact fun _ h=>List.mem_of_mem_erase h
 · exact fun _ h=>h
theorem q6S {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
 (eq : ws.toFinset=insert w U) :
 (zu (decide (w ∈ U)) w ws).toFinset=U:=by
 by_cases hw : w ∈ U
 · simp [zu,hw,eq,Finset.insert_eq_of_mem hw]
 · simp [zu,hw,q7a nd,eq]
theorem q7u {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
  (ab : a ≠ b) (eq : ws.toFinset=insert a (insert b U)) :
  (zu (decide (b ∈ U)) b (zu (decide (a ∈ U)) a ws)).toFinset=U:=by
 have x : decide (a ∈ insert b U)=decide (a ∈ U):=by simp [ab]
 have h:=q6S nd eq
 rw [x] at h
 exact q6S (wg nd _ _) h
theorem q2m {ws : List Word} {x : Word} (h : x ∈ ws) :
  ws.getD (ws.idxOf x) 0=x:=by
 have inb:=List.idxOf_lt_length_iff.mpr h
 simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inb] using
  List.getElem_idxOf inb
theorem wT (base : List Word) (q5 : Nat) : (yW base q5).Sublist base:=by
 induction base generalizing q5 with
 | nil=>exact List.Sublist.slnil
 | cons w ws ih =>
  change (if q5&&&1==0 then yW ws (q5>>>1)
   else w :: yW ws (q5>>>1)).Sublist (w :: ws)
  split
  · exact (ih _).cons _
  · exact (ih _).cons₂ _
theorem q9n (base : List Word) (S : Finset Word) :
 ∃ q5 < 2 ^ base.length,(yW base q5).toFinset=base.toFinset ∩ S:=by
 induction base with
 | nil=>exact ⟨0,by simp,by simp [yW]⟩
 | cons w ws ih =>
  obtain ⟨q5,htoken,ih⟩:=ih
  let bit : Nat:=if w ∈ S then 1 else 0
  have hbit : bit < 2:=by dsimp [bit];split <;> decide
  let code:=2*q5+bit
  have low : code&&&1=bit:=by
   rw [show (1 : Nat)=2 ^ 1 - 1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
   dsimp [code]
   omega
  have high : code>>>1=q5:=by
   rw [Nat.shiftRight_eq_div_pow]
   change code / 2=q5
   dsimp [code]
   omega
  refine ⟨code, ?_, ?_⟩
  · simp only [List.length_cons,pow_succ]
    dsimp [code]
    omega
  · change (if code&&&1==0 then yW ws (code>>>1)
     else w :: yW ws (code>>>1)).toFinset=_
    rw [low,high]
    by_cases hw : w ∈ S
    · simp [bit,hw,ih]
    · simp [bit,hw,ih]
theorem q1D {i j k t : Nat} {S : Finset Word}
 (h : qf mask target k t S) (m : jV i j mask)
 (all : ∀ w ∈ S,jV i j w) : jV i j target:=by
 induction h using qf.ind with
 | stop=>exact all _ (Finset.mem_singleton_self _)
 | @unary k t U a pa jB tail ih =>
  apply ih
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · simp only [jV,Nat.testBit_xor]
    rw [show mask.testBit i=mask.testBit j from m,
     show a.testBit i=a.testBit j from all a (Finset.mem_insert_self _ _)]
  · exact all _ (Finset.mem_insert_of_mem hw)
 | @binary k t U a b d pa pb ab jB tail ih =>
  apply ih
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · have aa : a.testBit i=a.testBit j:=all a (Finset.mem_insert_self _ _)
    have bb : b.testBit i=b.testBit j:=all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    cases d <;> simp [jV,qj,Nat.testBit_and,Nat.testBit_or,aa,bb]
  · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
theorem kU {i : Nat} (mt : qm mask target) (ht : target.testBit i=true) :
  mask.testBit i=true:=by
 have h:=congrArg (fun n : Nat=>n.testBit i) mt
 simpa [Nat.testBit_and,ht] using h
variable {rows : Nat}
def qI (rows : Nat) : Nat:=2 ^ rows - 1
theorem q7l (v : BitVec rows) : qm (qI rows) v.toNat:=by
 unfold qm qI
 rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt v.isLt]
theorem q9F (v : BitVec rows) : (~~~v).toNat=qI rows^^^v.toNat:=by
 rw [← BitVec.xor_allOnes,BitVec.toNat_xor,Nat.xor_comm,BitVec.toNat_allOnes]
 rfl
theorem yx (bank : List (BitVec rows)) (i : Nat) :
  z4 (qI rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat:=by
 rw [List.getD_eq_getElem?_getD]
 cases h : bank[i]? with
 | none=>exact Or.inl rfl
 | some a=>exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))
theorem jn {mask : Nat} {bank : List Word} {v : Word} :
  qC mask bank v=true ↔ z4 mask bank v:=by
 simp [qC,z4,or_assoc]
abbrev wo (rows : Nat):=Fin rows → Bool
def zq (f : wo rows) : BitVec rows :=
 (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem y6 (f : wo rows) (i : Fin rows) :
  (zq f).getLsbD i.val=f i:=by
 simp only [zq,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
  List.getD_eq_getElem?_getD,List.getElem?_ofFn]
 simp [i.isLt]
theorem q6j (a b : wo rows) :
  zq (fun i=>a i&&b i)=zq a&&&zq b:=by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 rw [BitVec.getLsbD_and,y6 a ⟨i,hi⟩,y6 b ⟨i,hi⟩,y6 _ ⟨i,hi⟩]
theorem q7R (a b : wo rows) :
  zq (fun i=>a i||b i)=zq a|||zq b:=by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 rw [BitVec.getLsbD_or,y6 a ⟨i,hi⟩,y6 b ⟨i,hi⟩,y6 _ ⟨i,hi⟩]
def yZ (f : wo rows) : Word:=(zq f).toNat
def z9 (qK : Fin rows → Fin rows) (word : Word) : Word :=
 yZ fun i=>word.testBit (qK i).val
theorem q60 : yZ (fun _ : Fin rows=>false)=0:=by
 have eq : zq (fun _ : Fin rows=>false)=0:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [y6 _ ⟨i,hi⟩]
  simp
 simp [yZ,eq]
theorem q7n (qK : Fin rows → Fin rows) : z9 qK 0=0:=by
 simpa [z9] using (q60 (rows:=rows))
theorem q8e (qK : Fin rows → Fin rows) (a b : Word) :
  z9 qK (a&&&b)=z9 qK a&&&z9 qK b:=by
 simp only [z9,Nat.testBit_and,yZ,q6j,BitVec.toNat_and]
theorem q9o (qK : Fin rows → Fin rows) (a b : Word) :
  z9 qK (a|||b)=z9 qK a|||z9 qK b:=by
 simp only [z9,Nat.testBit_or,yZ,q7R,BitVec.toNat_or]
theorem q8c (qK : Fin rows → Fin rows) (a b : Word) :
  z9 qK (a^^^b)=z9 qK a^^^z9 qK b:=by
 have eq : zq (fun i=>(a^^^b).testBit (qK i).val) =
   zq (fun i=>a.testBit (qK i).val) ^^^
   zq (fun i=>b.testBit (qK i).val):=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_xor,y6 _ ⟨i,hi⟩,y6 _ ⟨i,hi⟩,y6 _ ⟨i,hi⟩]
  exact Nat.testBit_xor ..
 simpa only [z9,yZ,BitVec.toNat_xor] using congrArg BitVec.toNat eq
theorem uq (qK : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
  (z9 qK word).testBit i.val=word.testBit (qK i).val :=
 y6 _ i
theorem uo (qK : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
  (z9 qK word).testBit i=false:=by
 apply Nat.testBit_lt_two_pow
 exact Nat.lt_of_lt_of_le (show (zq _).toNat < 2 ^ rows from BitVec.isLt _)
  (Nat.pow_le_pow_right (by decide) h)
theorem q8d (qK : Fin rows → Fin rows) (onto : Function.Surjective qK)
 {a b : Word} (ba : qm (qI rows) a) (bb : qm (qI rows) b)
 (eq : z9 qK a=z9 qK b) : a=b:=by
 apply Nat.eq_of_testBit_eq
 intro i
 by_cases inside : i < rows
 · obtain ⟨j,h⟩:=onto ⟨i,inside⟩
   have bit:=congrArg (fun w : Nat=>w.testBit j.val) eq
   simpa only [uq,h] using bit
 · have ea:=congrArg (fun w : Nat=>w.testBit i) ba
   have eb:=congrArg (fun w : Nat=>w.testBit i) bb
   simp only [Nat.testBit_and,qI,Nat.testBit_two_pow_sub_one,inside,decide_false,
    Bool.and_false] at ea eb
   rw [← ea, ← eb]
def q7i (mask goal : Word) (zi : Fin rows → Fin rows) : Prop :=
 Function.Surjective zi ∧ z9 zi mask=mask ∧ z9 zi goal=goal
abbrev qg:=List (Word × Nat) × List (Word × Nat)
abbrev z0:=List qg
def wE (m : qg) (w : Word) : Word :=
 let left:=List.rec 0 (fun (part,n) _ acc=>((w&&&part)<<<n)|||acc) m.1
 let right:=List.rec 0 (fun (part,n) _ acc=>((w&&&part)>>>n)|||acc) m.2
 left|||right
def y7 (f : Word → Word) : Prop :=
 ∀ w i,(f w).testBit i=true ↔ ∃ j,w.testBit j=true ∧ (f (2 ^ j)).testBit i=true
theorem q1y : y7 (fun _=>0):=by
 simp [y7]
theorem q0S {f g : Word → Word} (hf : y7 f) (hg : y7 g) :
 y7 (fun w=>f w|||g w):=by
 intro w i
 change ((f w|||g w).testBit i=true) ↔ _
 simp only [Nat.testBit_or,Bool.or_eq_true]
 rw [hf w i,hg w i]
 constructor
 · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
   · exact ⟨j,hw,Or.inl hj⟩
   · exact ⟨j,hw,Or.inr hj⟩
 · rintro ⟨j,hw,hj | hj⟩
   · exact Or.inl ⟨j,hw,hj⟩
   · exact Or.inr ⟨j,hw,hj⟩
theorem q5W (mask n : Nat) : y7 (fun w=>(w&&&mask)<<<n):=by
 intro w i
 simp only [Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_two_pow,
  Bool.and_eq_true,decide_eq_true_eq]
 constructor
 · rintro ⟨h,hw,hm⟩
   exact ⟨i-n,hw,h,rfl,hm⟩
 · rintro ⟨j,hw,h,rfl,hm⟩
   exact ⟨h,hw,hm⟩
theorem q57 (mask n : Nat) : y7 (fun w=>(w&&&mask)>>>n):=by
 intro w i
 simp only [Nat.testBit_shiftRight,Nat.testBit_and,Nat.testBit_two_pow,
  Bool.and_eq_true,decide_eq_true_eq]
 constructor
 · rintro ⟨hw,hm⟩
   exact ⟨n+i,hw,rfl,hm⟩
 · rintro ⟨j,hw,rfl,hm⟩
   exact ⟨hw,hm⟩
theorem q5v (move : qg) : y7 (wE move):=by
 obtain ⟨left,right⟩:=move
 unfold wE
 apply q0S
 · induction left with
   | nil=>exact q1y
   | cons kt rest ih =>
    obtain ⟨part,qQ⟩:=kt
    exact q0S (q5W part qQ) ih
 · induction right with
   | nil=>exact q1y
   | cons kt rest ih =>
    obtain ⟨part,qQ⟩:=kt
    exact q0S (q57 part qQ) ih
def yG (move : z0) (w : Word) : Word :=
 (List.rec (motive:=fun _=>Word → Word) id
  (fun step _ next w=>next (wE step w)) move) w
theorem q7X : y7 id:=by
 intro w i
 change w.testBit i=true ↔ ∃ j,w.testBit j=true ∧ (2 ^ j).testBit i=true
 simp [Nat.testBit_two_pow]
theorem q5X {f g : Word → Word} (hf : y7 f) (hg : y7 g) :
 y7 (fun w=>f (g w)):=by
 intro w i
 change (f (g w)).testBit i=true ↔ ∃ j,w.testBit j=true ∧ (f (g (2 ^ j))).testBit i=true
 rw [hf]
 constructor
 · rintro ⟨j,gj,fj⟩
   obtain ⟨k,wk,gk⟩:=(hg w j).mp gj
   exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
 · rintro ⟨j,wj,h⟩
   obtain ⟨k,gk,fk⟩:=(hf (g (2^j)) i).mp h
   exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩
theorem q5w (move : z0) : y7 (yG move):=by
 induction move with
 | nil=>exact q7X
 | cons op ops ih =>
  change y7 (fun w=>yG ops (wE op w))
  exact q5X ih (q5v op)
def q7p (axes : List Nat) (w7 row : Nat) : Nat :=
 w7^^^(List.rec (motive:=fun _=>Nat → Nat) (fun _=>0)
  (fun j _ next i=>(if row.testBit i then 1<<<j else 0)|||next (i+1)) axes) 0
theorem q5j (zi : Fin rows → Fin rows) : y7 (z9 zi):=by
 intro w i
 by_cases inside : i < rows
 · let ii : Fin rows:=⟨i,inside⟩
   change (z9 zi w).testBit ii.val=true ↔ _
   rw [uq]
   constructor
   · intro h
     refine ⟨(zi ii).val,h,?_⟩
     change (z9 zi (2 ^ (zi ii).val)).testBit ii.val=true
     rw [uq,Nat.testBit_two_pow]
     simp
   · rintro ⟨j,h,bit⟩
     change (z9 zi (2^j)).testBit ii.val=true at bit
     rw [uq,Nat.testBit_two_pow,decide_eq_true_eq] at bit
     exact bit ▸ h
 · rw [uo _ _ _ (Nat.le_of_not_gt inside)]
   simp [uo _ _ _ (Nat.le_of_not_gt inside)]
theorem q1S {zi : Fin rows → Fin rows} {mask : Word} {move : z0}
 (bounded : qm (qI rows) mask)
 (basis : ∀ i : Fin rows,mask.testBit i.val=true →
  yG move (2 ^ i.val)=z9 zi (2 ^ i.val))
 {w : Word} (zM : qm mask w) : yG move w=z9 zi w:=by
 apply Nat.eq_of_testBit_eq
 intro i
 apply Bool.eq_iff_iff.mpr
 rw [q5w,q5j]
 have source {j : Nat} (bit : w.testBit j=true) :
  yG move (2^j)=z9 zi (2^j):=by
  have m : mask.testBit j=true:=by
   have eq:=congrArg (fun x : Nat=>x.testBit j) zM
   simpa [Nat.testBit_and,bit] using eq
  have within : j < rows:=by
   have eq:=congrArg (fun x : Nat=>x.testBit j) bounded
   simpa [Nat.testBit_and,qI,Nat.testBit_two_pow_sub_one,m] using eq
  exact basis ⟨j,within⟩ m
 constructor <;> rintro ⟨j,hj,hi⟩
 · exact ⟨j,hj,by rwa [← source hj]⟩
 · exact ⟨j,hj,by rwa [source hj]⟩
theorem q6H {zi inverse : Fin rows → Fin rows}
 (left : ∀ i,inverse (zi i)=i) :
 ∀ j : Fin rows,zi (inverse j)=j →
  z9 zi (2 ^ j.val)=2 ^ (inverse j).val:=by
 intro j right
 apply Nat.eq_of_testBit_eq
 intro i
 by_cases inside : i < rows
 · let pos : Fin rows:=⟨i,inside⟩
   change (z9 zi (2 ^ j.val)).testBit pos.val=_
   rw [uq,Nat.testBit_two_pow,Nat.testBit_two_pow]
   apply (Bool.eq_iff_iff).mpr
   simp only [decide_eq_true_eq]
   constructor
   · intro eq
     have e : j=zi pos:=Fin.ext eq
     rw [e,left]
   · intro eq
     have hp : inverse j=pos:=Fin.ext eq
     rw [← hp,right]
 · rw [uo _ _ _ (Nat.le_of_not_gt inside),Nat.testBit_two_pow]
   have ne : (inverse j).val ≠ i:=by have:=(inverse j).isLt;omega
   simp [ne]
theorem q3S {zi inverse : Fin rows → Fin rows} {mask goal : Word} {move : z0}
  (left : ∀ i,inverse (zi i)=i)
  (right : ∀ i,zi (inverse i)=i)
  (bm : qm (qI rows) mask)
  (gm : qm mask goal)
  (basis : ∀ i : Fin rows,mask.testBit i.val=true →
   yG move (2 ^ i.val)=2 ^ (inverse i).val)
  (sameMask : yG move mask=mask) (sameGoal : yG move goal=goal) :
  q7i mask goal zi ∧ ∀ w,qm mask w → yG move w=z9 zi w:=by
 have agree {w : Word} (hw : qm mask w) : yG move w=z9 zi w :=
  q1S bm (fun i h=>(basis i h).trans (q6H left i (right i)).symm) hw
 exact ⟨⟨fun i=>⟨inverse i,right i⟩,(agree (by simp [qm])).symm.trans sameMask,
  (agree gm).symm.trans sameGoal⟩,fun _ h=>agree h⟩
abbrev zW:=Word × Nat × Nat
def q0j (w : zW) : Word:=w.1
def wO (mask target : Word) (stock : List Word) (kt : zW) : Bool :=
 let (w,p,n):=kt
 mask.testBit p&&mask.testBit n&&target.testBit p && !target.testBit n &&
  (w.testBit p != w.testBit n) &&
  stock.all (fun x=>x==w||x.testBit p==x.testBit n)
theorem q2y {stock : List Word} {kt : zW} {S : Finset Word} {k t : Nat}
  (ok : wO mask target stock kt=true)
  (sub : ∀ w ∈ S,w ∈ stock) (y1 : qf mask target k t S) :
  q0j kt ∈ S:=by
 obtain ⟨w,p,n⟩:=kt
 simp only [wO,Bool.and_eq_true] at ok
 obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩:=ok
 by_contra no
 have all : ∀ x ∈ S,jV p n x:=by
  intro x hx
  have h:=List.all_eq_true.mp rest x (sub x hx)
  have hw : x ≠ w:=fun e=>no (by simpa [q0j,e] using hx)
  simpa [hw,jV] using h
 have agree:=q1D y1 (mp.trans mn.symm) all
 have falseBit : target.testBit n=false:=by simpa using tn
 simp [jV,tp,falseBit] at agree
theorem q8W (goal : Word) (D D' : Finset Word) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
 (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
 (hsub : ∀ x ∈ D',x ≠ w → x ∈ D)
 (hf : ∀ e i,goal.testBit e=true → goal.testBit i=false →
  f e i ∈ D' ∧ (f e i).testBit e=true ∧ (f e i).testBit i=false)
 (hr : ∀ e i e' i',goal.testBit e=true → goal.testBit e'=true → goal.testBit i=false → goal.testBit i'=false → f e i=f e' i' → f e i'=f e i)
 (hcu : ∀ e i,w.testBit e=true → w.testBit i=false → c e i=true →
  u.testBit e=true ∧ u.testBit i=false)
 (hcv : ∀ e i,w.testBit e=true → w.testBit i=false → c e i=false →
  v.testBit e=true ∧ v.testBit i=false)
 (hc : ∀ e i e' i',c e i=c e' i' → c e i'=c e i) :
 ∃ g : ℕ → ℕ → ℕ,
  (∀ e i,goal.testBit e=true → goal.testBit i=false →
   g e i ∈ D ∧ (g e i).testBit e=true ∧ (g e i).testBit i=false) ∧
  (∀ e i e' i',goal.testBit e=true → goal.testBit e'=true → goal.testBit i=false → goal.testBit i'=false → g e i=g e' i' → g e i'=g e i):=by
 have hg : ∀ e i,goal.testBit e=true → goal.testBit i=false → f e i=w →
  ((if f e i=w then (cond (c e i) u v) else f e i)=u ∧ c e i=true) ∨
  ((if f e i=w then (cond (c e i) u v) else f e i)=v ∧ c e i=false):=by
  intro e i _ _ h
  rw [ite_eq_left (h)]
  cases c e i
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩
 refine ⟨fun e i=>if f e i=w then (cond (c e i) u v) else f e i, ?_, ?_⟩
 · intro e i he hi
   obtain ⟨h1,h2,h3⟩:=hf e i he hi
   show (if f e i=w then (cond (c e i) u v) else f e i) ∈ D ∧
    (if f e i=w then (cond (c e i) u v) else f e i).testBit e=true ∧
    (if f e i=w then (cond (c e i) u v) else f e i).testBit i=false
   by_cases hw : f e i=w
   · rw [hw] at h2 h3
     rcases hg e i he hi hw with ⟨hx,hcc⟩ | ⟨hx,hcc⟩
     · rw [hx];exact ⟨hu,hcu e i h2 h3 hcc⟩
     · rw [hx];exact ⟨hv,hcv e i h2 h3 hcc⟩
   · rw [ite_eq_right (hw)];exact ⟨hsub _ h1 hw,h2,h3⟩
 · intro e i e' i' he he' hi hi' heq
   show (if f e i'=w then (cond (c e i') u v) else f e i') =
    (if f e i=w then (cond (c e i) u v) else f e i)
   have heq' : (if f e i=w then (cond (c e i) u v) else f e i) =
    (if f e' i'=w then (cond (c e' i') u v) else f e' i'):=heq
   by_cases h1 : f e i=w
   · by_cases h2 : f e' i'=w
     · have h3 : f e i'=w:=(hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
       have hcc : c e i=c e' i':=by
        rcases hg e i he hi h1 with ⟨hx,hx'⟩ | ⟨hx,hx'⟩ <;>
         rcases hg e' i' he' hi' h2 with ⟨hy,hy'⟩ | ⟨hy,hy'⟩
        · rw [hx',hy']
        · exact absurd (hx.symm.trans (heq'.trans hy)) huv
        · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
        · rw [hx',hy']
       rw [ite_eq_left (h3),ite_eq_left (h1),hc e i e' i' hcc]
     · exfalso
       rw [ite_eq_right (h2)] at heq'
       have hm:=(hf e' i' he' hi').1
       rcases hg e i he hi h1 with ⟨hx,_⟩ | ⟨hx,_⟩
       · exact huD (by rw [← hx,heq'];exact hm)
       · exact hvD (by rw [← hx,heq'];exact hm)
   · by_cases h2 : f e' i'=w
     · exfalso
       rw [ite_eq_right (h1)] at heq'
       have hm:=(hf e i he hi).1
       rcases hg e' i' he' hi' h2 with ⟨hx,_⟩ | ⟨hx,_⟩
       · exact huD (by rw [← hx, ← heq'];exact hm)
       · exact hvD (by rw [← hx, ← heq'];exact hm)
     · have h1n : (if f e i=w then (cond (c e i) u v) else f e i)=f e i:=ite_eq_right h1
       have h2n : (if f e' i'=w then (cond (c e' i') u v) else f e' i')=f e' i':=ite_eq_right h2
       rw [h1n,h2n] at heq'
       have h3:=hr e i e' i' he he' hi hi' heq'
       have h3n : ¬ f e i'=w:=by rw [h3];exact h1
       rw [h1n,ite_eq_right (h3n)]
       exact h3
theorem q7h (u v e i : ℕ) (h1 : (u&&&v).testBit e=true) (_h2 : (u&&&v).testBit i=false)
  (h3 : (!(u.testBit i))=true) : u.testBit e=true ∧ u.testBit i=false:=by
 rw [Nat.testBit_and] at h1
 cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem q7g (u v e i : ℕ) (h1 : (u&&&v).testBit e=true) (h2 : (u&&&v).testBit i=false)
  (h3 : (!(u.testBit i))=false) : v.testBit e=true ∧ v.testBit i=false:=by
 rw [Nat.testBit_and] at h1 h2
 cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem q8U (u v e i : ℕ) (_h1 : (u|||v).testBit e=true) (h2 : (u|||v).testBit i=false)
  (h3 : u.testBit e=true) : u.testBit e=true ∧ u.testBit i=false:=by
 rw [Nat.testBit_or] at h2
 cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem q8T (u v e i : ℕ) (h1 : (u|||v).testBit e=true) (h2 : (u|||v).testBit i=false)
  (h3 : u.testBit e=false) : v.testBit e=true ∧ v.testBit i=false:=by
 rw [Nat.testBit_or] at h1 h2
 cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
def q3f (goal : Word) (ws : Finset Word) : Prop :=
 ∃ f : Nat → Nat → Word,
  (∀ e i,goal.testBit e=true → goal.testBit i=false →
   f e i ∈ ws ∧ (f e i).testBit e=true ∧ (f e i).testBit i=false) ∧
  (∀ e i e' i',goal.testBit e=true → goal.testBit e'=true →
   goal.testBit i=false → goal.testBit i'=false → f e i=f e' i' → f e i'=f e i)
theorem q8k {mask goal : Word} {k : Nat} {S : Finset Word}
 (y1 : qf mask goal k 0 S) (tight : S.card=k+1) : q3f goal S:=by
 induction k generalizing S with
 | zero =>
  obtain ⟨_,eq,_⟩:=y1
  subst S
  exact ⟨fun _ _=>goal,fun _ _ hp hn=>⟨by simp,hp,hn⟩,fun _ _ _ _ _ _ _ _ _=>rfl⟩
 | succ k ih =>
  rcases y1 with ⟨u,U,a,eq,_⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,jB,tail⟩
  · omega
  let w:=qj op a b
  have wU : w ∉ U:=fun h=>jB (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have wA : w ≠ a:=fun eq=>jB (Finset.mem_insert.mpr (Or.inl eq))
  have wB : w ≠ b:=fun eq=>jB (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
  have tailSize:=(wF tail).2
  change (insert w U).card+0 ≤ k+1 at tailSize
  rw [Finset.card_insert_of_notMem wU] at tailSize
  have paCard:=Finset.card_insert_le a (insert b U)
  have pbCard:=Finset.card_insert_le b U
  have aU : a ∉ U:=by
   intro h
   rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
   omega
  have bU : b ∉ U:=by
   intro h
   rw [Finset.insert_eq_of_mem h] at tight
   have:=Finset.card_insert_le a U
   omega
  obtain ⟨f,hf,hr⟩:=ih tail (by
   change (insert w U).card=k+1
   rw [Finset.card_insert_of_notMem wU]
   omega)
  have keepA : a ∉ insert w U:=by simp [wA.symm,aU]
  have keepB : b ∉ insert w U:=by simp [wB.symm,bU]
  have other : ∀ x ∈ insert w U,x ≠ w → x ∈ insert a (insert b U):=by
   intro x hx hn
   exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
  have ha : a ∈ insert a (insert b U):=Finset.mem_insert_self ..
  have hb : b ∈ insert a (insert b U):=Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  cases op
  · exact q8W goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
     (fun e i h1 h2 h3=>q7h a b e i h1 h2 h3) (fun e i h1 h2 h3=>q7g a b e i h1 h2 h3)
     (fun _ _ _ _ h=>h.symm)
  · exact q8W goal _ _ a b w (fun e _=>a.testBit e) f ha hb ab keepA keepB other hf hr
     (fun e i h1 h2 h3=>q8U a b e i h1 h2 h3) (fun e i h1 h2 h3=>q8T a b e i h1 h2 h3)
     (fun _ _ _ _ _=>rfl)
theorem q2f {mask goal : Word} {k : Nat} {S : Finset Word}
 (y1 : qf mask goal k 0 S) {p n : Nat}
 (hp : goal.testBit p=true) (hn : goal.testBit n=false) :
 ∃ w ∈ S,w.testBit p=true ∧ w.testBit n=false:=by
 induction k generalizing S with
 | zero =>
  obtain ⟨_,rfl,_⟩:=y1
  exact ⟨goal,by simp,hp,hn⟩
 | succ k ih =>
  rcases y1 with ⟨u,U,a,ueq,_⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,jB,tail⟩
  · omega
  obtain ⟨w,hw,wp,wn⟩:=ih tail
  rcases Finset.mem_insert.mp hw with eq | hU
  · subst w
    cases op
    · by_cases ha : a.testBit n=false
      · exact ⟨a,Finset.mem_insert_self ..,q7h a b p n wp wn (by simp [ha])⟩
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
         q7g a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
    · by_cases ha : a.testBit p=true
      · exact ⟨a,Finset.mem_insert_self ..,q8U a b p n wp wn ha⟩
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
         q8T a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
  · exact ⟨w,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩
namespace q0
def qam (w d : ℕ) : Bool :=
 Nat.beq (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) 0 &&
 Nat.beq (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) 0
def blk (m : Bool) (w d : ℕ) : Bool:=cond m (qam w d) (Nat.beq w d)
theorem q8j (w : ℕ) : w&&&(16777215 - w)=0:=by
 rcases lt_or_ge w (2 ^ 24) with h | h
 · apply Nat.eq_of_testBit_eq
   intro i
   have e : 16777215 - w=2 ^ 24 - (w+1):=by omega
   rw [e,Nat.testBit_and,Nat.testBit_two_pow_sub_succ h]
   cases w.testBit i <;> simp
 · have e : 16777215 - w=0:=by omega
   simp [e]
theorem q9w (w : ℕ) : qam w w=true:=by
 have h:=q8j w
 have h1 : Nat.land (Nat.land w 4095) (Nat.sub 16777215 w)=0:=by
  show (w&&&4095)&&&(16777215 - w)=0
  rw [Nat.and_right_comm,h];simp
 have h2 : Nat.land (Nat.land w (Nat.sub 16777215 w)) 16773120=0:=by
  show (w&&&(16777215 - w))&&&16773120=0
  rw [h];simp
 unfold qam
 rw [h1,h2]
 rfl
theorem q7W (m : Bool) (w : ℕ) : blk m w w=true:=by
 cases m
 · simp [blk]
 · simp [blk,q9w]
def vt (m : Bool) : Finset Word → Nat → Prop
 | D,0=>D={4095}
 | D,k+1=>D={4095} ∨ ∃ (u v w : Word) (ka kb : Bool),
  u ∈ D ∧ v ∈ D ∧ (w=u&&&v ∨ w=u|||v) ∧
  (∀ d ∈ D,blk m w d=false) ∧ True ∧
  vt m (insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))) k
theorem vt.ind {m : Bool} {P : ∀ D k,vt m D k → Prop}
 (done : ∀ k,P {4095} k (by cases k <;> first | rfl | exact Or.inl rfl))
 (step : ∀ D k u v w (ka kb : Bool) (hu : u ∈ D) (hv : v ∈ D)
  (hw : w=u&&&v ∨ w=u|||v) (hd : ∀ d ∈ D,blk m w d=false),True →
  (tail : vt m (insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))) k) →
  P (insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))) k tail →
  P D (k+1) (Or.inr ⟨u,v,w,ka,kb,hu,hv,hw,hd,trivial,tail⟩))
 {D k} (h : vt m D k) : P D k h:=by
 induction k generalizing D with
 | zero =>
  change D={4095} at h
  subst D
  exact done 0
 | succ k ih =>
  rcases h with he | ⟨u,v,w,ka,kb,hu,hv,gate,hd,hb,tail⟩
  · subst D
    exact done (k+1)
  · exact step D k u v w ka kb hu hv gate hd hb tail (ih tail)
theorem vt.card {m : Bool} {D : Finset ℕ} {k : ℕ} (h : vt m D k) : D.card ≤ k+1:=by
 induction h using vt.ind with
 | done k=>simp
 | step D k u v w ka kb hu hv hw hd hb _ ih =>
  have hwD : w ∉ D:=fun hm=>by
   have:=hd w hm
   rw [q7W] at this
   exact Bool.noConfusion this
  have hwF : w ∉ D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)) :=
   fun hm=>hwD (Finset.mem_of_mem_filter _ hm)
  rw [Finset.card_insert_of_notMem hwF] at ih
  have hsub : D ⊆ insert u (insert v
   (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))):=by
   intro x hx
   by_cases h1 : x=u
   · simp [h1]
   by_cases h2 : x=v
   · simp [h2]
   simp [hx,h1,h2]
  have h2:=Finset.card_le_card hsub
  have h3:=Finset.card_insert_le u (insert v
   (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))))
  have h4:=Finset.card_insert_le v
   (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))
  omega
theorem wt (i : ℕ) : (4095 : ℕ).testBit i=decide (i < 12):=by
 have e : (4095 : ℕ)=2 ^ 12 - 1:=by norm_num
 rw [e,Nat.testBit_two_pow_sub_one]
theorem vt.sep {m : Bool} {D : Finset ℕ} {k : ℕ} (h : vt m D k) (e i : ℕ) (he : e < 12)
 (hi : 12 ≤ i) : ∃ w ∈ D,w.testBit e=true ∧ w.testBit i=false:=by
 induction h using vt.ind with
 | done k =>
  refine ⟨4095,by simp, ?_, ?_⟩
  · rw [wt];simpa using he
  · rw [wt];simpa using hi
 | step D k u v w ka kb hu hv hw hd hb _ ih =>
  obtain ⟨x,hx,h1,h2⟩:=ih
  rcases Finset.mem_insert.mp hx with hxw | hx
  · subst hxw
    rcases hw with hw | hw
    · subst hw
      rw [Nat.testBit_and] at h1 h2
      cases hum : u.testBit i
      · exact ⟨u,hu,by simp_all,hum⟩
      · exact ⟨v,hv,by simp_all,by simp_all⟩
    · subst hw
      rw [Nat.testBit_or] at h1 h2
      cases hue : u.testBit e
      · exact ⟨v,hv,by simp_all,by simp_all⟩
      · exact ⟨u,hu,hue,by simp_all⟩
  · exact ⟨x,Finset.mem_of_mem_filter _ hx,h1,h2⟩
def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)
theorem q9y (w e : ℕ) : tb w e=w.testBit e:=by
 have h : Nat.land (Nat.shiftRight w e) 1=1&&&(w>>>e):=Nat.and_comm _ _
 unfold tb Nat.testBit
 rw [h]
 generalize (1&&&w>>>e)=X
 cases X <;> rfl
def rect (x J : ℕ) : ℕ → ℕ
 | 0=>0
 | e+1=>Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)
def qD (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12
theorem qa7 (x J i : ℕ) (hJ : J.testBit i=true) : ∀ n e : ℕ,e < n → x.testBit e=true →
 (rect x J n).testBit (12*e+i)=true:=by
 intro n
 induction n with
 | zero=>intro e he;omega
 | succ n ih =>
  intro e he hx
  show ((cond (tb x n) (J<<<(12*n)) 0)|||rect x J n).testBit (12*e+i)=true
  rw [Nat.testBit_or]
  by_cases hen : e=n
  · subst hen
    rw [q9y,hx]
    simp [Nat.testBit_shiftLeft,hJ]
  · rw [ih e (by omega) hx]
    simp
theorem q4l (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e=true)
  (h2 : x.testBit (12+i)=false) : (qD x).testBit (12*e+i)=true:=by
 apply qa7 _ _ _ _ 12 e he h1
 show ((x>>>12)^^^4095).testBit i=true
 rw [Nat.testBit_xor,Nat.testBit_shiftRight,h2,wt]
 simp [hi]
theorem qa5 {m : Bool} {D : Finset ℕ} {k : ℕ} (hR : vt m D k) (p : ℕ) (hp : p < 144) :
  ∃ x ∈ D,(qD x).testBit p=true:=by
 obtain ⟨x,hx,h1,h2⟩:=hR.sep (p / 12) (12+p % 12) (by omega) (by omega)
 refine ⟨x,hx, ?_⟩
 have:=q4l x (p / 12) (p % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h1 h2
 rwa [Nat.div_add_mod] at this
def qp : ℕ := 22300745198530623141535718272648361505980415
theorem qab : qp=2 ^ 144 - 1:=by norm_num [qp]
def bor (a b : Bool) : Bool := @Bool.rec (fun _=>Bool) b true a
def q8v (a b : Bool) : Bool := @Bool.rec (fun _=>Bool) false b a
def qah (a : Bool) : Bool := @Bool.rec (fun _=>Bool) true false a
theorem q9k (a b : Bool) : q8v a b=(a&&b):=by cases a <;> rfl
theorem qag (a : Bool) : qah a = !a:=by cases a <;> rfl
def tb' (w e : ℕ) : Bool:=qah (Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)
theorem qak (w e : ℕ) : tb' w e=tb w e:=by
 unfold tb' tb;rw [qag]
def rect' (x J n : ℕ) : ℕ :=
 @Nat.rec (fun _ => ℕ) 0
  (fun e ih=>Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) ih) n
theorem q4o (x J n : ℕ) : rect' x J n=rect x J n:=by
 induction n with
 | zero=>rfl
 | succ e ih =>
  show Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) (rect' x J e) =
   Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)
  rw [ih,qak]
  cases tb x e <;> rfl
theorem q4m (x J n q : Nat) (bounded : J < 4096) :
 (rect x J n).testBit q =
  (decide (q / 12 < n)&&x.testBit (q / 12)&&J.testBit (q % 12)):=by
 induction n with
 | zero=>simp [rect]
 | succ n ih =>
  change ((cond (tb x n) (J<<<(12*n)) 0)|||rect x J n).testBit q=_
  rw [Nat.testBit_or,ih,q9y]
  by_cases before : q / 12 < n
  · have start : ¬ 12*n ≤ q:=by omega
    have next : q/12 < n+1:=by omega
    cases x.testBit n <;> simp [Nat.testBit_shiftLeft,start,before,next]
  by_cases lane : q / 12=n
  · have start : 12*n ≤ q:=by omega
    have off : q-12*n=q % 12:=by omega
    have next : q/12 < n+1:=by omega
    cases enabled : x.testBit n <;> simp [Nat.testBit_shiftLeft,start,off,before,next,lane,enabled]
  · have next : ¬ q/12 < n+1:=by omega
    have off : 12 ≤ q-12*n:=by omega
    have beyond : J.testBit (q-12*n)=false:=by
     apply Nat.testBit_lt_two_pow
     exact lt_of_lt_of_le bounded (Nat.pow_le_pow_right (by decide : 0 < 2) off)
    cases x.testBit n <;> simp [Nat.testBit_shiftLeft,before,next,beyond]
def q4n (p : Nat → Bool) : Nat → Nat → Bool :=
 Nat.rec p (fun k prev s=>prev s&&prev (s+2^k))
theorem q8f {p : Nat → Bool} {k s i : Nat}
 (h : q4n p k s=true) (lo : s ≤ i) (hi : i < s+2^k) : p i=true:=by
 induction k generalizing s with
 | zero =>
  have eq : i=s:=by omega
  simpa [eq,q4n] using h
 | succ k ih =>
  obtain ⟨left,right⟩:=Bool.and_eq_true_iff.mp h
  by_cases half : i < s+2^k
  · exact ih left lo half
  · apply ih right (by omega)
    rw [Nat.pow_succ] at hi
    omega
def kN (p : Nat) : Nat :=
 let table:=0xfffffffffffffffffffff000ffffff000fffffffff000000fff000fffffffff000fff000fff000000ffffff000000000000fffffffff000ffffff000000fff000fff000fff000000000000ffffff000000fff000000000000fff000000000000
 (z3 table 48 (p&&&15)) |||
  ((z3 table 48 ((p>>>4)&&&15))<<<48) |||
  ((z3 table 48 ((p>>>8)&&&15))<<<96)
def vu (J : Nat) : Nat:=J*0x1001001001001001001001001001001001
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14 :
  q4n (fun v=>Nat.beq (kN v) (rect' v 4095 12) &&
   Nat.beq (vu v) (rect' 4095 v 12)) 12 0=true:=by
 decide +kernel
theorem we {i : Nat} (h : i < 4096) :
  kN i=rect i 4095 12 ∧ vu i=rect 4095 i 12:=by
 have line:=q8f q14 (i:=i) (Nat.zero_le _) (by simpa using h)
 obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp line
 exact ⟨(Nat.beq_eq.mp a).trans (q4o ..),(Nat.beq_eq.mp b).trans (q4o ..)⟩
def qD' (x : Nat) : Nat :=
 let J:=(x>>>12)^^^4095
 if Nat.blt J 4096 then kN (x % 4096)&&&vu J
 else rect' x J 12
theorem qD'_eq (x : Nat) : qD' x=qD x:=by
 unfold qD' qD
 let J:=(x>>>12)^^^4095
 change (if Nat.blt J 4096 then kN (x % 4096)&&&vu J
  else rect' x J 12)=rect x J 12
 split
 · next good =>
   have small:=Nat.blt_eq.mp good
   have modSmall : x % 4096 < 4096:=Nat.mod_lt _ (by decide)
   rw [(we modSmall).1,(we small).2]
   apply Nat.eq_of_testBit_eq
   intro q
   rw [Nat.testBit_and,q4m _ _ _ _ (by decide),q4m _ _ _ _ small,
    q4m _ _ _ _ small,wt,wt]
   change (_&&(x % 2^12).testBit (q/12)&&_&&_)=_
   rw [Nat.testBit_mod_two_pow]
   have modLt : q % 12 < 12:=Nat.mod_lt _ (by decide)
   simp only [modLt,decide_true,Bool.and_true]
   cases decide (q/12 < 12) <;> rfl
 · exact q4o ..
theorem q8X {c : Prop} [Decidable c] (a b : ℕ) (h : c) : (if c then a else b)=a:=by
 split
 · rfl
 · contradiction
theorem q8Y {c : Prop} [Decidable c] (a b : ℕ) (h : ¬ c) : (if c then a else b)=b:=by
 split
 · contradiction
 · rfl
theorem q5Z {α : Type} {R : α → α → Prop} (hs : ∀ a b,R a b → R b a) :
 ∀ l : List α,l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l,a ≠ b → R a b:=by
 intro l
 induction l with
 | nil=>intro _ a ha;simp at ha
 | cons x l ih =>
  intro h a ha b hb hab
  rw [List.pairwise_cons] at h
  rcases List.mem_cons.mp ha with ha' | ha'
  · rcases List.mem_cons.mp hb with hb' | hb'
    · exact absurd (ha'.trans hb'.symm) hab
    · rw [ha'];exact h.1 b hb'
  · rcases List.mem_cons.mp hb with hb' | hb'
    · rw [hb'];exact hs _ _ (h.1 a ha')
    · exact ih h.2 a ha' b hb' hab
theorem q9z (D : Finset ℕ) (u v : ℕ) (ka kb : Bool) :
  D.card ≤ (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))).card +
   (cond ka 0 1+cond kb 0 1):=by
 have hsub : D ⊆ (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))) ∪
   ((cond ka ∅ {u}) ∪ (cond kb ∅ {v})):=by
  intro x hx
  by_cases h1 : x=u <;> by_cases h2 : x=v <;> cases ka <;> cases kb <;> simp_all
 have h1:=Finset.card_le_card hsub
 have h2:=Finset.card_union_le (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))
  ((cond ka ∅ {u}) ∪ (cond kb ∅ {v}))
 have h3:=Finset.card_union_le (cond ka (∅ : Finset ℕ) {u}) (cond kb ∅ {v})
 have h4 : (cond ka (∅ : Finset ℕ) {u}).card=cond ka 0 1:=by cases ka <;> simp
 have h5 : (cond kb (∅ : Finset ℕ) {v}).card=cond kb 0 1:=by cases kb <;> simp
 omega
theorem q7h (u v e i : ℕ) (h1 : (u&&&v).testBit e=true) (_h2 : (u&&&v).testBit i=false)
  (h3 : (!(u.testBit i))=true) : u.testBit e=true ∧ u.testBit i=false:=by
 rw [Nat.testBit_and] at h1
 cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem q7g (u v e i : ℕ) (h1 : (u&&&v).testBit e=true) (h2 : (u&&&v).testBit i=false)
  (h3 : (!(u.testBit i))=false) : v.testBit e=true ∧ v.testBit i=false:=by
 rw [Nat.testBit_and] at h1 h2
 cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem q8U (u v e i : ℕ) (_h1 : (u|||v).testBit e=true) (h2 : (u|||v).testBit i=false)
  (h3 : u.testBit e=true) : u.testBit e=true ∧ u.testBit i=false:=by
 rw [Nat.testBit_or] at h2
 cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem q8T (u v e i : ℕ) (h1 : (u|||v).testBit e=true) (h2 : (u|||v).testBit i=false)
  (h3 : u.testBit e=false) : v.testBit e=true ∧ v.testBit i=false:=by
 rw [Nat.testBit_or] at h1 h2
 cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem qM (a b q : ℕ) : (Nat.land a b).testBit q=(a.testBit q&&b.testBit q) :=
 Nat.testBit_and a b q
theorem qX (a b q : ℕ) : (Nat.lor a b).testBit q=(a.testBit q||b.testBit q) :=
 Nat.testBit_or a b q
theorem j7 (a b q : ℕ) : (Nat.xor a b).testBit q=Bool.xor (a.testBit q) (b.testBit q) :=
 Nat.testBit_xor a b q
theorem jZ (q : ℕ) : qp.testBit q=decide (q < 144):=by
 rw [qab,Nat.testBit_two_pow_sub_one]
theorem q0B (h a : ℕ) (H : ∀ q,h.testBit q=true → a.testBit q=true) :
 Nat.land h a=h:=by
 apply Nat.eq_of_testBit_eq
 intro q
 rw [qM]
 cases hh : h.testBit q
 · rfl
 · rw [H q hh];rfl
theorem kO (a h : ℕ) (H : ∀ q,a.testBit q=true → h.testBit q=true → False) :
 Nat.land a h=0:=by
 apply Nat.eq_of_testBit_eq
 intro q
 rw [qM,Nat.zero_testBit]
 cases ha : a.testBit q
 · rfl
 · cases hh : h.testBit q
   · rfl
   · exact (H q ha hh).elim
def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)
def q2e (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)
theorem q9E (x s q : ℕ) : (orS x s).testBit q=(x.testBit q||x.testBit (s+q)):=by
 show (x|||x>>>s).testBit q=_
 rw [Nat.testBit_or,Nat.testBit_shiftRight]
theorem q8V (x s q : ℕ) :
  (q2e x s).testBit q=(x.testBit q||(decide (s ≤ q)&&x.testBit (q - s))):=by
 show (x|||x<<<s).testBit q=_
 simp only [Nat.testBit_or,Nat.testBit_shiftLeft,ge_iff_le]
theorem q0z (k p x n s : ℕ)
 (hx : ∀ q,x.testBit q=true → ∃ j,j < n ∧ p.testBit (k*j+q)=true) (q : ℕ)
 (h : (orS x (k*s)).testBit q=true) : ∃ j,j < n+s ∧ p.testBit (k*j+q)=true:=by
 rw [q9E,Bool.or_eq_true] at h
 rcases h with h | h
 · obtain ⟨j,hj,hp⟩:=hx q h
   exact ⟨j,by omega,hp⟩
 · obtain ⟨j,hj,hp⟩:=hx _ h
   refine ⟨j+s,by omega, ?_⟩
   rw [Nat.mul_add,Nat.add_assoc];exact hp
theorem uT (k p x n s : ℕ)
 (hx : ∀ q,x.testBit q=true → ∃ j,j < n ∧ k*j ≤ q ∧ p.testBit (q - k*j)=true)
 (q : ℕ) (h : (q2e x (k*s)).testBit q=true) :
 ∃ j,j < n+s ∧ k*j ≤ q ∧ p.testBit (q - k*j)=true:=by
 rw [q8V,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
 rcases h with h | ⟨hs,h⟩
 · obtain ⟨j,hj,hq,hp⟩:=hx q h
   exact ⟨j,by omega,hq,hp⟩
 · obtain ⟨j,hj,hq,hp⟩:=hx _ h
   have e : q - k*(j+s)=q - k*s - k*j:=by rw [Nat.mul_add];omega
   refine ⟨j+s,by omega, ?_, ?_⟩
   · rw [Nat.mul_add];omega
   · rw [e];exact hp
def q6G : ℕ := 5445847423328601499764522166702896582657
theorem qa6 (q : ℕ) (h : q6G.testBit q=true) : q < 144 ∧ q % 12=0:=by
 have hlt : q < 144:=by
  by_contra hq
  have h0 : q6G.testBit q=false:=by
   apply Nat.testBit_lt_two_pow
   have h1 : q6G < 2 ^ 144:=by norm_num [q6G]
   have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q:=Nat.pow_le_pow_right (by norm_num) (by omega)
   omega
  rw [h0] at h
  exact Bool.noConfusion h
 have hall : ∀ q : ℕ,q < 144 → q6G.testBit q=true → q % 12=0:=by decide +kernel
 exact ⟨hlt,hall q hlt h⟩
def vZ (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) q6G
def ua (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095
def q0a (p : ℕ) : ℕ :=
 Nat.land (q2e (q2e (q2e (q2e (vZ p) 6) 3) 1) 1)
  (q2e (q2e (q2e (q2e (ua p) 96) 48) 24) 12)
def vN (p : ℕ) : ℕ := q0a (Nat.land p qp)
theorem q9m (p q : ℕ) (h : (vZ p).testBit q=true) :
  (q < 144 ∧ q % 12=0) ∧ ∃ j,j < 12 ∧ p.testBit (j+q)=true:=by
 unfold vZ at h
 rw [qM,Bool.and_eq_true] at h
 refine ⟨qa6 q h.2, ?_⟩
 have h0 : ∀ q,p.testBit q=true → ∃ j,j < 1 ∧ p.testBit (1*j+q)=true :=
  fun q hq=>⟨0,by norm_num,by simpa using hq⟩
 have h1:=q0z 1 p _ 1 6 h0
 have h2:=q0z 1 p _ _ 3 h1
 have h3:=q0z 1 p _ _ 1 h2
 have h4:=q0z 1 p _ _ 1 h3
 obtain ⟨j,hj,hp⟩:=h4 q h.1
 exact ⟨j,by omega,by simpa using hp⟩
theorem q9x (p q : ℕ) (h : (ua p).testBit q=true) :
  q < 12 ∧ ∃ j,j < 16 ∧ p.testBit (12*j+q)=true:=by
 unfold ua at h
 rw [qM,Bool.and_eq_true,wt,decide_eq_true_eq] at h
 refine ⟨h.2, ?_⟩
 have h0 : ∀ q,p.testBit q=true → ∃ j,j < 1 ∧ p.testBit (12*j+q)=true :=
  fun q hq=>⟨0,by norm_num,by simpa using hq⟩
 have h1:=q0z 12 p _ 1 8 h0
 have h2:=q0z 12 p _ _ 4 h1
 have h3:=q0z 12 p _ _ 2 h2
 have h4:=q0z 12 p _ _ 1 h3
 obtain ⟨j,hj,hp⟩:=h4 q h.1
 exact ⟨j,by omega,hp⟩
theorem q8n (p : ℕ) (hp : ∀ q,p.testBit q=true → q < 144) (q : ℕ)
  (h : (q0a p).testBit q=true) :
  q < 144 ∧ ∃ i e',i < 12 ∧ e' < 12 ∧ p.testBit (12*(q / 12)+i)=true ∧
   p.testBit (12*e'+q % 12)=true:=by
 unfold q0a at h
 rw [qM,Bool.and_eq_true] at h
 obtain ⟨hR,hC⟩:=h
 have r0 : ∀ q,(vZ p).testBit q=true →
   ∃ j,j < 1 ∧ 1*j ≤ q ∧ (vZ p).testBit (q - 1*j)=true :=
  fun q hq=>⟨0,by norm_num,by omega,by simpa using hq⟩
 have r1:=uT 1 (vZ p) _ 1 6 r0
 have r2:=uT 1 (vZ p) _ _ 3 r1
 have r3:=uT 1 (vZ p) _ _ 1 r2
 have r4:=uT 1 (vZ p) _ _ 1 r3
 obtain ⟨j,hj,hjq,hr⟩:=r4 q hR
 obtain ⟨⟨hb,hm⟩,i,hi,hpi⟩:=q9m p _ hr
 have c0 : ∀ q,(ua p).testBit q=true →
   ∃ j,j < 1 ∧ 12*j ≤ q ∧ (ua p).testBit (q - 12*j)=true :=
  fun q hq=>⟨0,by norm_num,by omega,by simpa using hq⟩
 have c1:=uT 12 (ua p) _ 1 8 c0
 have c2:=uT 12 (ua p) _ _ 4 c1
 have c3:=uT 12 (ua p) _ _ 2 c2
 have c4:=uT 12 (ua p) _ _ 1 c3
 obtain ⟨j',hj',hjq',hc⟩:=c4 q hC
 obtain ⟨hlt,e',he',hpe⟩:=q9x p _ hc
 have e1 : i+(q - 1*j)=12*(q / 12)+i:=by omega
 have e2 : q - 12*j'=q % 12:=by omega
 rw [e1] at hpi
 rw [e2] at hpe
 have hb':=hp _ hpe
 exact ⟨by omega,i,e',hi,by omega,hpi,hpe⟩
theorem wh (p q : ℕ) (h : (vN p).testBit q=true) :
  q < 144 ∧ ∃ i e',i < 12 ∧ e' < 12 ∧ p.testBit (12*(q / 12)+i)=true ∧
   p.testBit (12*e'+q % 12)=true:=by
 have hp : ∀ q,(Nat.land p qp).testBit q=true → q < 144:=by
  intro q hq
  rw [qM,jZ,Bool.and_eq_true,decide_eq_true_eq] at hq
  exact hq.2
 obtain ⟨h1,i,e',hi,he,ha,hb⟩:=q8n _ hp q h
 rw [qM,Bool.and_eq_true] at ha hb
 exact ⟨h1,i,e',hi,he,ha.1,hb.1⟩
def tw : List ℕ → ℕ → ℕ → ℕ
 | [],_,t=>t
 | a :: l,o,t=>tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))
def ya (t a : ℕ) : ℕ := vN (Nat.land a (Nat.xor t qp))
def vg (t : ℕ) : List ℕ → ℕ → Bool
 | [],_=>true
 | a :: l,acc=>Nat.beq (Nat.land (ya t a) a) (ya t a) &&
  (Nat.beq (Nat.land acc (ya t a)) 0&&vg t l (Nat.lor acc (ya t a)))
def qa4 (as : List ℕ) : Bool:=vg (tw as 0 0) as 0
def q21 (l : List ℕ) : Bool:=qa4 (l.map qD)
def q1R (R : ℕ → Prop) : Prop :=
 ∀ e i e' i' : ℕ,e < 12 → i < 12 → e' < 12 → i' < 12 →
  R (12*e+i) → R (12*e'+i') → R (12*e+i')
def q58 (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
 (∀ z ∈ zs,q1R z.1) ∧
 (∀ z ∈ zs, ∀ q,z.1 q → q < 144) ∧
 (zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False)) ∧
 (∀ q,q < 144 → ∃ z ∈ zs,z.1 q) ∧
 (∀ z ∈ zs, ∀ q,z.1 q → z.2.testBit q=true)
theorem q58.rect {zs : List ((ℕ → Prop) × ℕ)} (h : q58 zs) :
 ∀ z ∈ zs,q1R z.1:=h.1
theorem q58.disj {zs : List ((ℕ → Prop) × ℕ)} (h : q58 zs) :
 zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False):=h.2.2.1
theorem q58.cov {zs : List ((ℕ → Prop) × ℕ)} (h : q58 zs) :
 ∀ q,q < 144 → ∃ z ∈ zs,z.1 q:=h.2.2.2.1
theorem q58.sub {zs : List ((ℕ → Prop) × ℕ)} (h : q58 zs) :
 ∀ z ∈ zs, ∀ q,z.1 q → z.2.testBit q=true:=h.2.2.2.2
theorem q40 (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ),(tw as o t).testBit q=false →
 t.testBit q=false ∧ (o.testBit q=true → ∀ a ∈ as,a.testBit q=false) ∧
 as.Pairwise (fun a b => ¬ (a.testBit q=true ∧ b.testBit q=true)):=by
 intro as
 induction as with
 | nil=>intro o t h;exact ⟨h,fun _ a ha=>by simp at ha,List.Pairwise.nil⟩
 | cons a l ih =>
  intro o t h
  obtain ⟨h1,h2,h3⟩:=ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
  rw [qX,Bool.or_eq_false_iff,qM] at h1
  refine ⟨h1.1, ?_, ?_⟩
  · intro ho b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have h4:=h1.2
      rw [ho] at h4
      simpa using h4
    · exact h2 (by rw [qX,ho];rfl) b hb
  · refine List.pairwise_cons.mpr ⟨?_,h3⟩
    intro b hb hab
    have h4:=h2 (by rw [qX,hab.1];simp) b hb
    rw [h4] at hab
    exact Bool.noConfusion hab.2
theorem qa8 {zs : List ((ℕ → Prop) × ℕ)} (hP : q58 zs) : ∀ z ∈ zs, ∀ q,
 (ya (tw (zs.map Prod.snd) 0 0) z.2).testBit q=true → z.1 q:=by
 intro z hz q hq
 obtain ⟨hq144,i,e',hi,he',ha,hb⟩:=wh _ q hq
 have key : ∀ x,x < 144 →
  (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) qp)).testBit x=true → z.1 x:=by
  intro x hx hbit
  rw [qM,j7,jZ,Bool.and_eq_true] at hbit
  obtain ⟨hzx,ht⟩:=hbit
  have ht' : (tw (zs.map Prod.snd) 0 0).testBit x=false:=by simpa [hx] using ht
  obtain ⟨_,_,hpw⟩:=q40 x _ 0 0 ht'
  rw [List.pairwise_map] at hpw
  obtain ⟨z',hz',hzq⟩:=hP.cov x hx
  by_cases hzz : z'=z
  · rw [← hzz];exact hzq
  · exfalso
    exact q5Z (fun a b h h'=>h ⟨h'.2,h'.1⟩) zs hpw z' hz' z hz hzz
     ⟨hP.sub z' hz' x hzq,hzx⟩
 have h1:=key _ (by omega) ha
 have h2:=key _ (by omega) hb
 have h3:=hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
  h1 h2
 rwa [Nat.div_add_mod] at h3
theorem q5F (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
 (∀ z ∈ zs, ∀ q,(ya t z.2).testBit q=true → z.1 q) →
 (∀ z ∈ zs, ∀ q,z.1 q → z.2.testBit q=true) →
 zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False) →
 (∀ q,acc.testBit q=true → ∀ z ∈ zs, ¬ z.1 q) →
 vg t (zs.map Prod.snd) acc=true:=by
 intro zs
 induction zs with
 | nil=>intros;rfl
 | cons z zs ih =>
  intro acc hh hs hd ha
  rw [List.pairwise_cons] at hd
  have hz:=hh z List.mem_cons_self
  have e1:=q0B _ _ (fun q hq=>hs z List.mem_cons_self q (hz q hq))
  have e2:=kO acc (ya t z.2) (fun q h1 h2=>ha q h1 z List.mem_cons_self (hz q h2))
  have e3:=ih (Nat.lor acc (ya t z.2)) (fun z' hz'=>hh z' (List.mem_cons_of_mem _ hz'))
   (fun z' hz'=>hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q=>by
    rw [qX,Bool.or_eq_true] at hq
    rcases hq with hq | hq
    · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
    · exact hd.1 z' hz' q (hz q hq) hz'q)
  show (Nat.beq (Nat.land (ya t z.2) z.2) (ya t z.2) &&
   (Nat.beq (Nat.land acc (ya t z.2)) 0 &&
    vg t (zs.map Prod.snd) (Nat.lor acc (ya t z.2))))=true
  rw [e1,e2,e3,Nat.beq_refl]
  rfl
theorem q7Y {zs : List ((ℕ → Prop) × ℕ)} (hP : q58 zs) :
  qa4 (zs.map Prod.snd)=true :=
 q5F _ zs 0 (qa8 hP) hP.sub hP.disj (fun q hq=>by simp at hq)
def tw' (l : List ℕ) : ℕ → ℕ → ℕ :=
 @List.rec ℕ (fun _ => ℕ → ℕ → ℕ) (fun _ t=>t)
  (fun a _ ih o t=>ih (Nat.lor o a) (Nat.lor t (Nat.land o a))) l
theorem q4k (l : List ℕ) : ∀ o t : ℕ,tw' l o t=tw l o t:=by
 induction l with
 | nil=>intro o t;rfl
 | cons a l ih =>
  intro o t
  show tw' l (Nat.lor o a) (Nat.lor t (Nat.land o a))=tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))
  exact ih _ _
def vg' (t : ℕ) (l : List ℕ) : ℕ → Bool :=
 @List.rec ℕ (fun _ => ℕ → Bool) (fun _=>true)
  (fun a _ ih acc=>(fun h=>q8v (Nat.beq (Nat.land h a) h)
   (q8v (Nat.beq (Nat.land acc h) 0) (ih (Nat.lor acc h)))) (ya t a)) l
theorem vg'_eq (t : ℕ) (l : List ℕ) : ∀ acc : ℕ,vg' t l acc=vg t l acc:=by
 induction l with
 | nil=>intro acc;rfl
 | cons a l ih =>
  intro acc
  show q8v (Nat.beq (Nat.land (ya t a) a) (ya t a))
   (q8v (Nat.beq (Nat.land acc (ya t a)) 0) (vg' t l (Nat.lor acc (ya t a)))) =
   (Nat.beq (Nat.land (ya t a) a) (ya t a) &&
    (Nat.beq (Nat.land acc (ya t a)) 0&&vg t l (Nat.lor acc (ya t a))))
  rw [ih,q9k,q9k]
def q8i' (l : List ℕ) : List ℕ :=
 @List.rec ℕ (fun _=>List ℕ) [] (fun x _ ih=>qD' x :: ih) l
theorem q0A (l : List ℕ) : q8i' l=l.map qD:=by
 induction l with
 | nil=>rfl
 | cons x l ih =>
  show qD' x :: q8i' l=qD x :: l.map qD
  rw [ih,qD'_eq]
def Pc (x e i : ℕ) : Prop:=x.testBit e=true ∧ x.testBit i=false
def q12 (S : ℕ → ℕ → Prop) : Prop := ∀ e i e' i' : ℕ,S e i → S e' i' → S e i'
theorem q6J (x : ℕ) : q12 (Pc x):=fun _ _ _ _ h1 h2=>⟨h1.1,h2.2⟩
def KS (D : Finset ℕ) (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ)
  (Pi : ℕ → ℕ → ℕ → Prop) : Prop :=
 (∀ e i,e < 12 → 12 ≤ i → f e i ∈ D ∧ env (f e i) e i) ∧
 (∀ x ∈ D,q12 (env x)) ∧
 (∀ x ∈ D, ∀ e i,env x e i → Pc x e i) ∧
 (∀ x ∈ D, ∀ y ∈ D,x ≠ y → c x=c y → ∀ e i,env x e i → env y e i → False) ∧
 (∀ x ∈ D,1 ≤ c x → ∀ e i,env x e i → Pi (c x) e i) ∧
 (∀ n,q12 (Pi n)) ∧
 (∀ n e i,1 ≤ n → Pi n e i → ∃ y ∈ D,1 ≤ c y ∧ c y ≤ n ∧ Pc y e i) ∧
 (∀ x ∈ D,c x ≤ j)
theorem KS.own {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
 ∀ e i,e < 12 → 12 ≤ i → f e i ∈ D ∧ env (f e i) e i:=h.1
theorem KS.envR {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
 ∀ x ∈ D,q12 (env x):=h.2.1
theorem KS.envP {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
 ∀ x ∈ D, ∀ e i,env x e i → Pc x e i:=h.2.2.1
theorem KS.s1 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
 ∀ x ∈ D, ∀ y ∈ D,x ≠ y → c x=c y → ∀ e i,env x e i → env y e i → False:=h.2.2.2.1
theorem KS.s2 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
 ∀ x ∈ D,1 ≤ c x → ∀ e i,env x e i → Pi (c x) e i:=h.2.2.2.2.1
theorem KS.piR {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
 ∀ n,q12 (Pi n):=h.2.2.2.2.2.1
theorem KS.s3 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
 ∀ n e i,1 ≤ n → Pi n e i → ∃ y ∈ D,1 ≤ c y ∧ c y ≤ n ∧ Pc y e i:=h.2.2.2.2.2.2.1
theorem KS.lab {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
 ∀ x ∈ D,c x ≤ j:=h.2.2.2.2.2.2.2
theorem qaa : KS {4095} 0 (fun _ _=>4095) (fun _ e i=>Pc 4095 e i) (fun _=>0)
 (fun _ _ _=>False):=by
 refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 · intro e i he hi
   refine ⟨by simp, ?_, ?_⟩
   · rw [wt];simpa using he
   · rw [wt];simpa using hi
 · intro x _;exact q6J 4095
 · intro x hx e i h
   rw [Finset.mem_singleton.mp hx];exact h
 · intro x hx y hy hxy
   exact absurd ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm) hxy
 · intro x _ h;simp at h
 · intro n e i e' i' h;exact h.elim
 · intro n e i _ h;exact h.elim
 · intro x _;exact le_rfl
def q0m (c : ℕ → ℕ) (x y : ℕ) : ℕ := if y=x then 1 else if c y=0 then 0 else c y+1
theorem yv (c : ℕ → ℕ) (x : ℕ) : q0m c x x=1:=by
 unfold q0m;exact q8X _ _ rfl
theorem jp (c : ℕ → ℕ) (x y : ℕ) (h : y ≠ x) :
 (c y=0 ∧ q0m c x y=0) ∨ (1 ≤ c y ∧ q0m c x y=c y+1):=by
 unfold q0m
 rw [q8Y _ _ h]
 by_cases h0 : c y=0
 · rw [q8X _ _ h0];exact Or.inl ⟨h0,rfl⟩
 · rw [q8Y _ _ h0];exact Or.inr ⟨by omega,rfl⟩
theorem KS.promote {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) (x : ℕ) (hxD : x ∈ D) :
 KS D (j+1) f (fun y e i=>(y=x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (q0m c x)
  (fun n e i=>(n=1 ∧ Pc x e i) ∨ (2 ≤ n ∧ Pi (n - 1) e i)):=by
 refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 · intro e i he hi
   obtain ⟨h1,h2⟩:=h.own e i he hi
   refine ⟨h1, ?_⟩
   by_cases hx : f e i=x
   · exact Or.inl ⟨hx,hx ▸ h.envP _ h1 e i h2⟩
   · exact Or.inr ⟨hx,h2⟩
 · intro y hy e i e' i' h1 h2
   rcases h1 with ⟨hx,h1⟩ | ⟨hx,h1⟩ <;> rcases h2 with ⟨hx',h2⟩ | ⟨hx',h2⟩
   · exact Or.inl ⟨hx,q6J x e i e' i' h1 h2⟩
   · exact absurd hx hx'
   · exact absurd hx' hx
   · exact Or.inr ⟨hx,h.envR y hy e i e' i' h1 h2⟩
 · intro y hy e i h1
   rcases h1 with ⟨hx,h1⟩ | ⟨hx,h1⟩
   · rw [hx];exact h1
   · exact h.envP y hy e i h1
 · intro y hy z hz hyz hc e i h1 h2
   by_cases hyx : y=x
   · have hzx : z ≠ x:=fun hh=>hyz (hyx.trans hh.symm)
     rw [hyx,yv] at hc
     rcases jp c x z hzx with ⟨_,h3⟩ | ⟨_,h3⟩ <;> omega
   · by_cases hzx : z=x
     · rw [hzx,yv] at hc
       rcases jp c x y hyx with ⟨_,h3⟩ | ⟨_,h3⟩ <;> omega
     · have hcc : c y=c z:=by
        rcases jp c x y hyx with ⟨_,h3⟩ | ⟨_,h3⟩ <;>
         rcases jp c x z hzx with ⟨_,h4⟩ | ⟨_,h4⟩ <;> omega
       rcases h1 with ⟨hx,_⟩ | ⟨_,h1⟩
       · exact hyx hx
       · rcases h2 with ⟨hx,_⟩ | ⟨_,h2⟩
         · exact hzx hx
         · exact h.s1 y hy z hz hyz hcc e i h1 h2
 · intro y hy hc e i h1
   rcases h1 with ⟨hx,h1⟩ | ⟨hx,h1⟩
   · rw [hx,yv];exact Or.inl ⟨rfl,h1⟩
   · rcases jp c x y hx with ⟨_,h3⟩ | ⟨h4,h3⟩
     · omega
     · rw [h3]
       refine Or.inr ⟨by omega, ?_⟩
       rw [Nat.add_sub_cancel]
       exact h.s2 y hy h4 e i h1
 · intro n e i e' i' h1 h2
   rcases h1 with ⟨hn,h1⟩ | ⟨hn,h1⟩ <;> rcases h2 with ⟨hn',h2⟩ | ⟨hn',h2⟩
   · exact Or.inl ⟨hn,q6J x e i e' i' h1 h2⟩
   · omega
   · omega
   · exact Or.inr ⟨hn,h.piR _ e i e' i' h1 h2⟩
 · intro n e i hn h1
   rcases h1 with ⟨hn1,h1⟩ | ⟨hn2,h1⟩
   · exact ⟨x,hxD,by rw [yv],by rw [yv];omega,h1⟩
   · obtain ⟨y,hy,h3,h4,h5⟩:=h.s3 (n - 1) e i (by omega) h1
     by_cases hyx : y=x
     · exact ⟨y,hy,by rw [hyx,yv],by rw [hyx,yv];omega,h5⟩
     · rcases jp c x y hyx with ⟨_,h6⟩ | ⟨_,h6⟩
       · omega
       · exact ⟨y,hy,by omega,by omega,h5⟩
 · intro y hy
   have:=h.lab y hy
   by_cases hyx : y=x
   · rw [hyx,yv];omega
   · rcases jp c x y hyx with ⟨_,h6⟩ | ⟨_,h6⟩ <;> omega
def q8w (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) : Prop :=
 (∀ e i,Pc x e i → env x e i) ∧ 1 ≤ c x ∧ (1 ≤ c w → c x ≤ c w)
theorem q0W (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) :
  q8w (fun y e i=>(y=x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (q0m c x) w x:=by
 refine ⟨fun e i h=>Or.inl ⟨rfl,h⟩,by rw [yv],fun h=>by rw [yv];exact h⟩
theorem q8g (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x y : ℕ) (hyx : y ≠ x) (hwx : w ≠ x)
 (h : q8w env c w y) :
 q8w (fun y e i=>(y=x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (q0m c x) w y:=by
 obtain ⟨h1,h2,h3⟩:=h
 refine ⟨fun e i hp=>Or.inr ⟨hyx,h1 e i hp⟩, ?_, ?_⟩
 · rcases jp c x y hyx with ⟨_,h6⟩ | ⟨_,h6⟩ <;> omega
 · intro hw
   rcases jp c x y hyx with ⟨_,h6⟩ | ⟨_,h6⟩ <;>
    rcases jp c x w hwx with ⟨_,h7⟩ | ⟨_,h7⟩ <;> omega
theorem qa9 {D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (hK : KS D' j f env c Pi) (u v w : ℕ) (_huw : u ≠ w) (hvw : v ≠ w)
 (huv : u ≠ v) (ka kb : Bool) (hua : u ∈ D' ↔ ka=true) (hvb : v ∈ D' ↔ kb=true) :
 ∃ (j2 : ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ) (Pi2 : ℕ → ℕ → ℕ → Prop),
  KS D' j2 f env2 c2 Pi2 ∧ j2=j+(cond ka 1 0+cond kb 1 0) ∧
  (u ∈ D' → q8w env2 c2 w u) ∧ (v ∈ D' → q8w env2 c2 w v):=by
 cases ka <;> cases kb
 · exact ⟨j,env,c,Pi,hK,rfl,fun h=>Bool.noConfusion (hua.mp h),
    fun h=>Bool.noConfusion (hvb.mp h)⟩
 · exact ⟨_,_,_,_,hK.promote v (hvb.mpr rfl),rfl,fun h=>Bool.noConfusion (hua.mp h),
    fun _=>q0W env c w v⟩
 · exact ⟨_,_,_,_,hK.promote u (hua.mpr rfl),rfl,fun _=>q0W env c w u,
    fun h=>Bool.noConfusion (hvb.mp h)⟩
 · exact ⟨_,_,_,_,(hK.promote u (hua.mpr rfl)).promote v (hvb.mpr rfl),rfl,
    fun _=>q8g _ _ w v u huv (Ne.symm hvw) (q0W env c w u),
    fun _=>q0W _ _ w v⟩
theorem KS.step {D D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D' j f env c Pi) (u v w : ℕ) (hu : u ∈ D) (hv : v ∈ D)
 (huv : u ≠ v) (hwD : w ∉ D) (hw : w ∈ D') (hD' : ∀ x ∈ D',x ≠ w → x ∈ D)
 (cc : ℕ → ℕ → Bool)
 (hcu : ∀ e i,Pc w e i → cc e i=true → Pc u e i)
 (hcv : ∀ e i,Pc w e i → cc e i=false → Pc v e i)
 (hcr : ∀ (b : Bool) (e i e' i' : ℕ),cc e i=b → cc e' i'=b → cc e i'=b)
 (hku : u ∈ D' → q8w env c w u) (hkv : v ∈ D' → q8w env c w v) :
 ∃ (f2 : ℕ → ℕ → ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ),KS D j f2 env2 c2 Pi:=by
 have hc2a : ∀ x,x ∈ D' → (if x ∈ D' then c x else c w)=c x:=fun x hx=>q8X _ _ hx
 have hc2b : ∀ x,x ∉ D' → (if x ∈ D' then c x else c w)=c w:=fun x hx=>q8Y _ _ hx
 refine ⟨fun e i=>if f e i=w then cond (cc e i) u v else f e i,
  fun x e i=>(x ∈ D' ∧ env x e i) ∨
   (x ∉ D' ∧ env w e i ∧ ((x=u ∧ cc e i=true) ∨ (x=v ∧ cc e i=false))),
  fun x=>if x ∈ D' then c x else c w, ?_⟩
 refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 · intro e i he hi
   obtain ⟨h1,h2⟩:=h.own e i he hi
   show (if f e i=w then cond (cc e i) u v else f e i) ∈ D ∧
    (((if f e i=w then cond (cc e i) u v else f e i) ∈ D' ∧
     env (if f e i=w then cond (cc e i) u v else f e i) e i) ∨
    ((if f e i=w then cond (cc e i) u v else f e i) ∉ D' ∧ env w e i ∧
     (((if f e i=w then cond (cc e i) u v else f e i)=u ∧ cc e i=true) ∨
      ((if f e i=w then cond (cc e i) u v else f e i)=v ∧ cc e i=false))))
   by_cases hfw : f e i=w
   · rw [q8X _ _ hfw]
     rw [hfw] at h2
     have hpw:=h.envP w hw e i h2
     cases hcc : cc e i
     · refine ⟨hv, ?_⟩
       by_cases hvD : v ∈ D'
       · exact Or.inl ⟨hvD,(hkv hvD).1 e i (hcv e i hpw hcc)⟩
       · exact Or.inr ⟨hvD,h2,Or.inr ⟨rfl,rfl⟩⟩
     · refine ⟨hu, ?_⟩
       by_cases huD : u ∈ D'
       · exact Or.inl ⟨huD,(hku huD).1 e i (hcu e i hpw hcc)⟩
       · exact Or.inr ⟨huD,h2,Or.inl ⟨rfl,rfl⟩⟩
   · rw [q8Y _ _ hfw]
     exact ⟨hD' _ h1 hfw,Or.inl ⟨h1,h2⟩⟩
 · intro x _ e i e' i' h1 h2
   rcases h1 with ⟨hx,h1⟩ | ⟨hx,h1,h1c⟩ <;> rcases h2 with ⟨hx',h2⟩ | ⟨hx',h2,h2c⟩
   · exact Or.inl ⟨hx,h.envR x hx e i e' i' h1 h2⟩
   · exact absurd hx hx'
   · exact absurd hx' hx
   · refine Or.inr ⟨hx,h.envR w hw e i e' i' h1 h2, ?_⟩
     rcases h1c with ⟨hxu,hc1⟩ | ⟨hxv,hc1⟩ <;> rcases h2c with ⟨hxu',hc2⟩ | ⟨hxv',hc2⟩
     · exact Or.inl ⟨hxu,hcr true e i e' i' hc1 hc2⟩
     · exact absurd (hxu.symm.trans hxv') huv
     · exact absurd (hxu'.symm.trans hxv) huv
     · exact Or.inr ⟨hxv,hcr false e i e' i' hc1 hc2⟩
 · intro x _ e i h1
   rcases h1 with ⟨hx,h1⟩ | ⟨_,h1,h1c⟩
   · exact h.envP x hx e i h1
   · have hpw:=h.envP w hw e i h1
     rcases h1c with ⟨hxu,hc1⟩ | ⟨hxv,hc1⟩
     · rw [hxu];exact hcu e i hpw hc1
     · rw [hxv];exact hcv e i hpw hc1
 · intro x hx y hy hxy hc e i h1 h2
   have hxw : x ≠ w:=fun hh=>hwD (hh ▸ hx)
   have hyw : y ≠ w:=fun hh=>hwD (hh ▸ hy)
   have hc' : (if x ∈ D' then c x else c w)=(if y ∈ D' then c y else c w):=hc
   rcases h1 with ⟨hx',h1⟩ | ⟨hx',h1,h1c⟩ <;> rcases h2 with ⟨hy',h2⟩ | ⟨hy',h2,h2c⟩
   · rw [hc2a x hx',hc2a y hy'] at hc'
     exact h.s1 x hx' y hy' hxy hc' e i h1 h2
   · rw [hc2a x hx',hc2b y hy'] at hc'
     exact h.s1 x hx' w hw hxw hc' e i h1 h2
   · rw [hc2b x hx',hc2a y hy'] at hc'
     exact h.s1 w hw y hy' (Ne.symm hyw) hc' e i h1 h2
   · rcases h1c with ⟨hxu,hc1⟩ | ⟨hxv,hc1⟩ <;> rcases h2c with ⟨hyu,hc2⟩ | ⟨hyv,hc2⟩
     · exact hxy (hxu.trans hyu.symm)
     · rw [hc1] at hc2;exact Bool.noConfusion hc2
     · rw [hc1] at hc2;exact Bool.noConfusion hc2
     · exact hxy (hxv.trans hyv.symm)
 · intro x _ hc e i h1
   have hc' : 1 ≤ (if x ∈ D' then c x else c w):=hc
   show Pi (if x ∈ D' then c x else c w) e i
   rcases h1 with ⟨hx',h1⟩ | ⟨hx',h1,_⟩
   · rw [hc2a x hx'] at hc' ⊢
     exact h.s2 x hx' hc' e i h1
   · rw [hc2b x hx'] at hc' ⊢
     exact h.s2 w hw hc' e i h1
 · exact h.piR
 · intro n e i hn h1
   obtain ⟨y,hy,h3,h4,h5⟩:=h.s3 n e i hn h1
   show ∃ y ∈ D,1 ≤ (if y ∈ D' then c y else c w) ∧ (if y ∈ D' then c y else c w) ≤ n ∧ Pc y e i
   by_cases hyw : y=w
   · rw [hyw] at h3 h4 h5
     cases hcc : cc e i
     · refine ⟨v,hv, ?_, ?_,hcv e i h5 hcc⟩
       · by_cases hvD : v ∈ D'
         · rw [hc2a v hvD];exact (hkv hvD).2.1
         · rw [hc2b v hvD];exact h3
       · by_cases hvD : v ∈ D'
         · rw [hc2a v hvD];exact le_trans ((hkv hvD).2.2 h3) h4
         · rw [hc2b v hvD];exact h4
     · refine ⟨u,hu, ?_, ?_,hcu e i h5 hcc⟩
       · by_cases huD : u ∈ D'
         · rw [hc2a u huD];exact (hku huD).2.1
         · rw [hc2b u huD];exact h3
       · by_cases huD : u ∈ D'
         · rw [hc2a u huD];exact le_trans ((hku huD).2.2 h3) h4
         · rw [hc2b u huD];exact h4
   · exact ⟨y,hD' y hy hyw,by rw [hc2a y hy];exact h3,by rw [hc2a y hy];exact h4,h5⟩
 · intro x _
   show (if x ∈ D' then c x else c w) ≤ j
   by_cases hx' : x ∈ D'
   · rw [hc2a x hx'];exact h.lab x hx'
   · rw [hc2b x hx'];exact h.lab w hw
theorem q7S (b : Bool) : (cond b 1 0 : ℕ)+cond b 0 1=1:=by cases b <;> rfl
theorem vt.ks {m : Bool} {D : Finset ℕ} {k : ℕ} (h : vt m D k) :
 ∃ (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (Pi : ℕ → ℕ → ℕ → Prop),
  KS D j f env c Pi ∧ j+D.card ≤ k+1:=by
 induction h using vt.ind with
 | done k=>exact ⟨0,_,_,_,_,qaa,by simp⟩
 | step D k u v w ka kb hu hv hw hd hb hR ih =>
  obtain ⟨j,f,env,c,Pi,hK,hj⟩:=ih
  have hwD : w ∉ D:=fun hm=>by
   have:=hd w hm
   rw [q7W] at this
   exact Bool.noConfusion this
  have hwu : w ≠ u:=fun h=>hwD (h ▸ hu)
  have hwv : w ≠ v:=fun h=>hwD (h ▸ hv)
  have huv : u ≠ v:=by
   rintro rfl
   rcases hw with hw | hw
   · rw [Nat.and_self] at hw;exact hwu hw
   · rw [Nat.or_self] at hw;exact hwu hw
  have hwF : w ∉ D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)) :=
   fun hm=>hwD (Finset.mem_of_mem_filter _ hm)
  rw [Finset.card_insert_of_notMem hwF] at hj
  have hsz:=q9z D u v ka kb
  generalize (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))).card=size at hj hsz
  have hua : u ∈ insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))) ↔
   ka=true:=by
   rw [Finset.mem_insert,Finset.mem_filter]
   constructor
   · rintro (h | ⟨_,h,_⟩)
     · exact absurd h.symm hwu
     · exact h.resolve_right (fun hh=>hh rfl)
   · intro h
     exact Or.inr ⟨hu,Or.inl h,Or.inr huv⟩
  have hvb : v ∈ insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))) ↔
   kb=true:=by
   rw [Finset.mem_insert,Finset.mem_filter]
   constructor
   · rintro (h | ⟨_,_,h⟩)
     · exact absurd h.symm hwv
     · exact h.resolve_right (fun hh=>hh rfl)
   · intro h
     exact Or.inr ⟨hv,Or.inr (Ne.symm huv),Or.inl h⟩
  obtain ⟨j2,env2,c2,Pi2,hK2,hj2,hpu,hpv⟩ :=
   qa9 hK u v w (Ne.symm hwu) (Ne.symm hwv) huv ka kb hua hvb
  have hD' : ∀ x ∈ insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))),
   x ≠ w → x ∈ D:=by
   intro x hx hxw
   rcases Finset.mem_insert.mp hx with h | h
   · exact absurd h hxw
   · exact Finset.mem_of_mem_filter _ h
  have hfin : ∃ (f2 : ℕ → ℕ → ℕ) (env3 : ℕ → ℕ → ℕ → Prop) (c3 : ℕ → ℕ),
   KS D j2 f2 env3 c3 Pi2:=by
   rcases hw with rfl | rfl
   · exact hK2.step u v (u&&&v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
      (fun _ i => !(u.testBit i))
      (fun e i h1 h3=>q7h u v e i h1.1 h1.2 h3)
      (fun e i h1 h3=>q7g u v e i h1.1 h1.2 h3)
      (fun b e i e' i' _ h2=>h2) hpu hpv
   · exact hK2.step u v (u|||v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
      (fun e _=>u.testBit e)
      (fun e i h1 h3=>q8U u v e i h1.1 h1.2 h3)
      (fun e i h1 h3=>q8T u v e i h1.1 h1.2 h3)
      (fun b e i e' i' h1 _=>h1) hpu hpv
  obtain ⟨f2,env3,c3,hK3⟩:=hfin
  refine ⟨j2,f2,env3,c3,Pi2,hK3, ?_⟩
  have e1:=q7S ka
  have e2:=q7S kb
  omega
def MS (l : List ℕ) (j : ℕ) (Env : ℕ → ℕ → Prop) (c : ℕ → ℕ) (PiM : ℕ → ℕ → Prop) : Prop :=
 (∀ q,q < 144 → ∃ x ∈ l,Env x q) ∧
 (∀ x ∈ l,q1R (Env x)) ∧
 (∀ x ∈ l, ∀ q,Env x q → q < 144 ∧ (qD x).testBit q=true) ∧
 (∀ x ∈ l, ∀ y ∈ l,x ≠ y → c x=c y → ∀ q,Env x q → Env y q → False) ∧
 (∀ x ∈ l,1 ≤ c x → ∀ q,Env x q → PiM (c x) q) ∧
 (∀ n,q1R (PiM n)) ∧
 (∀ n q,1 ≤ n → PiM n q → ∃ y ∈ l,1 ≤ c y ∧ c y ≤ n ∧ (qD y).testBit q=true) ∧
 (∀ x ∈ l,c x ≤ j)
theorem MS.own {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
 ∀ q,q < 144 → ∃ x ∈ l,Env x q:=h.1
theorem MS.envR {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
 ∀ x ∈ l,q1R (Env x):=h.2.1
theorem MS.envB {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
 ∀ x ∈ l, ∀ q,Env x q → q < 144 ∧ (qD x).testBit q=true:=h.2.2.1
theorem MS.s1 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
 ∀ x ∈ l, ∀ y ∈ l,x ≠ y → c x=c y → ∀ q,Env x q → Env y q → False:=h.2.2.2.1
theorem MS.s2 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
 ∀ x ∈ l,1 ≤ c x → ∀ q,Env x q → PiM (c x) q:=h.2.2.2.2.1
theorem MS.piR {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
 ∀ n,q1R (PiM n):=h.2.2.2.2.2.1
theorem MS.s3 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
 ∀ n q,1 ≤ n → PiM n q → ∃ y ∈ l,1 ≤ c y ∧ c y ≤ n ∧ (qD y).testBit q=true:=h.2.2.2.2.2.2.1
theorem MS.lab {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
 ∀ x ∈ l,c x ≤ j:=h.2.2.2.2.2.2.2
theorem q5Y (S : ℕ → ℕ → Prop) (hS : q12 S) :
  q1R (fun q=>q < 144 ∧ S (q / 12) (12+q % 12)):=by
 intro e i e' i' he hi he' hi' h1 h2
 have h1' : S ((12*e+i) / 12) (12+(12*e+i) % 12):=h1.2
 have h2' : S ((12*e'+i') / 12) (12+(12*e'+i') % 12):=h2.2
 have e1 : (12*e+i) / 12=e:=by omega
 have e2 : (12*e+i) % 12=i:=by omega
 have e3 : (12*e'+i') / 12=e':=by omega
 have e4 : (12*e'+i') % 12=i':=by omega
 have e5 : (12*e+i') / 12=e:=by omega
 have e6 : (12*e+i') % 12=i':=by omega
 rw [e1,e2] at h1'
 rw [e3,e4] at h2'
 show 12*e+i' < 144 ∧ S ((12*e+i') / 12) (12+(12*e+i') % 12)
 rw [e5,e6]
 exact ⟨by omega,hS _ _ _ _ h1' h2'⟩
theorem q9D (x q : ℕ) (hq : q < 144) (h : Pc x (q / 12) (12+q % 12)) :
  (qD x).testBit q=true:=by
 have h3:=q4l x (q / 12) (q % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h.1 h.2
 rwa [Nat.div_add_mod] at h3
theorem KS.toMS {l : List ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
 {Pi : ℕ → ℕ → ℕ → Prop} (h : KS l.toFinset j f env c Pi) :
 MS l j (fun x q=>q < 144 ∧ env x (q / 12) (12+q % 12)) c
  (fun n q=>q < 144 ∧ Pi n (q / 12) (12+q % 12)):=by
 refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 · intro q hq
   obtain ⟨h1,h2⟩:=h.own (q / 12) (12+q % 12) (by omega) (by omega)
   exact ⟨_,List.mem_toFinset.mp h1,hq,h2⟩
 · intro x hx
   exact q5Y _ (h.envR x (List.mem_toFinset.mpr hx))
 · intro x hx q hq
   exact ⟨hq.1,q9D x q hq.1 (h.envP x (List.mem_toFinset.mpr hx) _ _ hq.2)⟩
 · intro x hx y hy hxy hc q h1 h2
   exact h.s1 x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy) hxy hc _ _ h1.2 h2.2
 · intro x hx hc q h1
   exact ⟨h1.1,h.s2 x (List.mem_toFinset.mpr hx) hc _ _ h1.2⟩
 · intro n
   exact q5Y _ (h.piR n)
 · intro n q hn h1
   obtain ⟨y,hy,h3,h4,h5⟩:=h.s3 n _ _ hn h1.2
   exact ⟨y,List.mem_toFinset.mp hy,h3,h4,q9D y q h1.1 h5⟩
 · intro x hx
   exact h.lab x (List.mem_toFinset.mpr hx)
theorem MS.priv_env {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
 (hM : MS l j Env c PiM) : ∀ y ∈ l, ∀ q,
 (ya (tw (l.map qD) 0 0) (qD y)).testBit q=true → Env y q:=by
 intro y hy q hq
 obtain ⟨hq144,i,e',hi,he',ha,hb⟩:=wh _ q hq
 have key : ∀ x,x < 144 →
  (Nat.land (qD y) (Nat.xor (tw (l.map qD) 0 0) qp)).testBit x=true → Env y x:=by
  intro x hx hbit
  rw [qM,j7,jZ,Bool.and_eq_true] at hbit
  obtain ⟨hzx,ht⟩:=hbit
  have ht' : (tw (l.map qD) 0 0).testBit x=false:=by simpa [hx] using ht
  obtain ⟨_,_,hpw⟩:=q40 x _ 0 0 ht'
  rw [List.pairwise_map] at hpw
  obtain ⟨z,hz,hzq⟩:=hM.own x hx
  by_cases hzz : z=y
  · rw [← hzz];exact hzq
  · exfalso
    exact q5Z (fun a b h h'=>h ⟨h'.2,h'.1⟩) l hpw z hz y hy hzz
     ⟨(hM.envB z hz x hzq).2,hzx⟩
 have h1:=key _ (by omega) ha
 have h2:=key _ (by omega) hb
 have h3:=hM.envR y hy (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
  h1 h2
 rwa [Nat.div_add_mod] at h3
def q7Z (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop :=
 (∀ x ∈ l,c x ≤ K) ∧
 (∀ x ∈ l, ∀ y ∈ l,x ≠ y → c x=c y →
  Nat.land (ya (tw (l.map qD) 0 0) (qD x)) (ya (tw (l.map qD) 0 0) (qD y))=0) ∧
 (∀ i U : ℕ,1 ≤ i →
  (∀ q,U.testBit q=true →
   ∃ x ∈ l,c x=i ∧ (ya (tw (l.map qD) 0 0) (qD x)).testBit q=true) →
  ∀ q,(vN U).testBit q=true → ∃ y ∈ l,1 ≤ c y ∧ c y ≤ i ∧ (qD y).testBit q=true) ∧
 (∀ x ∈ l, ∀ q,(ya (tw (l.map qD) 0 0) (qD x)).testBit q=true →
  (qD x).testBit q=true)
theorem MS.validLab {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
 (hM : MS l j Env c PiM) (K : ℕ) (hK : j ≤ K) : q7Z l K c:=by
 refine ⟨fun x hx=>le_trans (hM.lab x hx) hK, ?_, ?_, ?_⟩
 · intro x hx y hy hxy hc
   exact kO _ _ (fun q h1 h2 =>
    hM.s1 x hx y hy hxy hc q (hM.priv_env x hx q h1) (hM.priv_env y hy q h2))
 · intro i U hi hU q hq
   obtain ⟨_,a,e',ha,he',h1,h2⟩:=wh _ q hq
   obtain ⟨x1,hx1,hc1,hb1⟩:=hU _ h1
   obtain ⟨x2,hx2,hc2,hb2⟩:=hU _ h2
   have hp1:=hM.s2 x1 hx1 (by omega) _ (hM.priv_env x1 hx1 _ hb1)
   have hp2:=hM.s2 x2 hx2 (by omega) _ (hM.priv_env x2 hx2 _ hb2)
   rw [hc1] at hp1
   rw [hc2] at hp2
   have h3:=hM.piR i (q / 12) a e' (q % 12) (by omega) ha he' (Nat.mod_lt _ (by norm_num))
    hp1 hp2
   rw [Nat.div_add_mod] at h3
   exact hM.s3 i q hi h3
 · intro x hx q hq
   exact (hM.envB x hx q (hM.priv_env x hx q hq)).2
theorem q4p {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hR : vt m l.toFinset k) :
  ∃ c : ℕ → ℕ,q7Z l (Nat.sub (Nat.succ k) l.length) c:=by
 obtain ⟨j,f,env,c,Pi,hK,hj⟩:=hR.ks
 rw [List.toFinset_card_of_nodup hnd] at hj
 exact ⟨c,hK.toMS.validLab _ (by
  show j ≤ (k+1) - l.length
  omega)⟩
def q13 (h c : ℕ) : Bool:=Nat.beq (Nat.land h c) h
def q1K (t t2 : ℕ) : List ℕ → ℕ
 | []=>0
 | a :: l=>cond (Nat.beq (Nat.land (ya t a) t2) 0) (Nat.lor a (q1K t t2 l)) (q1K t t2 l)
def k7 (l : List ℕ) (x : ℕ) : ℕ := ya (tw (l.map qD) 0 0) (qD x)
def qal (l : List ℕ) : ℕ := tw ((l.map qD).map (ya (tw (l.map qD) 0 0))) 0 0
def jO (l : List ℕ) (x : ℕ) : Prop:=Nat.land (k7 l x) (qal l) ≠ 0
def vV (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop :=
 (∀ x ∈ l,jO l x → c x ≤ K) ∧
 (l.Pairwise (fun x y=>jO l x → jO l y → c x=c y →
  Nat.land (k7 l x) (k7 l y)=0)) ∧
 (∀ i U : ℕ,1 ≤ i → i ≤ K →
  (∀ r,U.testBit r=true →
   ∃ x ∈ l,jO l x ∧ c x=i ∧ (k7 l x).testBit r=true) →
  ∀ q,(vN U).testBit q=true →
  ∃ y ∈ l,(qD y).testBit q=true ∧ (jO l y → 1 ≤ c y ∧ c y ≤ i))
theorem vV.le {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : vV l K c) :
 ∀ x ∈ l,jO l x → c x ≤ K:=h.1
theorem vV.ne {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : vV l K c) :
 l.Pairwise (fun x y=>jO l x → jO l y → c x=c y →
  Nat.land (k7 l x) (k7 l y)=0):=h.2.1
theorem vV.cov {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : vV l K c) :
 ∀ i U : ℕ,1 ≤ i → i ≤ K →
  (∀ r,U.testBit r=true →
   ∃ x ∈ l,jO l x ∧ c x=i ∧ (k7 l x).testBit r=true) →
  ∀ q,(vN U).testBit q=true →
  ∃ y ∈ l,(qD y).testBit q=true ∧ (jO l y → 1 ≤ c y ∧ c y ≤ i):=h.2.2
theorem zU (a b q : ℕ) (h : Nat.land a b=0) (ha : a.testBit q=true)
  (hb : b.testBit q=true) : False:=by
 have e:=qM a b q
 rw [h,ha,hb,Nat.zero_testBit] at e
 exact Bool.noConfusion e
theorem q9j (t t2 q : ℕ) : ∀ as : List ℕ, ∀ a ∈ as,
 Nat.beq (Nat.land (ya t a) t2) 0=true → a.testBit q=true →
 (q1K t t2 as).testBit q=true:=by
 intro as
 induction as with
 | nil=>intro a ha;simp at ha
 | cons b as ih =>
  intro a ha hb hq
  show (cond (Nat.beq (Nat.land (ya t b) t2) 0) (Nat.lor b (q1K t t2 as))
   (q1K t t2 as)).testBit q=true
  rcases List.mem_cons.mp ha with rfl | ha
  · rw [hb]
    show (Nat.lor a (q1K t t2 as)).testBit q=true
    rw [qX,hq]
    rfl
  · have:=ih a ha hb hq
    cases Nat.beq (Nat.land (ya t b) t2) 0
    · exact this
    · show (Nat.lor b (q1K t t2 as)).testBit q=true
      rw [qX,this]
      exact Bool.or_true _
theorem wR {n : ℕ} (h : Nat.beq n 0=false) : n ≠ 0:=by
 intro e
 rw [e] at h
 exact Bool.noConfusion h
def q0Y (w : Word) (k : Word → Bool) : Bool :=
 Nat.rec (k 0) (fun n _=>k (n+1)) w
theorem q3b (w : Word) (k : Word → Bool) : q0Y w k=k w:=by
 cases w <;> rfl
def uh (ws : List Word) (k : List Word → Bool) : Bool :=
 (List.rec (motive:=fun _=>(List Word → Bool) → Bool) (fun f=>f [])
  (fun a _ next f=>q0Y a (fun w=>next (fun tail=>f (w :: tail)))) ws) k
theorem q4U (ws : List Word) (k : List Word → Bool) : uh ws k=k ws:=by
 induction ws generalizing k with
 | nil=>rfl
 | cons a ws ih =>
  change q0Y a (fun w=>uh ws (fun tail=>k (w :: tail)))=_
  rw [q3b,ih]
def vk (ws : List Word) : Bool :=
 uh (q8i' ws) fun rs =>
  q0Y (tw' rs 0 0) fun twice=>vg' twice rs 0
theorem q2Z (ws : List Word) : vk ws=q21 ws:=by
 simp only [vk,q4U,q3b,q0A,vg'_eq,q4k,q21,qa4]
end q0
abbrev qw:={ rows : List Nat // rows.length=24 }
def vr (chart : qw) (i : Nat) : Nat :=
 chart.val.getD i 0
def yJ (w : Word) (rows : List Nat) : Word :=
 List.rec 0 (fun r _ kV=>((w>>>r)&&&1)|||(kV<<<1)) rows
theorem q7e (w : Word) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
  (yJ w rows).testBit i=w.testBit (rows.getD i 0):=by
 induction rows generalizing i with
 | nil=>simp at hi
 | cons row rows ih =>
  change (((w>>>row)&&&1)|||(yJ w rows<<<1)).testBit i=_
  rw [Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_shiftLeft]
  cases i with
  | zero=>simp
  | succ i =>
   have lt : i < rows.length:=by simpa using hi
   simp [ih i lt,Nat.testBit_succ]
def zy (chart : qw) (w : Word) : Word:=yJ w chart.val
def jD (goal : Word) (chart : qw) : Prop :=
 (∀ i : Fin 12,goal.testBit (vr chart i.val)=true) ∧
 (∀ i : Fin 12,goal.testBit (vr chart (12+i.val))=false)
def q54 (goal : Word) (chart : Option qw) : Bool :=
 chart.all fun c => @decide (jD goal c) (by unfold jD;infer_instance)
theorem q7d {goal : Word} {chart : Option qw}
  (ok : q54 goal chart=true) (c : qw) (eq : chart=some c) :
  jD goal c:=by
 subst chart
 unfold jD
 exact of_decide_eq_true ok
theorem yt (chart : qw) (w : Word) {i : Nat} (hi : i < 24) :
  (zy chart w).testBit i=w.testBit (vr chart i):=by
 exact q7e w chart.val i (by rw [chart.property];exact hi)
theorem q0P {goal : Word} {chart : qw} (ok : jD goal chart) {i : Nat} (hi : i < 12) :
 goal.testBit (vr chart i)=true:=ok.1 ⟨i,hi⟩
theorem q0Q {goal : Word} {chart : qw} (ok : jD goal chart) {i : Nat} (hi : i < 12) :
 goal.testBit (vr chart (12+i))=false:=ok.2 ⟨i,hi⟩
theorem q3V {goal : Word} {chart : qw} {ws : List Word}
 (ok : jD goal chart) (nd : ws.Nodup) (kw : q3f goal ws.toFinset) :
 q0.q21 (ws.map (zy chart))=true:=by
 obtain ⟨f,good,rectangle⟩:=kw
 let label:=fun p n=>f (vr chart p) (vr chart (12+n))
 let part:=fun w=>((fun q : Nat=>q < 144 ∧ label (q/12) (q % 12)=w),
  q0.qD (zy chart w))
 have partition : q0.q58 (ws.map part):=by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro z hz
    obtain ⟨w,_,rfl⟩:=List.mem_map.mp hz
    intro p n p' n' hp hn hp' hn' h h'
    have divmod (a b : Nat) (lt : b < 12) :
     (12*a+b)/12=a ∧ (12*a+b)%12=b:=by omega
    have h1:=h.2
    have h2:=h'.2
    rw [(divmod p n hn).1,(divmod p n hn).2] at h1
    rw [(divmod p' n' hn').1,(divmod p' n' hn').2] at h2
    refine ⟨by omega,?_⟩
    rw [(divmod p n' hn').1,(divmod p n' hn').2]
    exact (rectangle _ _ _ _ (q0P ok hp) (q0P ok hp') (q0Q ok hn)
     (q0Q ok hn') (h1.trans h2.symm)).trans h1
  · intro z hz q hq
    obtain ⟨w,_,rfl⟩:=List.mem_map.mp hz
    exact hq.1
  · rw [List.pairwise_map]
    exact List.Pairwise.imp (fun hne q h1 h2=>hne (h1.2.symm.trans h2.2)) nd
  · intro q hq
    have member:=(good _ _ (q0P ok (show q/12 < 12 by omega))
     (q0Q ok (Nat.mod_lt q (by decide : 0 < 12)))).1
    exact ⟨_,List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
  · intro z hz q hq
    obtain ⟨w,_,rfl⟩:=List.mem_map.mp hz
    obtain ⟨bound,same⟩:=hq
    have hp : q/12 < 12:=by omega
    have hn : q % 12 < 12:=Nat.mod_lt _ (by decide)
    have h:=(good _ _ (q0P ok hp) (q0Q ok hn)).2
    change (label (q/12) (q % 12)).testBit (vr chart (q/12))=true ∧
     (label (q/12) (q % 12)).testBit (vr chart (12+q % 12))=false at h
    rw [same] at h
    have bit:=q0.q4l (zy chart w) (q/12) (q % 12) hp hn
     ((yt chart w (by omega)).trans h.1)
     ((yt chart w (by omega)).trans h.2)
    rwa [Nat.div_add_mod] at bit
 have hw:=q0.q7Y partition
 simpa only [q0.q21,List.map_map,Function.comp_def,part] using hw
theorem q38 {mask w : Word} (bm : qm (qI rows) mask)
  (bw : qm mask w) : qm (qI rows) w:=by
 unfold qm at *
 rw [← bw,Nat.land_assoc,bm,bw]
theorem q3D {mask goal : Word} {zi : Fin rows → Fin rows}
 (auto : q7i mask goal zi) (kH : qm (qI rows) mask)
 {k t : Nat} {S : Finset Word} (y1 : qf mask goal k t S)
 (zM : ∀ w ∈ S,qm mask w) :
 qf mask goal k t (S.image (z9 zi)):=by
 let f:=z9 zi
 have hmask : f mask=mask:=auto.2.1
 have inj {a b : Word} (ma : qm mask a) (mb : qm mask b) :
  f a=f b → a=b :=
  q8d zi auto.1 (q38 kH ma) (q38 kH mb)
 have proper {a : Word} (ma : qm mask a) (ha : qi mask a) :
  qi mask (f a):=by
  exact ⟨fun eq=>ha.1 (inj ma (by simp [qm]) (eq.trans (q7n zi).symm)),
   fun eq=>ha.2 (inj ma (by simp [qm]) (eq.trans hmask.symm))⟩
 have freshImage {S : Finset Word} {v : Word} (hv : v ∉ S) (mv : qm mask v)
  (ms : ∀ w ∈ S,qm mask w) : f v ∉ S.image f:=by
  intro hw
  obtain ⟨w,hs,eq⟩:=Finset.mem_image.mp hw
  exact hv (inj (ms w hs) mv eq ▸ hs)
 induction y1 using qf.ind with
 | stop hp =>
  rw [Finset.image_singleton,auto.2.2]
  exact qf.stop hp
 | @unary k t U a ha jB tail ih =>
  let v:=mask^^^a
  have ma:=zM a (Finset.mem_insert_self ..)
  have mv : qm mask v:=by
   apply ux (bank:=[a]) (by simpa using ma)
   exact Or.inl ⟨a,Or.inr (Or.inr (by simp)),rfl⟩
  have hnew : ∀ w ∈ insert v U,qm mask w:=by
   intro w h
   rcases Finset.mem_insert.mp h with rfl | hU
   · exact mv
   · exact zM _ (Finset.mem_insert_of_mem hU)
  have fve : f v=mask^^^f a:=by
   change z9 zi (mask^^^a)=_
   rw [q8c,auto.2.1]
  have ht:=ih hnew
  have hf:=freshImage jB mv zM
  change qf mask goal (k+1) (t+1) ((insert a U).image f)
  rw [Finset.image_insert] at ht hf
  change qf mask goal k t (insert (f v) (U.image f)) at ht
  rw [fve] at ht hf
  rw [Finset.image_insert]
  exact qf.unary (proper ma ha) hf ht
 | @binary k t U a b op pa pb ab jB tail ih =>
  let v:=qj op a b
  have ma:=zM a (Finset.mem_insert_self ..)
  have mb:=zM b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  have mv : qm mask v:=by
   apply ux (bank:=[a,b]) (by simpa using And.intro ma mb)
   exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
    cases op <;> simp [v,qj]⟩
  have hnew : ∀ w ∈ insert v U,qm mask w:=by
   intro w h
   rcases Finset.mem_insert.mp h with rfl | hU
   · exact mv
   · exact zM _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
  have fve : f v=qj op (f a) (f b):=by
   cases op
   · exact q8e ..
   · exact q9o ..
  have ht:=ih hnew
  have hf:=freshImage jB mv zM
  change qf mask goal (k+1) t ((insert a (insert b U)).image f)
  rw [Finset.image_insert] at ht
  change qf mask goal k t (insert (f v) (U.image f)) at ht
  rw [fve] at ht
  rw [Finset.image_insert,Finset.image_insert,fve] at hf
  rw [Finset.image_insert,Finset.image_insert]
  exact qf.binary (proper ma pa) (proper mb pb) (fun h=>ab (inj ma mb h)) hf ht
def jc (m : z0) (ws : List Word) : List Word :=
 List.rec [] (fun w _ next=>qB (yG m w) next) ws
theorem q8s {m : z0} {ws : List Word} {zi : Fin rows → Fin rows}
  (agree : ∀ w ∈ ws,yG m w=z9 zi w) :
  (jc m ws).toFinset=ws.toFinset.image (z9 zi):=by
 induction ws with
 | nil=>simp [jc]
 | cons w ws ih =>
  change (qB (yG m w) (jc m ws)).toFinset=_
  rw [w8,ih (fun w hw=>agree _ (List.mem_cons_of_mem _ hw)),
   agree _ List.mem_cons_self,List.toFinset_cons,Finset.image_insert]
def qN {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
 BitVec rows :=
 let args:=g.inputs.map fun i=>bank.getD i 0
 match g.op with
 | PEqualNP.CircuitLowerBounds.GateOp.and=>args.foldr (· &&& ·) (BitVec.allOnes rows)
 | PEqualNP.CircuitLowerBounds.GateOp.or=>args.foldr (· ||| ·) 0
 | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
 | _=>0
def yK {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
  List (BitVec rows) :=
 bank ++ [qN bank g]
theorem uD {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
  (bank.getD k 0).getLsbD i=(bank.map fun w=>w.getLsbD i).getD k false:=by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
 cases bank[k]? <;> simp
theorem q9r {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
 (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val=(xs.map fun w=>w.getLsbD i.val).all id:=by
 induction xs with
 | nil=>simp [i.isLt]
 | cons a t ih=>simp only [List.foldr_cons,BitVec.getLsbD_and,List.map_cons,List.all_cons,id_eq,ih]
theorem q9G {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
 (xs.foldr (· ||| ·) 0).getLsbD i.val=(xs.map fun w=>w.getLsbD i.val).any id:=by
 induction xs with
 | nil=>simp
 | cons a t ih=>simp only [List.foldr_cons,BitVec.getLsbD_or,List.map_cons,List.any_cons,id_eq,ih]
theorem q8o {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
 (g : PEqualNP.CircuitLowerBounds.Gate)
 (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
  PEqualNP.CircuitLowerBounds.GateOp.or,
  PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
 (qN bank g).getLsbD i.val =
  g.op.eval (g.inputs.map fun k=>(bank.map fun w=>w.getLsbD i.val).getD k false):=by
 obtain ⟨op,ins⟩:=g
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
 rcases hop with rfl | rfl | rfl
 · simp only [qN,PEqualNP.CircuitLowerBounds.GateOp.eval,q9r,List.map_map]
   congr 1
   apply List.map_congr_left
   intro k _
   exact uD bank i.val k
 · simp only [qN,PEqualNP.CircuitLowerBounds.GateOp.eval,q9G,List.map_map]
   congr 1
   apply List.map_congr_left
   intro k _
   exact uD bank i.val k
 · simp only [qN,PEqualNP.CircuitLowerBounds.GateOp.eval,BitVec.getLsbD_not,i.isLt,
    decide_true,Bool.true_and]
   cases ins with
   | nil=>simp
   | cons k _=>simp only [List.map_cons,List.headD_cons,uD]
theorem q3a {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
  (gs : List PEqualNP.CircuitLowerBounds.Gate)
  (hfan : ∀ g ∈ gs,g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
   PEqualNP.CircuitLowerBounds.GateOp.or,
   PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
   g.inputs.length ≤ 2) :
  (gs.foldl yK bank).map (fun w=>w.getLsbD i.val) =
   gs.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun k=>w.getD k false)])
    (bank.map fun w=>w.getLsbD i.val):=by
 induction gs generalizing bank with
 | nil=>rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  have hstep : (yK bank g).map (fun w=>w.getLsbD i.val) =
    (bank.map fun w=>w.getLsbD i.val) ++
     [g.op.eval (g.inputs.map fun k=>(bank.map fun w=>w.getLsbD i.val).getD k false)]:=by
   simp only [yK,List.map_append,List.map_cons,List.map_nil,
    q8o bank i g (hfan g List.mem_cons_self).1]
  rw [ih (yK bank g) (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg')),hstep]
def yc (p : Nat → Bool) : Nat → Nat → Bool
 | 0,s=>p s
 | k+1,s=>yc p k s&&yc p k (s+2 ^ k)
theorem jY {p : Nat → Bool} {k s i : Nat}
 (h : yc p k s=true) (lo : s ≤ i) (hi : i < s+2 ^ k) : p i=true:=by
 induction k generalizing s with
 | zero =>
  have e : i=s:=by omega
  simpa [yc,e] using h
 | succ k ih =>
  simp only [yc,Bool.and_eq_true] at h
  by_cases hlt : i < s+2 ^ k
  · exact ih h.1 lo hlt
  · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi;omega)
def yF : {k : Nat} → (Fin k → Bool) → Nat
 | 0,_=>0
 | k+1,x=>(if x 0 then 1 else 0)+2*yF (fun i : Fin k=>x i.succ)
theorem q1o : ∀ {k : Nat} (x : Fin k → Bool),yF x < 2 ^ k
 | 0,_=>by simp [yF]
 | k+1,x=>by
  have ih:=q1o (fun i : Fin k=>x i.succ)
  simp only [yF,Nat.pow_succ]
  cases x 0
  · simp;omega
  · simp;omega
theorem uE : ∀ {k : Nat} (x : Fin k → Bool) (i : Fin k),
 (yF x).testBit i.val=x i
 | 0,_,i=>Fin.elim0 i
 | k+1,x,i=>by
  refine Fin.cases ?_ ?_ i
  · simp only [yF,Fin.val_zero]
    cases x 0
    · simp [Nat.testBit_zero]
    · have hmod : (1+2*yF (fun m : Fin k=>x m.succ)) % 2=1:=by omega
      simp [Nat.testBit_zero,hmod]
  · intro j
    have ih:=uE (fun m : Fin k=>x m.succ) j
    have hdiv : ((if x 0 then 1 else 0)+2*yF (fun m : Fin k=>x m.succ)) / 2 =
     yF (fun m : Fin k=>x m.succ):=by
     cases x 0
     · simp
     · simp;omega
    simpa only [yF,Fin.val_succ,Nat.testBit_succ,hdiv] using ih
theorem q0G {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
  (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool)
  (hfan : PEqualNP.MetaComplexity.FanInTwo C)
  (hRaw : yc (fun r=>(raw.map fun v=>v.getLsbD r)==List.ofFn fun j : Fin n=>r.testBit j.val) n 0=true)
  (hGoal : yc (fun r=>goal.getLsbD r==f (fun j : Fin n=>r.testBit j.val)) n 0=true)
  (hEval : (C.gates.foldl yK raw).getD C.output 0=goal) :
  ∀ x : Fin n → Bool,C.eval (List.ofFn x)=f x:=by
 intro x
 let r:=yF x
 have hr : r < 2 ^ n:=q1o x
 have hx : x=fun j : Fin n=>r.testBit j.val:=by
  funext j
  exact (uE x j).symm
 rw [hx]
 have hbank : raw.map (fun v=>v.getLsbD r)=List.ofFn fun j : Fin n=>r.testBit j.val :=
  beq_iff_eq.mp (jY hRaw (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
 have hfg : goal.getLsbD r=f (fun j : Fin n=>r.testBit j.val) :=
  beq_iff_eq.mp (jY hGoal (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
 have hbits:=q3a raw ⟨r,hr⟩ C.gates hfan
 change (C.gates.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun k=>w.getD k false)])
  (List.ofFn fun j : Fin n=>r.testBit j.val)).getD C.output false =
   f (fun j : Fin n=>r.testBit j.val)
 rw [← hbank, ← hbits, ← uD,hEval,hfg]
theorem q7C {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
  (f : (Fin n → Bool) → Bool)
  (hRaw : yc (fun r=>(raw.map fun v=>v.getLsbD r)==List.ofFn fun j : Fin n=>r.testBit j.val) n 0=true)
  (hGoal : yc (fun r=>goal.getLsbD r==f (fun j : Fin n=>r.testBit j.val)) n 0=true)
  (C : PEqualNP.CircuitLowerBounds.Circuit)
  (hfan : PEqualNP.MetaComplexity.FanInTwo C)
  (hev : ∀ x,C.eval (List.ofFn x)=f x) :
  (C.gates.foldl yK raw).getD C.output 0=goal:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 let y : Fin n → Bool:=fun k=>j.testBit k.val
 have hbank : raw.map (fun v=>v.getLsbD j)=List.ofFn y :=
  beq_iff_eq.mp (jY hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
 have hfg : goal.getLsbD j=f y :=
  beq_iff_eq.mp (jY hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
 have hbits:=q3a raw ⟨j,hj⟩ C.gates hfan
 have hevj : (C.wires (List.ofFn y)).getD C.output false=f y:=hev y
 change (C.gates.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun k=>w.getD k false)])
  (List.ofFn y)).getD C.output false=f y at hevj
 rw [← hbank, ← hbits] at hevj
 rw [hfg, ← hevj, ← uD]
def qo (mask : Nat) (stock : List Word) (goal : Word) (t min : Nat) : Prop :=
 ∀ k S,qf mask goal k t S → (∀ w ∈ S,z4 mask stock w) → min ≤ k
abbrev q2:=Nat × List Word × Nat × Nat × Word
def qu (bounds : List q2) : Prop :=
 ∀ b ∈ bounds,
  qo b.1 b.2.1 b.2.2.2.2 0 b.2.2.1 ∧
  qo b.1 b.2.1 b.2.2.2.2 1 b.2.2.2.1
theorem q1 {b : q2} {bs : List q2}
 (old : qu bs)
 (h0 : qo b.1 b.2.1 b.2.2.2.2 0 b.2.2.1)
 (h1 : qo b.1 b.2.1 b.2.2.2.2 1 b.2.2.2.1) :
 qu (b :: bs):=by
 intro x hx
 rcases List.mem_cons.mp hx with rfl | hx
 · exact ⟨h0,h1⟩
 · exact old x hx
theorem um {mask : Word} {stock : List Word}
  (h : stock.all (fun w=>w&&&mask==w)=true) :
  ∀ w ∈ stock,qm mask w :=
 fun w hw=>beq_iff_eq.mp (List.all_eq_true.mp h w hw)
theorem qF {mask target : Word} {w : List Word} {z : Word} {k t : Nat} {S : Finset Word}
 (h : qf mask target k t S) (sub : ∀ a ∈ S,a ∈ w ++ [z]) :
 (zB mask w z → ∃ S',qf mask target k t S' ∧ ∀ a ∈ S',a ∈ w) ∧
 (vJ mask w z → ∃ k' S',k' ≤ k+1 ∧ qf mask target k' t S' ∧ ∀ a ∈ S',a ∈ w) ∧
 ((∃ a ∈ w,qi mask a ∧ z=mask^^^a) →
  ∃ k' t' S',k' ≤ k+1 ∧ t ≤ t' ∧ t' ≤ t+1 ∧ k'+(t+1 - t') ≤ k+1 ∧
   qf mask target k' t' S' ∧ ∀ a ∈ S',a ∈ w):=by
 have noZ (hdrop : z ∉ S ∨ z ∈ w) : ∀ a ∈ S,a ∈ w:=by
  intro a ha
  have hu : a ∈ w ∨ a=z:=by simpa using sub a ha
  rcases hu with hu | rfl
  · exact hu
  · exact hdrop.resolve_left (fun hn=>hn ha)
 refine ⟨?_, ?_, ?_⟩
 · intro hr
   by_cases hm : z ∈ S
   · by_cases hw : z ∈ w
     · exact ⟨S,h,noZ (Or.inr hw)⟩
     · exact False.elim ((hr.resolve_left hw) (jK h z hm))
   · exact ⟨S,h,noZ (Or.inl hm)⟩
 · intro hb
   by_cases hm : z ∈ S
   · by_cases hw : z ∈ w
     · exact ⟨k,S,by omega,h,noZ (Or.inr hw)⟩
     · obtain ⟨d,a,b,ha,hb',pa,pb,hab,rfl⟩:=hb
       let U:=S.erase (qj d a b)
       have ht : qf mask target k t (insert (qj d a b) U):=by
        simpa [U,Finset.insert_erase hm] using h
       have hu : ∀ v ∈ U,v ∈ w:=by
        intro v hv
        obtain ⟨hne,hvm⟩:=Finset.mem_erase.mp hv
        simpa [hne] using sub v hvm
       have hf : qj d a b ∉ insert a (insert b U):=by
        intro hh
        rcases Finset.mem_insert.mp hh with eq | u
        · exact hw (eq.symm ▸ ha)
        rcases Finset.mem_insert.mp u with eq | u
        · exact hw (eq.symm ▸ hb')
        · exact hw (hu _ u)
       exact ⟨k+1,insert a (insert b U),Nat.le_refl _,
        qf.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb' hu)⟩
   · exact ⟨k,S,by omega,h,noZ (Or.inl hm)⟩
 · intro hu_w
   by_cases hm : z ∈ S
   · by_cases hw : z ∈ w
     · exact ⟨k,t,S,by omega,by omega,by omega,by omega,h,noZ (Or.inr hw)⟩
     · obtain ⟨a,ha,pa,rfl⟩:=hu_w
       let U:=S.erase (mask^^^a)
       have ht : qf mask target k t (insert (mask^^^a) U):=by
        simpa [U,Finset.insert_erase hm] using h
       have hu : ∀ v ∈ U,v ∈ w:=by
        intro v hv
        obtain ⟨hne,hvm⟩:=Finset.mem_erase.mp hv
        simpa [hne] using sub v hvm
       have hf : mask^^^a ∉ insert a U:=by
        intro hh
        rcases Finset.mem_insert.mp hh with eq | u
        · exact hw (eq.symm ▸ ha)
        · exact hw (hu _ u)
       exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by omega,Nat.le_refl _,by omega,
        qf.unary pa hf ht,by simpa using And.intro ha hu⟩
   · exact ⟨k,t,S,by omega,by omega,by omega,by omega,h,noZ (Or.inl hm)⟩
theorem q80 {mask cut a : Word} (sub : mask&&&cut=cut) :
 (mask^^^a)&&&cut=cut^^^(a&&&cut):=by
 apply Nat.eq_of_testBit_eq;intro i
 have h:=congrArg (fun n : Nat=>n.testBit i) sub
 simp only [Nat.testBit_and,Nat.testBit_xor] at h ⊢
 cases hc : cut.testBit i
 · simp
 · simp [hc] at h;simp [h]
theorem q8u {cut a b : Word} (d : Bool) :
  qj d a b&&&cut=qj d (a&&&cut) (b&&&cut):=by
 apply Nat.eq_of_testBit_eq;intro i
 cases d <;> simp only [qj,Bool.false_eq_true,ite_true,ite_false,
  Nat.testBit_and,Nat.testBit_or] <;> cases cut.testBit i <;> simp
theorem zY (cut w : Word) : qW cut w=true ↔ ¬qi cut (w&&&cut):=by
 simp only [qW,qi,Bool.or_eq_true,beq_iff_eq]
 tauto
theorem kI (cut a : Word) (U : Finset Word) :
 ((insert a U).filter (fun w=>qW cut w=true)).card ≤
  (U.filter (fun w=>qW cut w=true)).card +
   if qW cut a=true then 1 else 0:=by
 by_cases ha : a ∈ U
 · rw [Finset.insert_eq_of_mem ha];split <;> omega
 · rw [Finset.filter_insert]
   split
   · rw [Finset.card_insert_of_notMem (by simp [ha])]
   · exact Nat.le_refl _
theorem kJ (cut a : Word) (U : Finset Word) (ha : a ∉ U) :
 ((insert a U).filter (fun w=>qW cut w=true)).card =
  (U.filter (fun w=>qW cut w=true)).card +
   if qW cut a=true then 1 else 0:=by
 rw [Finset.filter_insert]
 split
 · rw [Finset.card_insert_of_notMem (by simp [ha])]
 · omega
theorem q6I {cut a : Word} :
 qi cut (cut^^^a) ↔ qi cut a:=by
 have cancel : cut^^^(cut^^^a)=a:=by
  apply Nat.eq_of_testBit_eq;intro i;simp only [Nat.testBit_xor]
  cases cut.testBit i <;> cases a.testBit i <;> simp
 have selfZero : cut^^^cut=0:=by
  apply Nat.eq_of_testBit_eq;intro i;simp
 constructor
 · intro ⟨h0,hm⟩
   exact ⟨fun eq=>hm (by rw [eq,Nat.xor_zero]),fun eq=>h0 (by rw [eq,selfZero])⟩
 · intro ⟨h0,hm⟩
   exact ⟨fun eq=>hm (by rw [← cancel,eq,Nat.xor_zero]),fun eq=>h0 (by rw [← cancel,eq,selfZero])⟩
theorem q1J {cut : Word} {wList : List Word} {x y : Word} (d : Bool)
 (hx : x ∈ wList) (hy : y ∈ wList) (mx : qm cut x) (my : qm cut y)
 (hflat : ¬qi cut x ∨ ¬qi cut y) :
 zB cut wList (qj d x y):=by
 have absorb {u : Word} (mu : qm cut u) : cut&&&u=u ∧ cut|||u=cut:=by
  constructor
  · rw [Nat.land_comm];exact mu
  · apply Nat.eq_of_testBit_eq;intro i
    have h:=congrArg (fun n : Nat=>n.testBit i) mu
    simp only [Nat.testBit_and,Nat.testBit_or] at h ⊢
    cases hc : cut.testBit i <;> simp_all
 have splitFlat {u : Word} (h : ¬qi cut u) : u=0 ∨ u=cut:=by
  by_cases h0 : u=0
  · exact Or.inl h0
  · exact Or.inr (by by_contra h1;exact h ⟨h0,h1⟩)
 rcases hflat with hfx | hfy
 · rcases splitFlat hfx with hx0 | hxc
   · rw [hx0];cases d
     · exact Or.inr (by simp [qj,qi])
     · exact Or.inl (by simpa [qj] using hy)
   · rw [hxc];cases d
     · exact Or.inl (by simpa [qj,(absorb my).1] using hy)
     · exact Or.inr (by simp [qj,(absorb my).2,qi])
 · rcases splitFlat hfy with hy0 | hyc
   · rw [hy0];cases d
     · exact Or.inr (by simp [qj,qi])
     · exact Or.inl (by simpa [qj] using hx)
   · rw [hyc];cases d
     · exact Or.inl (by simpa [qj,Nat.land_comm,(absorb mx).1] using hx)
     · exact Or.inr (by simp [qj,Nat.lor_comm,(absorb mx).2,qi])
theorem q2E {mask cut target : Word} (submask : mask&&&cut=cut)
 (hgoal : qi cut (target&&&cut)) {k t : Nat} {S : Finset Word}
 (y1 : qf mask target k t S) :
 ∃ k' t' S',qf cut (target&&&cut) k' t' S' ∧
  t' ≤ t ∧ k'+(S.filter (fun w=>qW cut w=true)).card+(t - t') ≤ k ∧
  ∀ v ∈ S', ∃ w ∈ S,v=w&&&cut:=by
 induction y1 using qf.ind with
 | stop hp =>
  have hmf : ¬(qW cut target=true):=fun h=>(zY cut target).mp h hgoal
  have hfl : (({target} : Finset Word).filter (fun w=>qW cut w=true)).card=0:=by
   simp [hmf]
  exact ⟨0,0,{target&&&cut},qf.stop hgoal,Nat.le_refl _,by omega,
   fun v hv=>⟨target,Finset.mem_singleton_self _,by simpa using hv⟩⟩
 | @unary k t U a ha hfresh tail ih =>
  obtain ⟨k',t',S',hlive,ht,hcard,hsub⟩:=ih
  have hzU : mask^^^a ∉ U:=fun hm=>hfresh (Finset.mem_insert_of_mem hm)
  have hfcChild:=kJ cut (mask^^^a) U hzU
  have hfcPar:=kI cut a U
  have hzeq : (mask^^^a)&&&cut=cut^^^(a&&&cut):=q80 submask
  have hpropEq : qi cut ((mask^^^a)&&&cut) ↔ qi cut (a&&&cut):=by
   rw [hzeq];exact q6I
  let wList : List Word:=(insert a U).toList.map (· &&& cut)
  have subList : ∀ v ∈ S',v ∈ wList ++ [(mask^^^a)&&&cut]:=by
   intro v hv;obtain ⟨u,hu,rfl⟩:=hsub v hv
   rcases Finset.mem_insert.mp hu with rfl | huU
   · exact List.mem_append_right _ List.mem_cons_self
   · exact List.mem_append_left _ (List.mem_map.mpr ⟨u,Finset.mem_toList.mpr (Finset.mem_insert_of_mem huU),rfl⟩)
  by_cases hpa : qi cut (a&&&cut)
  · have hpz : qi cut ((mask^^^a)&&&cut):=hpropEq.mpr hpa
    have hma : ¬(qW cut a=true):=fun h=>(zY cut a).mp h hpa
    have hmz : ¬(qW cut (mask^^^a)=true):=fun h=>(zY cut (mask^^^a)).mp h hpz
    have haMem : a&&&cut ∈ wList :=
     List.mem_map.mpr ⟨a,Finset.mem_toList.mpr (Finset.mem_insert_self a U),rfl⟩
    obtain ⟨k2,t2,S2,hk2,_,ht2,hsum2,hl2,hsub2⟩ :=
     (qF hlive subList).2.2 ⟨a&&&cut,haMem,hpa,hzeq⟩
    refine ⟨k2,t2,S2,hl2,by omega, ?_, ?_⟩
    · simp only [hma,hmz,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar;omega
    · intro v hv;obtain ⟨u,hu,rfl⟩:=List.mem_map.mp (hsub2 v hv);exact ⟨u,Finset.mem_toList.mp hu,rfl⟩
  · have hpz : ¬qi cut ((mask^^^a)&&&cut):=fun h=>hpa (hpropEq.mp h)
    have hma : qW cut a=true:=(zY cut a).mpr hpa
    have hmz : qW cut (mask^^^a)=true:=(zY cut (mask^^^a)).mpr hpz
    obtain ⟨S2,hl2,hsub2⟩:=(qF hlive subList).1 (Or.inr hpz)
    refine ⟨k',t',S2,hl2,by omega, ?_, ?_⟩
    · simp only [hma,hmz, ↓reduceIte] at hfcChild hfcPar;omega
    · intro v hv;obtain ⟨u,hu,rfl⟩:=List.mem_map.mp (hsub2 v hv);exact ⟨u,Finset.mem_toList.mp hu,rfl⟩
 | @binary k t U a b d pa pb hab hfresh tail ih =>
  obtain ⟨k',t',S',hlive,ht,hcard,hsub⟩:=ih
  have hzU : qj d a b ∉ U:=fun hm=>hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hfcChild:=kJ cut (qj d a b) U hzU
  have hfcPar1:=kI cut a (insert b U)
  have hfcPar2:=kI cut b U
  let wList : List Word:=(insert a (insert b U)).toList.map (· &&& cut)
  have subList : ∀ v ∈ S',v ∈ wList ++ [qj d a b&&&cut]:=by
   intro v hv;obtain ⟨u,hu,rfl⟩:=hsub v hv
   rcases Finset.mem_insert.mp hu with rfl | huU
   · exact List.mem_append_right _ List.mem_cons_self
   · exact List.mem_append_left _ (List.mem_map.mpr ⟨u,Finset.mem_toList.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem huU)),rfl⟩)
  have hzeq : qj d a b&&&cut=qj d (a&&&cut) (b&&&cut):=q8u d
  have haMem : a&&&cut ∈ wList :=
   List.mem_map.mpr ⟨a,Finset.mem_toList.mpr (Finset.mem_insert_self a _),rfl⟩
  have hbMem : b&&&cut ∈ wList :=
   List.mem_map.mpr ⟨b,Finset.mem_toList.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)),rfl⟩
  have finishSub : ∀ {S2 : Finset Word},(∀ v ∈ S2,v ∈ wList) →
   ∀ v ∈ S2, ∃ w ∈ insert a (insert b U),v=w&&&cut:=by
   intro S2 hs2 v hv;obtain ⟨u,hu,rfl⟩:=List.mem_map.mp (hs2 v hv);exact ⟨u,Finset.mem_toList.mp hu,rfl⟩
  by_cases hpa : qi cut (a&&&cut)
  · have hma : ¬(qW cut a=true):=fun h=>(zY cut a).mp h hpa
    by_cases hpb : qi cut (b&&&cut)
    · have hmb : ¬(qW cut b=true):=fun h=>(zY cut b).mp h hpb
      by_cases heq : a&&&cut=b&&&cut
      · have hrep : zB cut wList (qj d a b&&&cut):=by
         rw [hzeq,heq];cases d <;> exact Or.inl (by simpa [qj] using hbMem)
        obtain ⟨S2,hl2,hsub2⟩:=(qF hlive subList).1 hrep
        refine ⟨k',t',S2,hl2,ht, ?_,finishSub hsub2⟩
        simp only [hma,hmb,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar1 hfcPar2
        by_cases hmz : qW cut (qj d a b)=true <;> simp [hmz] at hfcChild <;> omega
      · have hbin : vJ cut wList (qj d a b&&&cut) :=
         ⟨d,a&&&cut,b&&&cut,haMem,hbMem,hpa,hpb,heq,hzeq⟩
        obtain ⟨k2,S2,hk2,hl2,hsub2⟩:=(qF hlive subList).2.1 hbin
        refine ⟨k2,t',S2,hl2,ht, ?_,finishSub hsub2⟩
        simp only [hma,hmb,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar1 hfcPar2
        by_cases hmz : qW cut (qj d a b)=true <;> simp [hmz] at hfcChild <;> omega
    · have hmb : qW cut b=true:=(zY cut b).mpr hpb
      have hrep : zB cut wList (qj d a b&&&cut):=by
       rw [hzeq];exact q1J d haMem hbMem (by simp [qm]) (by simp [qm]) (Or.inr hpb)
      obtain ⟨S2,hl2,hsub2⟩:=(qF hlive subList).1 hrep
      refine ⟨k',t',S2,hl2,ht, ?_,finishSub hsub2⟩
      simp only [hma,hmb,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar1 hfcPar2
      by_cases hmz : qW cut (qj d a b)=true <;> simp [hmz] at hfcChild <;> omega
  · have hma : qW cut a=true:=(zY cut a).mpr hpa
    by_cases hpb : qi cut (b&&&cut)
    · have hmb : ¬(qW cut b=true):=fun h=>(zY cut b).mp h hpb
      have hrep : zB cut wList (qj d a b&&&cut):=by
       rw [hzeq];exact q1J d haMem hbMem (by simp [qm]) (by simp [qm]) (Or.inl hpa)
      obtain ⟨S2,hl2,hsub2⟩:=(qF hlive subList).1 hrep
      refine ⟨k',t',S2,hl2,ht, ?_,finishSub hsub2⟩
      simp only [hma,hmb,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar1 hfcPar2
      by_cases hmz : qW cut (qj d a b)=true <;> simp [hmz] at hfcChild <;> omega
    · have hmb : qW cut b=true:=(zY cut b).mpr hpb
      have hrep : zB cut wList (qj d a b&&&cut):=by
       rw [hzeq];exact q1J d haMem hbMem (by simp [qm]) (by simp [qm]) (Or.inl hpa)
      have hpz : ¬qi cut (qj d a b&&&cut):=by
       rw [hzeq]
       have ha0 : a&&&cut=0 ∨ a&&&cut=cut:=by
        by_cases h0 : a&&&cut=0
        · exact Or.inl h0
        · exact Or.inr (by by_contra h1;exact hpa ⟨h0,h1⟩)
       have hb0 : b&&&cut=0 ∨ b&&&cut=cut:=by
        by_cases h0 : b&&&cut=0
        · exact Or.inl h0
        · exact Or.inr (by by_contra h1;exact hpb ⟨h0,h1⟩)
       rcases ha0 with h1 | h1 <;> rcases hb0 with h2 | h2 <;> cases d <;>
        simp [h1,h2,qj,qi]
      have hmz : qW cut (qj d a b)=true:=(zY cut (qj d a b)).mpr hpz
      obtain ⟨S2,hl2,hsub2⟩:=(qF hlive subList).1 hrep
      refine ⟨k',t',S2,hl2,ht, ?_,finishSub hsub2⟩
      simp only [hma,hmb,hmz, ↓reduceIte] at hfcChild hfcPar1 hfcPar2;omega
theorem q2o (cut : Word) {ws : List Word} (nd : ws.Nodup) :
  z5 cut ws=(ws.toFinset.filter (fun w=>qW cut w=true)).card:=by
 induction ws with
 | nil=>rfl
 | cons w ws ih =>
  have hnd:=List.nodup_cons.mp nd
  have hw : w ∉ ws.toFinset:=by simpa using hnd.1
  change (if qW cut w then z5 cut ws+1 else z5 cut ws)=_
  rw [List.toFinset_cons,kJ cut w ws.toFinset hw,ih hnd.2]
  cases qW cut w <;> simp
theorem q6R {m1 m2 g1 g2 : Word} (f : Word → Word)
 (h0 : f 0=0) (hm : f m1=m2)
 (hxor : ∀ a,f (m1^^^a)=m2^^^f a)
 (hand : ∀ a b,f (a&&&b)=f a&&&f b)
 (hor : ∀ a b,f (a|||b)=f a|||f b)
 (hgoal : f g1=g2)
 (hinj : ∀ a b,qm m1 a → qm m1 b → f a=f b → a=b)
 {k t : Nat} {S : Finset Word} (y1 : qf m1 g1 k t S)
 (hM : ∀ w ∈ S,qm m1 w) :
 qf m2 g2 k t (S.image f):=by
 have hprop {a : Word} (ma : qm m1 a) (pa : qi m1 a) : qi m2 (f a) :=
  ⟨fun eq=>pa.1 (hinj a 0 ma (by simp [qm]) (eq.trans h0.symm)),
   fun eq=>pa.2 (hinj a m1 ma (by simp [qm]) (eq.trans hm.symm))⟩
 have hfresh {T : Finset Word} {v : Word} (hv : v ∉ T) (mv : qm m1 v)
  (mT : ∀ w ∈ T,qm m1 w) : f v ∉ T.image f:=by
  intro hmem;obtain ⟨w,hw,eq⟩:=Finset.mem_image.mp hmem
  exact hv (hinj w v (mT w hw) mv eq ▸ hw)
 induction y1 using qf.ind with
 | stop hp =>
  rw [Finset.image_singleton,hgoal]
  exact qf.stop (hgoal ▸ hprop (hM g1 (Finset.mem_singleton_self g1)) hp)
 | @unary k t U a pa jB tail ih =>
  let v:=m1^^^a
  have ma:=hM a (Finset.mem_insert_self a U)
  have mv : qm m1 v:=ux (bank:=[a]) (by simpa using ma) (Or.inl ⟨a,Or.inr (Or.inr (by simp)),rfl⟩)
  have hnew : ∀ w ∈ insert v U,qm m1 w:=fun w hw=>by
   rcases Finset.mem_insert.mp hw with rfl | hU
   · exact mv
   · exact hM w (Finset.mem_insert_of_mem hU)
  have ht:=ih hnew
  have hf:=hfresh jB mv hM
  rw [Finset.image_insert,hxor a] at ht hf
  rw [Finset.image_insert]
  exact qf.unary (hprop ma pa) hf ht
 | @binary k t U a b d pa pb hab jB tail ih =>
  let v:=qj d a b
  have ma:=hM a (Finset.mem_insert_self a _)
  have mb:=hM b (Finset.mem_insert_of_mem (Finset.mem_insert_self b U))
  have mv : qm m1 v:=ux (bank:=[a,b]) (by simpa using And.intro ma mb)
   (Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by cases d <;> simp [v,qj]⟩)
  have hnew : ∀ w ∈ insert v U,qm m1 w:=fun w hw=>by
   rcases Finset.mem_insert.mp hw with rfl | hU
   · exact mv
   · exact hM w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
  have hfv : f v=qj d (f a) (f b):=by cases d <;> simp [v,qj,hand,hor]
  have ht:=ih hnew
  have hf:=hfresh jB mv hM
  rw [Finset.image_insert,hfv] at ht
  rw [Finset.image_insert,Finset.image_insert,hfv] at hf
  rw [Finset.image_insert,Finset.image_insert]
  exact qf.binary (hprop ma pa) (hprop mb pb) (fun h=>hab (hinj a b ma mb h)) hf ht
theorem q34 {m1 m2 g1 g2 t min : Nat} {s1 s2 : List Word} (f : Word → Word)
 (h0 : f 0=0) (hm : f m1=m2)
 (hxor : ∀ a,f (m1^^^a)=m2^^^f a)
 (hand : ∀ a b,f (a&&&b)=f a&&&f b)
 (hor : ∀ a b,f (a|||b)=f a|||f b)
 (hgoal : f g1=g2)
 (hinj : ∀ a b,qm m1 a → qm m1 b → f a=f b → a=b)
 (s1M : ∀ w ∈ s1,qm m1 w)
 (sup : ∀ w ∈ s1,z4 m2 s2 (f w))
 (hlow : qo m2 s2 g2 t min) :
 qo m1 s1 g1 t min:=by
 intro k S hlive hS
 have hSM : ∀ w ∈ S,qm m1 w:=fun w hw=>zX s1M (hS w hw)
 have hl2:=q6R f h0 hm hxor hand hor hgoal hinj hlive hSM
 have hS2 : ∀ v ∈ S.image f,z4 m2 s2 v:=by
  intro v hv;obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
  rcases hS w hw with rfl | rfl | hmem
  · exact Or.inl h0
  · exact Or.inr (Or.inl hm)
  · exact sup w hmem
 exact hlow k (S.image f) hl2 hS2
def y5 {rows m : Nat} (source : Fin m → Fin rows) (w : Word) : Word :=
 yZ fun i=>w.testBit (source i).val
theorem vU {rows m : Nat} (source : Fin m → Fin rows)
 {m1 m2 : Word} {s1 s2 : List Word} {g1 g2 t min : Nat}
 (yV : decide ((m1&&&qI rows=m1) ∧
  (∀ r : Fin rows,m1.testBit r.val=true → ∃ i : Fin m,source i=r) ∧
  y5 source m1=m2 ∧ y5 source g1=g2 ∧
  s1.all (fun w=>w&&&m1==w)=true ∧
  s1.all (fun w=>qC m2 s2 (y5 source w))=true)=true)
 (hlow : qo m2 s2 g2 t min) :
 qo m1 s1 g1 t min:=by
 obtain ⟨bm,hsurj,hm,hg,s1M,sup⟩:=of_decide_eq_true yV
 let f:=y5 source
 have hz : f 0=0:=by simpa only [f,y5,Nat.zero_testBit] using (q60 (rows:=m))
 have hand (a b : Word) : f (a&&&b)=f a&&&f b:=by
  simp only [f,y5,Nat.testBit_and,yZ,q6j,BitVec.toNat_and]
 have hor (a b : Word) : f (a|||b)=f a|||f b:=by
  simp only [f,y5,Nat.testBit_or,yZ,q7R,BitVec.toNat_or]
 have hxor (a : Word) : f (m1^^^a)=m2^^^f a:=by
  have hx : zq (fun i : Fin m=>(m1^^^a).testBit (source i).val) =
   zq (fun i : Fin m=>m1.testBit (source i).val) ^^^
   zq (fun i : Fin m=>a.testBit (source i).val):=by
   apply BitVec.eq_of_getLsbD_eq;intro i hi
   rw [BitVec.getLsbD_xor,y6 _ ⟨i,hi⟩,y6 _ ⟨i,hi⟩,y6 _ ⟨i,hi⟩]
   exact Nat.testBit_xor _ _ _
  have h2 : f (m1^^^a)=f m1^^^f a:=by
   simpa only [f,y5,yZ,BitVec.toNat_xor] using congrArg BitVec.toNat hx
  rw [h2];exact congrArg (· ^^^ f a) hm
 have hinj : ∀ a b,qm m1 a → qm m1 b → f a=f b → a=b:=by
  intro a b ma mb eq
  apply Nat.eq_of_testBit_eq;intro r
  by_cases hmr : m1.testBit r=true
  · have hrlt : r < rows:=by
     by_contra! big
     have eb:=congrArg (fun n : Nat=>n.testBit r) bm
     simp [qI,Nat.testBit_and,Nat.testBit_two_pow_sub_one,hmr,Nat.not_lt.mpr big] at eb
    obtain ⟨i,hi⟩:=hsurj ⟨r,hrlt⟩ hmr
    have hbit:=congrArg (fun n : Nat=>n.testBit i.val) eq
    simp only [f,y5,yZ,BitVec.testBit_toNat,i.isLt,decide_true,Bool.true_and,y6,hi] at hbit
    exact hbit
  · have ea:=congrArg (fun n : Nat=>n.testBit r) ma
    have eb:=congrArg (fun n : Nat=>n.testBit r) mb
    simp [qm,Nat.testBit_and,hmr] at ea eb
    rw [ea,eb]
 exact q34 f hz hm hxor hand hor hg hinj
  (fun w hw=>beq_iff_eq.mp (List.all_eq_true.mp s1M w hw))
  (fun w hw=>jn.mp (List.all_eq_true.mp sup w hw)) hlow
def qq {α : Type} (word : Word) (cont : Word → α) : α :=
 Nat.rec (cont 0) (fun k _=>cont (k+1)) word
theorem zG {α : Type} (word : Word) (cont : Word → α) :
 qq word cont=cont word:=by cases word <;> rfl
def jU (words : List Word) (cont : List Word → Bool) : Bool :=
 (List.rec (motive:=fun _=>(List Word → Bool) → Bool) (fun k=>k [])
  (fun w _ next k=>qq w (fun v=>next (fun rest=>k (v :: rest)))) words) cont
theorem wm (words : List Word) (cont : List Word → Bool) :
  jU words cont=cont words:=by
 induction words generalizing cont with
 | nil=>rfl
 | cons w ws ih =>
  change qq w (fun v=>jU ws (fun rest=>cont (v :: rest)))=_
  rw [zG,ih]
def y8 (mask : Nat) (bank : List Word) (v a b : Word) : Bool :=
 qC mask bank a&&qC mask bank b&&(v==(a&&&b)||v==(a|||b))
def qd (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
  (bank : List Word) (notsLeft : Nat) : List Word × Nat :=
 (List.rec (motive:=fun _=>List Word → Nat → List Word × Nat) (fun _ _=>([],0))
  (fun (w,a,b) _ next bank nl =>
   qq (w&&&mask) fun v =>
    if needed.contains v && !qC mask bank v then
     qq (a&&&mask) fun am =>
      qq (b&&&mask) fun bm =>
       if y8 mask bank v am bm then
        let r:=next (v :: bank) nl
        (v :: r.1,r.2)
       else if nl > 0&&qC mask bank am&&v==(mask^^^am) then
        let r:=next (v :: bank) (nl - 1)
        (v :: r.1,r.2+1)
       else next bank nl
    else next bank nl) recipes) bank notsLeft
theorem q3g {mask goal : Word} {needed : List Word}
 {recipes : List (Word × Word × Word)} {bank : List Word} {nl k t : Nat} {S : Finset Word}
 (bankM : ∀ w ∈ bank,qm mask w)
 (hlive : qf mask goal k t S)
 (hsub : ∀ w ∈ S,w ∈ (qd mask needed recipes bank nl).1 ++ bank) :
 ∃ k' t' S',
  k'+(t+(qd mask needed recipes bank nl).2 - t') ≤
   k+(qd mask needed recipes bank nl).1.length ∧
  (qd mask needed recipes bank nl).2 ≤ nl ∧
  t ≤ t' ∧ t' ≤ t+(qd mask needed recipes bank nl).2 ∧
  qf mask goal k' t' S' ∧ ∀ w ∈ S',w ∈ bank:=by
 induction recipes generalizing bank nl k t S with
 | nil =>
  exact ⟨k,t,S,by simp [qd],Nat.zero_le _,Nat.le_refl _,by simp [qd],hlive,by simpa [qd] using hsub⟩
 | cons rec rest ih =>
  obtain ⟨w,a,b⟩:=rec
  let v:=w&&&mask
  let am:=a&&&mask
  let bm:=b&&&mask
  have hstep : qd mask needed ((w,a,b) :: rest) bank nl =
   if needed.contains v && !qC mask bank v then
    if y8 mask bank v am bm then
     let r:=qd mask needed rest (v :: bank) nl
     (v :: r.1,r.2)
    else if nl > 0&&qC mask bank am&&v==(mask^^^am) then
     let r:=qd mask needed rest (v :: bank) (nl - 1)
     (v :: r.1,r.2+1)
    else qd mask needed rest bank nl
   else qd mask needed rest bank nl:=by
   change qq v (fun v=>if needed.contains v && !qC mask bank v then
    qq am (fun am=>qq bm (fun bm =>
     if y8 mask bank v am bm then
      let r:=qd mask needed rest (v :: bank) nl
      (v :: r.1,r.2)
     else if nl > 0&&qC mask bank am&&v==(mask^^^am) then
      let r:=qd mask needed rest (v :: bank) (nl - 1)
      (v :: r.1,r.2+1)
     else qd mask needed rest bank nl))
    else qd mask needed rest bank nl)=_
   simp only [zG]
  rw [hstep] at hsub ⊢
  by_cases hcond : (needed.contains v && !qC mask bank v)=true
  · rw [if_pos hcond] at hsub ⊢
    by_cases hbin : y8 mask bank v am bm=true
    · rw [if_pos hbin] at hsub ⊢
      dsimp only at hsub ⊢
      have bankM' : ∀ u ∈ v :: bank,qm mask u:=fun u hu=>by
       rcases List.mem_cons.mp hu with rfl | hu
       · simp [v,qm]
       · exact bankM u hu
      have hsub' : ∀ u ∈ S,u ∈ (qd mask needed rest (v :: bank) nl).1 ++ (v :: bank):=by
       intro u hu
       have hm:=hsub u hu
       simp only [List.mem_append,List.mem_cons] at hm ⊢
       rcases hm with (huv | h1) | h2
       · exact Or.inr (Or.inl huv)
       · exact Or.inl h1
       · exact Or.inr (Or.inr h2)
      obtain ⟨k1,t1,S1,hk1,hu1,ht1lo,ht1,hl1,hs1⟩:=ih bankM' hlive hsub'
      have hs1' : ∀ u ∈ S1,u ∈ bank ++ [v]:=fun u hu=>by simpa [or_comm] using hs1 u hu
      simp only [y8,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,jn] at hbin
      obtain ⟨⟨ham,hbm⟩,hveq⟩:=hbin
      have hcls : zB mask bank v ∨ vJ mask bank v:=by
       rcases hveq with hv | hv
       · rw [hv];exact vq bankM false ham hbm
       · rw [hv];exact vq bankM true ham hbm
      rcases hcls with hrep | hbw
      · obtain ⟨S2,hl2,hs2⟩:=(qF hl1 hs1').1 hrep
        exact ⟨k1,t1,S2,by simp only [List.length_cons];omega,hu1,ht1lo,ht1,hl2,hs2⟩
      · obtain ⟨k2,S2,hk2,hl2,hs2⟩:=(qF hl1 hs1').2.1 hbw
        exact ⟨k2,t1,S2,by simp only [List.length_cons];omega,hu1,ht1lo,ht1,hl2,hs2⟩
    · rw [if_neg hbin] at hsub ⊢
      by_cases hun : (nl > 0&&qC mask bank am&&(v==mask^^^am))=true
      · rw [if_pos hun] at hsub ⊢
        dsimp only at hsub ⊢
        have bankM' : ∀ u ∈ v :: bank,qm mask u:=fun u hu=>by
         rcases List.mem_cons.mp hu with rfl | hu
         · simp [v,qm]
         · exact bankM u hu
        have hsub' : ∀ u ∈ S,u ∈ (qd mask needed rest (v :: bank) (nl - 1)).1 ++ (v :: bank):=by
         intro u hu
         have hm:=hsub u hu
         simp only [List.mem_append,List.mem_cons] at hm ⊢
         rcases hm with (huv | h1) | h2
         · exact Or.inr (Or.inl huv)
         · exact Or.inl h1
         · exact Or.inr (Or.inr h2)
        obtain ⟨k1,t1,S1,hk1,hu1,ht1lo,ht1,hl1,hs1⟩:=ih bankM' hlive hsub'
        have hs1' : ∀ u ∈ S1,u ∈ bank ++ [v]:=fun u hu=>by simpa [or_comm] using hs1 u hu
        simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,jn] at hun
        obtain ⟨⟨hnl,ham⟩,hveq⟩:=hun
        have hcls : zB mask bank v ∨ (∃ a ∈ bank,qi mask a ∧ v=mask^^^a):=by
         by_cases ha0 : am=0
         · exact Or.inl (Or.inr (by simp [hveq,ha0,qi]))
         by_cases ham2 : am=mask
         · have hself : mask^^^mask=0:=by apply Nat.eq_of_testBit_eq;intro i;simp
           exact Or.inl (Or.inr (by simp [hveq,ham2,hself,qi]))
         exact Or.inr ⟨am,(ham.resolve_left ha0).resolve_left ham2,⟨ha0,ham2⟩,hveq⟩
        rcases hcls with hrep | huw
        · obtain ⟨S2,hl2,hs2⟩:=(qF hl1 hs1').1 hrep
          exact ⟨k1,t1,S2,by simp only [List.length_cons];omega,by omega,ht1lo,by omega,hl2,hs2⟩
        · obtain ⟨k2,t2,S2,hk2,ht2lo,ht2,hsum2,hl2,hs2⟩:=(qF hl1 hs1').2.2 huw
          exact ⟨k2,t2,S2,by simp only [List.length_cons];omega,by omega,by omega,by omega,hl2,hs2⟩
      · rw [if_neg hun] at hsub ⊢
        exact ih bankM hlive hsub
  · rw [if_neg hcond] at hsub ⊢
    exact ih bankM hlive hsub
abbrev qc:=Nat × Nat × List Word × List (Word × Word × Word)
abbrev k6:=qc → Bool
def y4 (q4 : Bool) (target : Word) (state : qc) (bound : q2) : Bool :=
 let (cut,stock,qY,y0,goal):=bound
 let (q8,nots,ws,history):=state
 let lower1Eff:=min y0 (qY+1)
 let maxLower :=
  if nots==1 then lower1Eff
  else if q4 then max qY lower1Eff
  else qY
 let nl:=if nots==0&&q4 then 1 else 0
 (target&&&cut)==goal&&goal != 0&&goal != cut &&
  qq (q8 - z5 cut ws) (fun yX =>
   if Nat.blt yX maxLower then
    jU (zC cut stock ws) (fun start =>
     if Nat.blt (start.length+yX) maxLower then
      jU (zc cut stock history start) (fun needed =>
       if Nat.blt (needed.length+yX) maxLower then
        let res:=qd cut needed history.reverse stock nl
        jU res.1 (fun replay =>
         let effLower:=if nots==1||res.2 != 0 then lower1Eff else qY
         Nat.blt (replay.length+yX) effLower &&
          ws.all (fun w=>qC cut (replay ++ stock) (w&&&cut)))
       else false)
     else false)
   else false)
def k5 (q4 : Bool) (target : Word) (bounds : List q2) (state : qc) : Bool :=
 List.rec false (fun bound _ later=>y4 q4 target state bound||later) bounds
def zZ (mask target : Word) (state : qc) : Prop :=
 state.2.2.1.Nodup ∧ ∃ k,k ≤ state.1 ∧ qf mask target k state.2.1 state.2.2.1.toFinset
theorem q0i {q4 : Bool} {mask target : Word}
 {state : qc} {bound : q2}
 (h0 : qo bound.1 bound.2.1 bound.2.2.2.2 0 bound.2.2.1)
 (h1 : qo bound.1 bound.2.1 bound.2.2.2.2 1 bound.2.2.2.1)
 (submask : mask&&&bound.1=bound.1)
 (stockM : ∀ w ∈ bound.2.1,qm bound.1 w)
 (hnots : state.2.1 ≤ 1)
 (j6 : zZ mask target state) :
 y4 q4 target state bound=false:=by
 rcases state with ⟨q8,nots,ws,history⟩
 rcases bound with ⟨cut,stock,qY,y0,goal⟩
 dsimp only at h0 h1 submask stockM hnots j6
 obtain ⟨nd,k,hk,y1⟩:=j6
 change ws.Nodup at nd
 change k ≤ q8 at hk
 change qf mask target k nots ws.toFinset at y1
 apply Bool.eq_false_iff.mpr
 intro hc
 unfold y4 at hc
 dsimp only at hc
 generalize hmax : (if nots==1 then min y0 (qY+1) else if q4=true then max qY (min y0 (qY+1)) else qY)=maxL at hc
 generalize hnl : (if nots==0&&q4 then 1 else 0)=nl at hc
 simp only [zG,wm,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,Nat.blt_eq] at hc
 obtain ⟨⟨⟨goalEq,nz⟩,nf⟩,scan⟩:=hc
 split at scan <;> try contradiction
 split at scan <;> try contradiction
 split at scan <;> try contradiction
 rcases Bool.and_eq_true_iff.mp scan with ⟨hlen,hsrc⟩
 rw [Nat.blt_eq] at hlen
 have hpg : qi cut (target&&&cut):=by rw [goalEq];exact ⟨nz,nf⟩
 obtain ⟨k',t',S',hlive',ht',hcard',hsub'⟩:=q2E submask hpg y1
 rw [← q2o cut nd] at hcard'
 let res:=qd cut (zc cut stock history (zC cut stock ws)) history.reverse stock nl
 have hS'mem : ∀ v ∈ S',v ∈ res.1 ++ stock:=by
  intro v hv
  obtain ⟨w,hw,rfl⟩:=hsub' v hv
  have hav:=jn.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
  have hpv:=jK hlive' (w&&&cut) hv
  exact (hav.resolve_left hpv.1).resolve_left hpv.2
 rw [goalEq] at hlive'
 obtain ⟨k2,t2,S2,hk2,huLe,ht2lo,ht2,hlive2,hsub2⟩:=q3g stockM hlive' hS'mem
 have hS2av : ∀ w ∈ S2,z4 cut stock w:=fun w hw=>Or.inr (Or.inr (hsub2 w hw))
 change res.1.length+(q8 - z5 cut ws) < (if (nots==1||res.2 != 0)=true then min y0 (qY+1) else qY) at hlen
 change res.2 ≤ nl at huLe
 change k2+(t'+res.2 - t2) ≤ k'+res.1.length at hk2
 change t2 ≤ t'+res.2 at ht2
 by_cases hn1 : nots=1
 · subst hn1
   have hnl0 : nl=0:=by rw [← hnl];rfl
   have hu0 : res.2=0:=by omega
   simp only [beq_self_eq_true,Bool.true_or, ↓reduceIte] at hlen
   have ht2' : t2=t':=by omega
   rw [ht2'] at hlive2
   have hcases : t'=0 ∨ t'=1:=by omega
   rcases hcases with rfl | rfl
   · have hl:=h0 k2 S2 hlive2 hS2av
     have : min y0 (qY+1) ≤ qY+1:=Nat.min_le_right _ _
     omega
   · have hl:=h1 k2 S2 hlive2 hS2av
     have : min y0 (qY+1) ≤ y0:=Nat.min_le_left _ _
     omega
 · have hn0 : nots=0:=by omega
   subst hn0
   have ht'0 : t'=0:=by omega
   subst ht'0
   by_cases hu0 : res.2=0
   · simp only [hu0,bne_self_eq_false,Bool.or_false,beq_iff_eq,zero_ne_one, ↓reduceIte] at hlen
     have ht20 : t2=0:=by omega
     subst ht20
     have hl:=h0 k2 S2 hlive2 hS2av
     omega
   · have hbne : (res.2 != 0)=true:=bne_iff_ne.mpr hu0
     simp only [hbne,Bool.or_true, ↓reduceIte] at hlen
     have hnlLe : nl ≤ 1:=by rw [← hnl];cases q4 <;> decide
     have hu1 : res.2=1:=by omega
     have ht2c : t2=0 ∨ t2=1:=by omega
     rcases ht2c with rfl | rfl
     · have hl:=h0 k2 S2 hlive2 hS2av
       have : min y0 (qY+1) ≤ qY+1:=Nat.min_le_right _ _
       omega
     · have hl:=h1 k2 S2 hlive2 hS2av
       have : min y0 (qY+1) ≤ y0:=Nat.min_le_left _ _
       omega
theorem q0h {q4 : Bool} {mask target : Word}
  {bounds : List q2} {state : qc}
  (q63 : qu bounds)
  (q20 : ∀ b ∈ bounds,mask&&&b.1=b.1)
  (q41 : ∀ b ∈ bounds, ∀ w ∈ b.2.1,qm b.1 w)
  (hnots : state.2.1 ≤ 1)
  (j6 : zZ mask target state) :
  k5 q4 target bounds state=false:=by
 induction bounds with
 | nil=>rfl
 | cons b bs ih =>
  change (y4 q4 target state b ||
   k5 q4 target bs state)=false
  have hb:=q63 b List.mem_cons_self
  rw [q0i hb.1 hb.2 (q20 b List.mem_cons_self)
   (q41 b List.mem_cons_self) hnots j6]
  exact ih (fun x hx=>q63 x (List.mem_cons_of_mem _ hx))
   (fun x hx=>q20 x (List.mem_cons_of_mem _ hx))
   (fun x hx=>q41 x (List.mem_cons_of_mem _ hx))
theorem q7U (w : Nat) (l : List Nat) : yJ w l < 2 ^ l.length:=by
 induction l with
 | nil=>simp [yJ]
 | cons r rs ih =>
  change (((w>>>r)&&&1)|||(yJ w rs<<<1)) < 2 ^ (rs.length+1)
  have hb : ((w>>>r)&&&1) < 2:=by
   rw [show (1 : Nat)=2 ^ 1 - 1 from rfl,Nat.and_two_pow_sub_one_eq_mod,Nat.pow_one]
   exact Nat.mod_lt _ (by decide)
  have heq : (((w>>>r)&&&1)|||(yJ w rs<<<1))=((w>>>r)&&&1)+2*yJ w rs:=by
   apply Nat.eq_of_testBit_eq;intro j
   rw [Nat.testBit_or,Nat.testBit_shiftLeft]
   cases j with
   | zero =>
    simp [Nat.testBit_zero,Nat.add_mod,Nat.mul_mod_right]
   | succ j =>
    have h0 : ((w>>>r)&&&1).testBit (j+1)=false :=
     Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (n:=2) (by decide) (show 1 ≤ j+1 by omega)))
    have hd : (((w>>>r)&&&1)+2*yJ w rs) / 2=yJ w rs:=by
     have : ((w>>>r)&&&1) / 2=0:=Nat.div_eq_of_lt hb
     rw [Nat.add_mul_div_left _ _ (by decide),this,Nat.zero_add]
    rw [h0,Bool.false_or,Nat.testBit_succ,hd];simp
  rw [heq,Nat.pow_succ,Nat.add_comm]
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hb _) (by
   rw [Nat.mul_comm 2, ← Nat.succ_mul];exact Nat.mul_le_mul_right 2 ih)
theorem wP (chart : qw) (w : Word) {i : Nat} (hi : 24 ≤ i) :
  (zy chart w).testBit i=false:=by
 have hlt : zy chart w < 2 ^ 24:=by
  simpa [zy,chart.property] using q7U w chart.val
 exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hi))
theorem q7c (chart : qw) (a b : Word) :
 zy chart (a&&&b)=zy chart a&&&zy chart b:=by
 apply Nat.eq_of_testBit_eq;intro i
 by_cases hi : i < 24
 · rw [Nat.testBit_and,yt chart _ hi,yt chart _ hi,yt chart _ hi,Nat.testBit_and]
 · simp [Nat.testBit_and,wP chart _ (Nat.le_of_not_lt hi)]
theorem q7T (chart : qw) (a b : Word) :
 zy chart (a|||b)=zy chart a|||zy chart b:=by
 apply Nat.eq_of_testBit_eq;intro i
 by_cases hi : i < 24
 · rw [Nat.testBit_or,yt chart _ hi,yt chart _ hi,yt chart _ hi,Nat.testBit_or]
 · simp [Nat.testBit_or,wP chart _ (Nat.le_of_not_lt hi)]
theorem q5P {goal : Word} {chart : qw} (ok : jD goal chart) :
 zy chart goal=4095:=by
 apply Nat.eq_of_testBit_eq;intro i
 rw [q0.wt]
 by_cases hi : i < 24
 · rw [yt chart goal hi]
   by_cases h12 : i < 12
   · simp [h12,q0P ok h12]
   · have hsub : i=12+(i - 12):=by omega
     have hneg:=q0Q ok (show i - 12 < 12 by omega)
     rw [← hsub] at hneg
     simp [h12,hneg]
 · simp [wP chart goal (Nat.le_of_not_lt hi),show ¬ i < 12 by omega]
theorem q2Q {mask goal : Word} {chart : qw} (ok : jD goal chart)
 {k : Nat} {S : Finset Word} (y1 : qf mask goal k 0 S) :
 ∃ k' S',k' ≤ k ∧ S' ⊆ S.image (zy chart) ∧ q0.vt false S' k':=by
 let f:=zy chart
 have step : ∀ {k t : Nat} {S : Finset Word},qf mask goal k t S → t=0 →
  ∃ k' S',k' ≤ k ∧ S' ⊆ S.image f ∧ q0.vt false S' k':=by
  intro k t S h
  induction h using qf.ind with
  | stop _ =>
   intro _
   refine ⟨0,{4095},Nat.le_refl _, ?_,rfl⟩
   dsimp only [f];rw [Finset.image_singleton,q5P ok]
  | unary _ _ _ _=>intro ht;omega
  | @binary k t U a b d _ _ _ _ tail ih =>
   intro ht
   obtain ⟨k',S',hk',hsub,hR⟩:=ih ht
   let z:=qj d a b
   let T:=(insert a (insert b U)).image f
   have hfz : f z=qj d (f a) (f b):=by cases d;exact q7c chart a b;exact q7T chart a b
   have hUsub : U.image f ⊆ T:=Finset.image_subset_image (fun x hx=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
   by_cases hmem : f z ∈ S'
   · by_cases hinT : f z ∈ T
     · refine ⟨k',S',by omega, ?_,hR⟩
       intro x hx;have h1:=hsub hx;rw [Finset.image_insert] at h1
       rcases Finset.mem_insert.mp h1 with rfl | hxU
       · exact hinT
       · exact hUsub hxU
     · let U':=S'.erase (f z)
       have hU'sub : U' ⊆ T:=by
        intro x hx;obtain ⟨hne,hxS⟩:=Finset.mem_erase.mp hx
        have h1:=hsub hxS;rw [Finset.image_insert] at h1
        exact hUsub ((Finset.mem_insert.mp h1).resolve_left hne)
       let S2:=insert (f a) (insert (f b) U')
       have hfaT : f a ∈ T:=Finset.mem_image_of_mem f (Finset.mem_insert_self a _)
       have hfbT : f b ∈ T:=Finset.mem_image_of_mem f (Finset.mem_insert_of_mem (Finset.mem_insert_self b U))
       have hS2sub : S2 ⊆ T:=by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hfaT
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hfbT
        · exact hU'sub hx
       have hfab : f a ≠ f b:=by
        intro eq;apply hinT;rw [hfz,eq];cases d <;> simpa [qj] using hfbT
       have hfnot : f z ∉ S2:=fun hm=>hinT (hS2sub hm)
       refine ⟨k'+1,S2,by omega,hS2sub,Or.inr ⟨f a,f b,f z,decide (f a ∈ U'),decide (f b ∈ U'),
        Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
        by rw [hfz];cases d <;> simp [qj], ?_,trivial, ?_⟩⟩
       · intro x hx
         simp only [q0.blk,cond_false]
         apply Bool.eq_false_iff.mpr
         intro eq;exact hfnot ((Nat.beq_eq.mp eq) ▸ hx)
       · have hf : S2.filter (fun x=>(decide (f a ∈ U')=true ∨ x ≠ f a) ∧ (decide (f b ∈ U')=true ∨ x ≠ f b))=U':=by
          ext x;rw [Finset.mem_filter]
          by_cases ha : x=f a
          · subst x;simp [S2,hfab]
          by_cases hb : x=f b
          · subst x;simp [S2,hfab.symm]
          simp [S2,ha,hb]
         rw [hf,Finset.insert_erase hmem]
         exact hR
   · refine ⟨k',S',by omega, ?_,hR⟩
     intro x hx;have hne : x ≠ f z:=fun eq=>hmem (eq ▸ hx)
     have h1:=hsub hx;rw [Finset.image_insert] at h1
     exact hUsub ((Finset.mem_insert.mp h1).resolve_left hne)
 exact step y1 rfl
theorem wf {q : Nat} {xs : List Nat}
 (hp : xs.Pairwise (fun a b => ¬ ((q0.qD a).testBit q=true ∧ (q0.qD b).testBit q=true)))
 {u v : Nat} (hu : u ∈ xs) (hv : v ∈ xs) (huv : u ≠ v) :
 ¬ ((q0.qD u).testBit q=true ∧ (q0.qD v).testBit q=true):=by
 induction hp with
 | nil=>simp at hu
 | @cons x xs hx _ ih =>
  rcases List.mem_cons.mp hu with hu1 | hu2 <;> rcases List.mem_cons.mp hv with hv1 | hv2
  · exact absurd (hu1.trans hv1.symm) huv
  · rw [hu1];exact hx v hv2
  · rw [hv1];intro ⟨h1,h2⟩;exact hx u hu2 ⟨h2,h1⟩
  · exact ih hu2 hv2
theorem q9l {q : Nat} {l' l : List Nat} (hnd' : l'.Nodup) (hsub : ∀ x ∈ l',x ∈ l)
 (h : (q0.tw (l'.map q0.qD) 0 0).testBit q=true) :
 (q0.tw (l.map q0.qD) 0 0).testBit q=true:=by
 by_contra hfalse
 have hf : (q0.tw (l.map q0.qD) 0 0).testBit q=false:=by
  cases hb : (q0.tw (l.map q0.qD) 0 0).testBit q <;> simp_all
 have hpwL:=List.pairwise_map.mp (q0.q40 q (l.map q0.qD) 0 0 hf).2.2
 have hpw' : l'.Pairwise (fun x y => ¬ ((q0.qD x).testBit q=true ∧ (q0.qD y).testBit q=true)) :=
  List.Pairwise.imp_of_mem (fun {a b} ha hb hab=>wf hpwL (hsub a ha) (hsub b hb) hab) hnd'
 have hzero : ∀ (xs : List Nat) (o t : Nat),
  t.testBit q=false →
  (o.testBit q=true → ∀ x ∈ xs,(q0.qD x).testBit q=false) →
  xs.Pairwise (fun x y => ¬ ((q0.qD x).testBit q=true ∧ (q0.qD y).testBit q=true)) →
  (q0.tw (xs.map q0.qD) o t).testBit q=false:=by
  intro xs
  induction xs with
  | nil=>intro o t ht _ _;exact ht
  | cons x xs ih =>
   intro o t ht ho hpx
   obtain ⟨hx,hxs⟩:=List.pairwise_cons.mp hpx
   apply ih (Nat.lor o (q0.qD x)) (Nat.lor t (Nat.land o (q0.qD x)))
   · rw [q0.qX,Bool.or_eq_false_iff,q0.qM]
     refine ⟨ht, ?_⟩
     cases hox : o.testBit q
     · simp
     · simp [ho hox x List.mem_cons_self]
   · intro hox y hy
     rw [q0.qX,Bool.or_eq_true] at hox
     rcases hox with h1 | h2
     · exact ho h1 y (List.mem_cons_of_mem _ hy)
     · cases hry : (q0.qD y).testBit q
       · rfl
       · exact False.elim (hx y hy ⟨h2,hry⟩)
   · exact hxs
 have hc:=hzero l' 0 0 (by simp) (by simp) hpw'
 rw [hc] at h
 exact Bool.noConfusion h
theorem q70 {a b q : Nat} (hsub : ∀ r < 144,a.testBit r=true → b.testBit r=true)
  (hq : (q0.vN a).testBit q=true) : (q0.vN b).testBit q=true:=by
 have landM {x y m : Nat} (h : ∀ r,x.testBit r=true → y.testBit r=true) :
   ∀ r,(Nat.land x m).testBit r=true → (Nat.land y m).testBit r=true:=by
  intro r hr;rw [q0.qM,Bool.and_eq_true] at hr ⊢;exact ⟨h r hr.1,hr.2⟩
 have orSM {x y s : Nat} (h : ∀ r,x.testBit r=true → y.testBit r=true) :
   ∀ r,(q0.orS x s).testBit r=true → (q0.orS y s).testBit r=true:=by
  intro r hr;rw [q0.q9E,Bool.or_eq_true] at hr ⊢;exact hr.imp (h r) (h (s+r))
 have orSLM {x y s : Nat} (h : ∀ r,x.testBit r=true → y.testBit r=true) :
   ∀ r,(q0.q2e x s).testBit r=true → (q0.q2e y s).testBit r=true:=by
  intro r hr;rw [q0.q8V,Bool.or_eq_true,Bool.and_eq_true] at hr ⊢
  exact hr.imp (h r) (fun ⟨h1,h2⟩=>⟨h1,h (r - s) h2⟩)
 have h1 : ∀ r,(Nat.land a q0.qp).testBit r=true → (Nat.land b q0.qp).testBit r=true:=by
  intro r hr
  rw [q0.qM,q0.jZ,Bool.and_eq_true,decide_eq_true_eq] at hr ⊢
  exact ⟨hsub r hr.2 hr.1,hr.2⟩
 have hR:=orSLM (orSLM (orSLM (orSLM (landM (orSM (orSM (orSM (orSM h1 (s:=6)) (s:=3)) (s:=1)) (s:=1)) (m:=q0.q6G)) (s:=6)) (s:=3)) (s:=1)) (s:=1)
 have hC:=orSLM (orSLM (orSLM (orSLM (landM (orSM (orSM (orSM (orSM h1 (s:=96)) (s:=48)) (s:=24)) (s:=12)) (m:=4095)) (s:=96)) (s:=48)) (s:=24)) (s:=12)
 unfold q0.vN q0.q0a q0.vZ q0.ua at hq ⊢
 rw [q0.qM,Bool.and_eq_true] at hq ⊢
 exact ⟨hR q hq.1,hC q hq.2⟩
def yY (l : List Word) : Nat :=
 let rs:=q0.q8i' l
 let t:=q0.tw' rs 0 0
 (rs.filter (fun r => !Nat.beq (Nat.land (Nat.land r (Nat.xor t q0.qp)) q0.qp) 0)).length
def qL (mask q5 : Nat) (state : qc) : Option qc :=
 let (q8,nots,ws,history):=state
 let keep:=q5 % 4
 let op:=(q5 / 4) % 3
 let a:=q5 / (4*3*64)
 let b:=(q5 / (4*3)) % 64
 if q8==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b) then none
 else
  let x:=ws.getD a 0
  let y:=ws.getD b 0
  let w:=if op==0 then x&&&y else if op==1 then x|||y else mask^^^x
  if w==0||w==mask||ws.contains w then none
  else
   let rest:=if keep.testBit 0 then ws else ws.erase x
   let rest:=if op==2||keep.testBit 1 then rest else rest.erase y
   let zJ:=if op==2 then nots - 1 else nots
   some (q8 - 1,zJ,qB w rest,(w,x,y) :: history)
def zO (base : List Word) (q8 q9 q5 : Nat) : qc :=
 (q8,q9,yW base q5,[])
def jr (mask : Word) (stock : List Word) (q8 q9 : Nat) (q3 : zj)
  (i : Nat) : Option qc :=
 (Nat.rec (motive:=fun _=>Nat → Option qc) (fun _=>none)
  (fun _ previous j =>
   let (qz,q5):=q3 j
   if qz==0 then
    if q5 < 2 ^ stock.length then some (zO stock q8 q9 q5) else none
   else (previous (qz - 1)).bind (qL mask q5)) (q8+1)) i
abbrev jo:=Nat × Nat
def zF (qJ : Bool) (ws : List Word) : Word → Word → Bool :=
 List.rec
  (fun p n=>Nat.beq p 0||Nat.beq n 0)
  (fun w _ rest p n =>
   Nat.beq p 0||Nat.beq n 0 ||
   qq (p&&&w) (fun up =>
    qq (n&&&w) (fun down =>
     rest up down &&
      qq (p^^^up) (fun offP =>
       qq (if qJ then n else n^^^down) (rest offP))))) ws
theorem q3d {v w : Word} {i : Nat} (bit : (v^^^(v&&&w)).testBit i=true) :
  v.testBit i=true ∧ w.testBit i=false:=by
 rw [Nat.testBit_xor,Nat.testBit_and] at bit
 cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv,hw] at bit ⊢
theorem q1Q {qJ : Bool} {ws : List Word} {positive negative : Word}
 (fail : zF qJ ws positive negative=false) :
 ∃ p n,positive.testBit p=true ∧ negative.testBit n=true ∧
  ∀ w ∈ ws,if qJ then w.testBit p=true → w.testBit n=true
   else w.testBit p=w.testBit n:=by
 have nonempty {w : Word} (hn : w ≠ 0) : ∃ j,w.testBit j=true:=by
  by_contra! all;apply hn;apply Nat.eq_of_testBit_eq;intro i;simp [all i]
 induction ws generalizing positive negative with
 | nil =>
  change (Nat.beq positive 0||Nat.beq negative 0)=false at fail
  simp only [Bool.or_eq_false_iff] at fail
  obtain ⟨p,hp⟩:=nonempty (w:=positive) (fun eq=>by simp [eq] at fail)
  obtain ⟨n,hn⟩:=nonempty (w:=negative) (fun eq=>by simp [eq] at fail)
  exact ⟨p,n,hp,hn,by simp⟩
 | cons w ws ih =>
  change (Nat.beq positive 0||Nat.beq negative 0 ||
   qq (positive&&&w) (fun up =>
    qq (negative&&&w) (fun down =>
     zF qJ ws up down &&
      qq (positive^^^up) (fun offP =>
       qq (if qJ then negative else negative^^^down)
        (zF qJ ws offP)))))=false at fail
  simp only [zG,Bool.or_eq_false_iff,Bool.and_eq_false_iff] at fail
  rcases fail.2 with on | off
  · obtain ⟨p,n,hp,hn,agree⟩:=ih on
    rw [Nat.testBit_and,Bool.and_eq_true] at hp hn
    refine ⟨p,n,hp.1,hn.1, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | tail
    · simp [hp.2,hn.2]
    · exact agree _ tail
  · obtain ⟨p,n,hp,hn,agree⟩:=ih off
    have hp':=q3d hp
    cases mode : qJ
    · have hn' : negative.testBit n=true ∧ w.testBit n=false:=by
       apply q3d;simpa [mode] using hn
      refine ⟨p,n,hp'.1,hn'.1, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp'.2,hn'.2]
      · simpa [mode] using agree _ tail
    · have hn' : negative.testBit n=true:=by simpa [mode] using hn
      refine ⟨p,n,hp'.1,hn', ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp'.2]
      · simpa [mode] using agree _ tail
theorem uZ {mask goal : Word} {ws : List Word} {k t : Nat} {qJ : Bool}
  (vh : qm mask goal) (y1 : qf mask goal k t ws.toFinset)
  (noNot : qJ=true → t=0) :
  zF qJ ws goal (mask^^^goal)=true:=by
 by_contra fail
 have openPair : zF qJ ws goal (mask^^^goal)=false:=by
  cases h : zF qJ ws goal (mask^^^goal) <;> simp_all
 obtain ⟨p,n,hp,hn,agree⟩:=q1Q openPair
 have pm:=kU vh hp
 have nm : mask.testBit n=true ∧ goal.testBit n=false:=by
  rw [Nat.testBit_xor] at hn
  have implied:=fun ht : goal.testBit n=true=>kU vh ht
  cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
 cases mode : qJ with
 | false =>
  have same:=q1D y1 (pm.trans nm.1.symm) (fun w hw=>by
   simpa [mode,jV] using agree w (List.mem_toFinset.mp hw))
  simp [jV,hp,nm.2] at same
 | true =>
  have ht:=noNot mode
  subst t
  obtain ⟨w,hw,a,b⟩:=q2f y1 hp nm.2
  have same:=agree w (List.mem_toFinset.mp hw)
  simp [mode,a,b] at same
abbrev qH:=Nat × Nat
abbrev qU:=Word × Word
abbrev wS:=Word × Word × Word
abbrev qb:=Word × qU
def uQ (tags : List qU) (use : List qU → Bool) : Bool :=
 (List.rec (motive:=fun _=>(List qU → Bool) → Bool) (fun k=>k [])
  (fun tag _ next k =>
   qq tag.1 (fun up=>qq tag.2 (fun down =>
    next (fun tail=>k ((up,down) :: tail))))) tags) use
theorem q35 (tags : List qU) (use : List qU → Bool) :
  uQ tags use=use tags:=by
 induction tags generalizing use with
 | nil=>rfl
 | cons tag rest ih =>
  obtain ⟨a,b⟩:=tag
  change qq a (fun up=>qq b (fun down =>
   uQ rest (fun tail=>use ((up,down) :: tail))))=_
  simp only [zG,ih]
def zg (mask op x y : Word) : Word :=
 if Nat.beq op 0 then x&&&y else if Nat.beq op 1 then x|||y else mask^^^x
def zk (stock : List Word) (positive negative qV : Nat) : List qb :=
 (List.rec (motive:=fun _=>Nat → List qb) (fun _=>[])
  (fun w _ next i=>(w,z3 positive qV i,z3 negative qV i) :: next (i+1)) stock) 0
theorem q3e {ws : List Word} {x w : Word} {keep : Bool}
 (nd : ws.Nodup) (h : w ∈ zu keep x ws) : w ∈ ws ∧ (keep=true ∨ w ≠ x):=by
 cases keep
 · simpa [zu,nd.mem_erase_iff,and_comm] using h
 · simpa [zu] using h
def zE (n op keep : Nat) : Nat :=
 (n - (if keep.testBit 0 then 0 else 1) -
  (if op==2||keep.testBit 1 then 0 else 1))+1
def yg (ws : List Word) (op keep x y : Nat) : List Word :=
 zu (op==2||keep.testBit 1) y (zu (keep.testBit 0) x ws)
def u8 (mask : Word) (state : qc) (a b op keep x y out : Nat) : Option qc :=
 let (q8,nots,ws,history):=state
 if q8==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b) then none
 else if out==0||out==mask||ws.contains out then none
 else
  let zJ:=if op==2 then nots - 1 else nots
  some (q8 - 1,zJ,qB out (yg ws op keep x y),(out,x,y) :: history)
theorem jC {mask a b op keep : Nat} {state : qc}
  (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
  let x:=state.2.2.1.getD a 0
  let y:=state.2.2.1.getD b 0
  u8 mask state a b op keep x y (zg mask op x y) =
   qL mask (zl a b op keep) state:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 obtain ⟨keepEq,opEq,aEq,bEq⟩:=u5 (a:=a) hb hop hk
 simp only [qL,u8,yg,zu,keepEq,opEq,aEq,bEq,zg]
 cases op with
 | zero=>rfl
 | succ op=>cases op <;> rfl
def u9 (witnesses : List zW) (ws : List Word) : Bool :=
 witnesses.all (fun kt=>ws.contains (q0j kt))
def q6l (mask : Nat) (state child : qc) : Prop :=
 ∃ a b op keep,a < state.2.2.1.length ∧
  ((a=b ∧ op=2 ∧ keep < 2 ∧ state.2.1 ≠ 0) ∨
   (a < b ∧ b < state.2.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
  qL mask (zl a b op keep) state=some child
theorem q5b {mask target : Word} {state : qc}
 (qV : state.2.2.1.length ≤ 64) (j6 : zZ mask target state) :
 (state.2.1=0 ∧ target ∈ state.2.2.1) ∨
  ∃ child,q6l mask state child ∧ zZ mask target child ∧ child.2.1 ≤ state.2.1:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 change ws.length ≤ 64 at qV
 obtain ⟨nd,k,cap,y1⟩:=j6
 change k ≤ q8 at cap
 change qf mask target k nots ws.toFinset at y1
 cases k with
 | zero =>
  left
  obtain ⟨ht0,eq,_⟩:=y1
  exact ⟨ht0,List.mem_toFinset.mp (by rw [eq];simp)⟩
 | succ k =>
  right
  rcases y1 with ⟨u,U,x,rfl,eq,px,jB,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,jB,tail⟩
  · let a:=ws.idxOf x
    have xm : x ∈ ws:=by rw [← List.mem_toFinset,eq];simp
    have ha : a < ws.length:=List.idxOf_lt_length_iff.mpr xm
    have hx : ws.getD a 0=x:=q2m xm
    have p:=jK tail (mask^^^x) (Finset.mem_insert_self _ _)
    let save:=decide (x ∈ U)
    let keep:=if save then 1 else 0
    have keepLt : keep < 2:=by dsimp [keep];split <;> decide
    have keepBit : keep.testBit 0=save:=by unfold keep;cases save <;> decide
    have fn : mask^^^x ∉ ws:=by simpa [← List.mem_toFinset,eq] using jB
    let rest:=zu save x ws
    let child : qc:=(q8 - 1,u,qB (mask^^^x) rest,(mask^^^x,x,x) :: history)
    obtain ⟨ke,op,aa,bb⟩:=u5 (a:=a) (show a < 64 by omega) (by decide : 2 < 3) (by omega : keep < 4)
    have heval : qL mask (zl a a 2 keep) (q8,u+1,ws,history)=some child:=by
     simp only [qL,ke,op,aa,bb,hx,keepBit]
     simp [show q8 ≠ 0 by omega,Nat.not_le_of_lt ha,Nat.not_le_of_lt keepLt,p.1,p.2,fn,zu,child,rest]
    refine ⟨child,⟨a,a,2,keep,ha,Or.inl ⟨rfl,rfl,keepLt,Nat.succ_ne_zero u⟩,heval⟩, ?_,by change u ≤ u+1;omega⟩
    refine ⟨q09 (wg nd save x) (fun h=>fn (uy save x ws _ h)),k,by change k ≤ q8 - 1;omega, ?_⟩
    change qf mask target k u (qB (mask^^^x) rest).toFinset
    rw [w8,q6S nd eq]
    exact tail
  · have doBin (x y : Word) (d : Bool) (eq : ws.toFinset=insert x (insert y U))
     (xy : x ≠ y) (ordered : ws.idxOf x < ws.idxOf y)
     (jB : qj d x y ∉ insert x (insert y U))
     (tail : qf mask target k nots (insert (qj d x y) U)) :
     ∃ child,q6l mask (q8,nots,ws,history) child ∧ zZ mask target child ∧ child.2.1 ≤ nots:=by
     let a:=ws.idxOf x
     let b:=ws.idxOf y
     have xm : x ∈ ws:=by rw [← List.mem_toFinset,eq];simp
     have ym : y ∈ ws:=by rw [← List.mem_toFinset,eq];simp
     have ha : a < ws.length:=List.idxOf_lt_length_iff.mpr xm
     have hb : b < ws.length:=List.idxOf_lt_length_iff.mpr ym
     have hx : ws.getD a 0=x:=q2m xm
     have hy : ws.getD b 0=y:=q2m ym
     let v:=qj d x y
     have p:=jK tail v (Finset.mem_insert_self _ _)
     let saveA:=decide (x ∈ U)
     let saveB:=decide (y ∈ U)
     let keep:=(if saveA then 1 else 0)+(if saveB then 2 else 0)
     have keepLt : keep < 4:=by dsimp [keep];split <;> split <;> decide
     have kb0 : keep.testBit 0=saveA:=by dsimp [keep];cases saveA <;> cases saveB <;> decide
     have kb1 : keep.testBit 1=saveB:=by dsimp [keep];cases saveA <;> cases saveB <;> decide
     have fn : v ∉ ws:=by simpa [← List.mem_toFinset,eq] using jB
     let rest:=zu saveB y (zu saveA x ws)
     let opN:=if d then 1 else 0
     have hop : opN < 2:=by dsimp [opN];cases d <;> decide
     obtain ⟨ke,op,aa,bb⟩:=u5 (a:=a) (show b < 64 by omega) (by omega : opN < 3) keepLt
     let child : qc:=(q8 - 1,nots,qB v rest,(v,x,y) :: history)
     have heval : qL mask (zl a b opN keep) (q8,nots,ws,history)=some child:=by
      have habLt : a < b:=ordered
      simp only [qL,ke,op,aa,bb,hx,hy,kb0,kb1]
      cases d <;> (
       simp only [v,qj, ↓reduceIte,Bool.false_eq_true] at p fn
       simp [opN,show q8 ≠ 0 by omega,habLt,Nat.not_le_of_lt hb,zu,qj,p.1,p.2,fn,child,rest,v])
     refine ⟨child,⟨a,b,opN,keep,ha,Or.inr ⟨ordered,hb,hop,keepLt⟩,heval⟩, ?_,Nat.le_refl _⟩
     refine ⟨q09 (wg (wg nd saveA x) saveB y)
      (fun h=>fn (uy saveA x ws _ (uy saveB y _ _ h))),
      k,by change k ≤ q8 - 1;omega, ?_⟩
     change qf mask target k nots (qB v rest).toFinset
     rw [w8,q7u nd xy eq]
     exact tail
    have xm : x ∈ ws:=by rw [← List.mem_toFinset,eq];simp
    have ym : y ∈ ws:=by rw [← List.mem_toFinset,eq];simp
    have diff : ws.idxOf x ≠ ws.idxOf y:=by
     intro same;apply xy;rw [← q2m xm,same,q2m ym]
    by_cases hord : ws.idxOf x < ws.idxOf y
    · exact doBin x y d eq xy hord jB tail
    · exact doBin y x d (by rw [eq,Finset.insert_comm]) xy.symm (by omega)
       (by rw [uk d y x,Finset.insert_comm];exact jB)
       (by rw [uk d y x];exact tail)
theorem uc {mask a b op keep x y out : Nat} {state child : qc}
 (h : u8 mask state a b op keep x y out=some child) :
 child.2.1=(if op==2 then state.2.1 - 1 else state.2.1) ∧
 (out==0||out==mask||state.2.2.1.contains out)=false:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 let bad : Bool:=q8==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
 let stale : Bool:=out==0||out==mask||ws.contains out
 change (if bad then none else if stale then none else
  some (q8 - 1,if op==2 then nots - 1 else nots,qB out (yg ws op keep x y),(out,x,y) :: history))=some child at h
 by_cases h1 : bad=true
 · simp [h1] at h
 by_cases h2 : stale=true
 · simp [h1,h2] at h
 have heq : (q8 - 1,if op==2 then nots - 1 else nots,qB out (yg ws op keep x y),(out,x,y) :: history)=child:=by
  simpa [h1,h2] using h
 refine ⟨by rw [← heq],Bool.eq_false_iff.mpr h2⟩
theorem q3U {mask q5 : Nat} {state child : qc}
 (eval : qL mask q5 state=some child)
 (zM : ∀ w ∈ state.2.2.1,qm mask w) :
 child.1 < state.1 ∧ child.2.1 ≤ state.2.1 ∧ ∀ w ∈ child.2.2.1,qm mask w:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 let keep:=q5 % 4
 let op:=q5 / 4 % 3
 let a:=q5 / (4*3*64)
 let b:=q5 / (4*3) % 64
 let x:=ws.getD a 0
 let y:=ws.getD b 0
 let z:=if op==0 then x&&&y else if op==1 then x|||y else mask^^^x
 let rest:=zu (op==2||keep.testBit 1) y (zu (keep.testBit 0) x ws)
 let zJ:=if op==2 then nots - 1 else nots
 let bad : Bool:=q8==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
 let stale : Bool:=z==0||z==mask||ws.contains z
 change (if bad then none else if stale then none else
  some (q8 - 1,zJ,qB z rest,(z,x,y) :: history))=some child at eval
 by_cases hb : bad=true
 · simp [hb] at eval
 by_cases hs : stale=true
 · simp [hb,hs] at eval
 have eq : (q8 - 1,zJ,qB z rest,(z,x,y) :: history)=child:=by simpa [hb,hs] using eval
 subst child
 have pos : 0 < q8:=by
  by_contra! h
  have he : q8=0:=by omega
  exact hb (by simp [bad,he])
 have hnle : zJ ≤ nots:=by
  dsimp only [zJ];by_cases h : (op==2)=true <;> simp [h] <;> omega
 refine ⟨by dsimp;omega,hnle, ?_⟩
 have read (i : Nat) : z4 mask ws (ws.getD i 0):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none=>exact Or.inl rfl
  | some a=>exact Or.inr (Or.inr (List.mem_of_getElem? h))
 have hm : qm mask z:=by
  apply ux zM
  unfold z
  split
  · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
  split
  · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
  · exact Or.inl ⟨x,read _,rfl⟩
 intro w hw
 rcases vF.mp hw with rfl | other
 · exact hm
 · exact zM w (uy (keep.testBit 0) x ws w (uy (op==2||keep.testBit 1) y _ w other))
abbrev q5a (qV : Nat):=z0 × (Fin qV → Fin qV) × (Fin qV → Fin qV)
def kC : PEqualNP.CircuitLowerBounds.GateOp → Bool
 | PEqualNP.CircuitLowerBounds.GateOp.not=>true
 | _=>false
def yb (gs : List PEqualNP.CircuitLowerBounds.Gate) : Nat :=
 (gs.filter (fun g=>kC g.op)).length
theorem q5u {gs : List PEqualNP.CircuitLowerBounds.Gate}
 (h1 : ∀ i j : Fin gs.length,
  (gs.get i).op=PEqualNP.CircuitLowerBounds.GateOp.not →
  (gs.get j).op=PEqualNP.CircuitLowerBounds.GateOp.not → i=j) :
 yb gs ≤ 1:=by
 induction gs with
 | nil=>simp [yb]
 | cons g gs ih =>
  have htail : ∀ i j : Fin gs.length,
   (gs.get i).op=PEqualNP.CircuitLowerBounds.GateOp.not →
   (gs.get j).op=PEqualNP.CircuitLowerBounds.GateOp.not → i=j:=by
   intro i j hi hj
   exact Fin.succ_inj.mp (h1 i.succ j.succ hi hj)
  cases hgop : g.op with
  | not =>
   have hnone : ∀ x ∈ gs,kC x.op=false:=by
    intro x hx
    cases hxop : x.op <;> simp only [kC]
    exfalso
    obtain ⟨k,hk,rfl⟩:=List.mem_iff_getElem.mp hx
    have heq:=h1 ⟨0,by simp⟩ ⟨k+1,by simp [hk]⟩ hgop (by simpa using hxop)
    have hval:=congrArg Fin.val heq
    dsimp at hval;omega
   have hfil : gs.filter (fun x=>kC x.op)=[]:=by
    rw [List.filter_eq_nil_iff];intro x hx;simp [hnone x hx]
   have : (List.filter (fun x=>kC x.op) (g :: gs))=[g]:=by
    rw [List.filter_cons,hgop];exact congrArg (g :: ·) hfil
   simp [yb,this]
  | and=>exact by simpa [yb,hgop,kC] using ih htail
  | or=>exact by simpa [yb,hgop,kC] using ih htail
  | mod _=>exact by simpa [yb,hgop,kC] using ih htail
  | maj=>exact by simpa [yb,hgop,kC] using ih htail
theorem q3M {rows : Nat} (bank : List (BitVec rows))
 (gs : List PEqualNP.CircuitLowerBounds.Gate) (goal : Word)
 (hlegal : ∀ g ∈ gs,
  (g.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
   g.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨
   g.op=PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2)
 (hpg : qi (qI rows) goal)
 (hhit : goal ∈ (gs.foldl yK bank).map BitVec.toNat) :
 ∃ k t S,k ≤ gs.length ∧ t ≤ yb gs ∧
  qf (qI rows) goal k t S ∧ ∀ w ∈ S,w ∈ bank.map BitVec.toNat:=by
 induction gs generalizing bank with
 | nil =>
  exact ⟨0,0,{goal},Nat.le_refl _,Nat.zero_le _,qf.stop hpg,by simpa using hhit⟩
 | cons g gs ih =>
  have hg:=hlegal g List.mem_cons_self
  have hrest : ∀ g' ∈ gs,
   (g'.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
    g'.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨
    g'.op=PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g'.inputs.length ≤ 2 :=
   fun g' hg'=>hlegal g' (List.mem_cons_of_mem _ hg')
  obtain ⟨k,t,S,hk,ht,hlive,hsub⟩:=ih (yK bank g) hrest hhit
  have hstepEq : (yK bank g).map BitVec.toNat=bank.map BitVec.toNat ++ [(qN bank g).toNat]:=by
   simp [yK]
  rw [hstepEq] at hsub
  have hM : ∀ w ∈ bank.map BitVec.toNat,qm (qI rows) w:=fun w hw=>by
   obtain ⟨v,_,rfl⟩:=List.mem_map.mp hw;exact q7l v
  obtain ⟨op,ins⟩:=g
  have hop:=hg.1
  have hlen:=hg.2
  rcases hop with rfl | rfl | rfl
  · have hnc : yb (⟨.and,ins⟩ :: gs)=yb gs:=by simp [yb,kC]
    rw [hnc]
    cases ins with
    | nil =>
     have hrep : zB (qI rows) (bank.map BitVec.toNat) (qN bank ⟨.and,[]⟩).toNat :=
      Or.inr (by simp [qN,qI,qi])
     obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
     exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
    | cons a rest =>
     cases rest with
     | nil =>
      have hval : (qN bank ⟨.and,[a]⟩).toNat=(bank.getD a 0).toNat:=by simp [qN]
      have hav:=yx bank a
      have hrep : zB (qI rows) (bank.map BitVec.toNat) (qN bank ⟨.and,[a]⟩).toNat:=by
       rw [hval]
       rcases hav with h0 | hm | hmem
       · exact Or.inr (by rw [h0];exact fun h=>h.1 rfl)
       · exact Or.inr (by rw [hm];exact fun h=>h.2 rfl)
       · exact Or.inl hmem
      obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
      exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
     | cons b rest =>
      cases rest with
      | nil =>
       have hval : (qN bank ⟨.and,[a,b]⟩).toNat=qj false (bank.getD a 0).toNat (bank.getD b 0).toNat:=by
        simp [qN,qj,BitVec.toNat_and]
       rw [hval] at hsub
       rcases vq hM false (yx bank a) (yx bank b) with hrep | hbw
       · obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
         exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
       · obtain ⟨k',S',hk',hl',hs'⟩:=(qF hlive hsub).2.1 hbw
         exact ⟨k',t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
      | cons _ _=>simp at hlen
  · have hnc : yb (⟨.or,ins⟩ :: gs)=yb gs:=by simp [yb,kC]
    rw [hnc]
    cases ins with
    | nil =>
     have hrep : zB (qI rows) (bank.map BitVec.toNat) (qN bank ⟨.or,[]⟩).toNat :=
      Or.inr (by simp [qN,qi])
     obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
     exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
    | cons a rest =>
     cases rest with
     | nil =>
      have hval : (qN bank ⟨.or,[a]⟩).toNat=(bank.getD a 0).toNat:=by simp [qN]
      have hav:=yx bank a
      have hrep : zB (qI rows) (bank.map BitVec.toNat) (qN bank ⟨.or,[a]⟩).toNat:=by
       rw [hval]
       rcases hav with h0 | hm | hmem
       · exact Or.inr (by rw [h0];exact fun h=>h.1 rfl)
       · exact Or.inr (by rw [hm];exact fun h=>h.2 rfl)
       · exact Or.inl hmem
      obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
      exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
     | cons b rest =>
      cases rest with
      | nil =>
       have hval : (qN bank ⟨.or,[a,b]⟩).toNat=qj true (bank.getD a 0).toNat (bank.getD b 0).toNat:=by
        simp [qN,qj,BitVec.toNat_or]
       rw [hval] at hsub
       rcases vq hM true (yx bank a) (yx bank b) with hrep | hbw
       · obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
         exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
       · obtain ⟨k',S',hk',hl',hs'⟩:=(qF hlive hsub).2.1 hbw
         exact ⟨k',t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
      | cons _ _=>simp at hlen
  · have hnc : yb (⟨.not,ins⟩ :: gs)=yb gs+1:=by simp [yb,kC]
    rw [hnc]
    cases ins with
    | nil =>
     have hrep : zB (qI rows) (bank.map BitVec.toNat) (qN bank ⟨.not,[]⟩).toNat:=by
      have : (qN bank ⟨.not,[]⟩).toNat=qI rows:=by
       simpa [qN] using q9F (0 : BitVec rows)
      exact Or.inr (by simp [this,qi])
     obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
     exact ⟨k,t,S',by simp only [List.length_cons];omega,by omega,hl',hs'⟩
    | cons a rest =>
     have hval : (qN bank ⟨.not,a :: rest⟩).toNat=qI rows^^^(bank.getD a 0).toNat:=by
      simpa [qN] using q9F (bank.getD a 0)
     have hav:=yx bank a
     by_cases ha0 : (bank.getD a 0).toNat=0
     · have hrep : zB (qI rows) (bank.map BitVec.toNat) (qN bank ⟨.not,a :: rest⟩).toNat:=by
        right;rw [hval,ha0];simp [qi]
       obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
       exact ⟨k,t,S',by simp only [List.length_cons];omega,by omega,hl',hs'⟩
     by_cases ham : (bank.getD a 0).toNat=qI rows
     · have hself : qI rows^^^qI rows=0:=by
        apply Nat.eq_of_testBit_eq;intro i;simp
       have hrep : zB (qI rows) (bank.map BitVec.toNat) (qN bank ⟨.not,a :: rest⟩).toNat:=by
        right;rw [hval,ham,hself];simp [qi]
       obtain ⟨S',hl',hs'⟩:=(qF hlive hsub).1 hrep
       exact ⟨k,t,S',by simp only [List.length_cons];omega,by omega,hl',hs'⟩
     have hmem : (bank.getD a 0).toNat ∈ bank.map BitVec.toNat:=(hav.resolve_left ha0).resolve_left ham
     obtain ⟨k',t',S',hk',_,ht',_,hl',hs'⟩ :=
      (qF hlive hsub).2.2 ⟨(bank.getD a 0).toNat,hmem,⟨ha0,ham⟩,hval⟩
     exact ⟨k',t',S',by simp only [List.length_cons];omega,by omega,hl',hs'⟩
theorem q0f {rows : Nat} (bank : List (BitVec rows)) (goal : BitVec rows)
 {k : Nat} {S : Finset Word}
 (y1 : qf (qI rows) goal.toNat k 0 S)
 (sub : ∀ w ∈ S,w ∈ bank.map BitVec.toNat) :
 ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : Nat),
  (∀ g ∈ gs,(g.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
   g.op=PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  gs.length ≤ k ∧
  (gs.foldl yK bank).getD o 0=goal:=by
 generalize ht : (0 : Nat)=t at y1
 induction y1 using qf.ind generalizing bank with
 | stop hp =>
  have hmem : goal.toNat ∈ bank.map BitVec.toNat:=sub goal.toNat (Finset.mem_singleton_self _)
  obtain ⟨v,hv,hveq⟩:=List.mem_map.mp hmem
  have hvgoal : v=goal:=BitVec.eq_of_toNat_eq hveq
  subst hvgoal
  obtain ⟨i,hi,heq⟩:=List.mem_iff_getElem.mp hv
  refine ⟨[],i,fun _ h=>False.elim (List.not_mem_nil h),Nat.le_refl _, ?_⟩
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using heq
 | unary _ _ _ _=>exact False.elim (Nat.succ_ne_zero _ ht.symm)
 | @binary k t U a b d pa pb hab hfresh tail ih =>
  have haMem : a ∈ bank.map BitVec.toNat:=sub a (Finset.mem_insert_self a _)
  have hbMem : b ∈ bank.map BitVec.toNat:=sub b (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
  obtain ⟨va,hva,hvaEq⟩:=List.mem_map.mp haMem
  obtain ⟨vb,hvb,hvbEq⟩:=List.mem_map.mp hbMem
  obtain ⟨ia,hia,hiaEq⟩:=List.mem_iff_getElem.mp hva
  obtain ⟨ib,hib,hibEq⟩:=List.mem_iff_getElem.mp hvb
  let g : PEqualNP.CircuitLowerBounds.Gate :=
   ⟨if d then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and,[ia,ib]⟩
  have hgetA : (bank.getD ia 0).toNat=a:=by
   have : bank.getD ia 0=va:=by simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hia] using hiaEq
   rw [this,hvaEq]
  have hgetB : (bank.getD ib 0).toNat=b:=by
   have : bank.getD ib 0=vb:=by simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hib] using hibEq
   rw [this,hvbEq]
  have hval : (qN bank g).toNat=qj d a b:=by
   cases d
   · simp only [g,qN,qj,Bool.false_eq_true, ↓reduceIte,List.map_cons,List.map_nil,
      List.foldr_cons,List.foldr_nil,BitVec.and_allOnes,BitVec.toNat_and,hgetA,hgetB]
   · simp only [g,qN,qj, ↓reduceIte,List.map_cons,List.map_nil,
      List.foldr_cons,List.foldr_nil]
     rw [BitVec.toNat_or,BitVec.toNat_or,hgetA,hgetB]
     simp [Nat.or_zero]
  have hsub' : ∀ w ∈ insert (qj d a b) U,w ∈ (yK bank g).map BitVec.toNat:=by
   intro w hw
   simp only [yK,List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_singleton]
   rcases Finset.mem_insert.mp hw with rfl | hu
   · exact Or.inr hval.symm
   · exact Or.inl (sub w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)))
  obtain ⟨gs,o,hleg,hlen,heval⟩:=ih (yK bank g) hsub' ht
  refine ⟨g :: gs,o, ?_,by simp only [List.length_cons];omega,heval⟩
  intro g' hg'
  rcases List.mem_cons.mp hg' with rfl | hg'
  · cases d <;> simp [g]
  · exact hleg g' hg'
def zn (a b : Bool) : Bool := @Bool.rec (fun _=>Bool) b true a
def qS (a b : Bool) : Bool := @Bool.rec (fun _=>Bool) false b a
def kq (a : Bool) : Bool := @Bool.rec (fun _=>Bool) true false a
theorem zQ (a b : Bool) : zn a b=(a||b):=by cases a <;> rfl
theorem qR (a b : Bool) : qS a b=(a&&b):=by cases a <;> rfl
theorem uP (a : Bool) : kq a = !a:=by cases a <;> rfl
def q7 {α : Type} (w : Word) (k : Word → α) : α :=
 @Nat.rec (fun _ => α) (k 0) (fun n _=>k (Nat.succ n)) w
theorem ql {α : Type} (w : Word) (k : Word → α) : q7 w k=k w:=by
 cases w <;> rfl
def ye {α : Type} (ws : List Word) (k : List Word → α) : α :=
 (List.rec (motive:=fun _=>(List Word → α) → α) (fun f=>f [])
  (fun w _ next f=>q7 w (fun v=>next (fun rest=>f (v :: rest)))) ws) k
theorem zV {α : Type} (ws : List Word) (k : List Word → α) :
  ye ws k=k ws:=by
 induction ws generalizing k with
 | nil=>rfl
 | cons w ws ih =>
  change q7 w (fun v=>ye ws (fun rest=>k (v :: rest)))=_
  rw [ql,ih]
theorem qA (a b : Nat) : Nat.beq a b=(a==b):=rfl
theorem uK (a b : Nat) : Nat.ble a b=decide (a ≤ b):=by
 cases h : Nat.ble a b
 · have : ¬ a ≤ b:=fun hl=>Bool.noConfusion ((Nat.ble_eq.mpr hl).symm.trans h)
   simp [this]
 · simp [Nat.ble_eq.mp h]
theorem q4W (a b : Nat) : Nat.blt a b=decide (a < b):=by
 cases h : Nat.blt a b
 · have : ¬ a < b:=fun hl=>Bool.noConfusion ((Nat.blt_eq.mpr hl).symm.trans h)
   simp [this]
 · simp [Nat.blt_eq.mp h]
def qZ (w : Word) (ws : List Word) : Bool :=
 List.rec false (fun a _ next=>zn (Nat.beq a w) next) ws
theorem za (w : Word) (ws : List Word) : qZ w ws=ws.contains w:=by
 induction ws with
 | nil=>rfl
 | cons a ws ih =>
  change zn (Nat.beq a w) (qZ w ws)=(a :: ws).contains w
  rw [zQ,ih,List.contains_cons,Bool.or_comm]
  cases h : Nat.beq a w
  · have hne : w ≠ a:=fun he=>Bool.noConfusion ((Nat.beq_eq.mpr he.symm).symm.trans h)
    simp [hne]
  · have heq : w=a:=(Nat.beq_eq.mp h).symm
    simp [heq]
def q32 (w : Word) (ws : List Word) : List Word :=
 List.rec [] (fun a tail next => @Bool.rec (fun _=>List Word) (a :: next) tail (Nat.beq a w)) ws
theorem q9u (w : Word) (ws : List Word) : q32 w ws=ws.erase w:=by
 induction ws with
 | nil=>rfl
 | cons a ws ih =>
  change @Bool.rec (fun _=>List Word) (a :: q32 w ws) ws (Nat.beq a w)=(a :: ws).erase w
  rw [ih,List.erase_cons]
  cases h : Nat.beq a w
  · have hne : a ≠ w:=fun he=>Bool.noConfusion ((Nat.beq_eq.mpr he).symm.trans h)
    simp [hne]
  · have heq : a=w:=Nat.beq_eq.mp h
    simp [heq]
def yh (w : Word) (ws : List Word) : List Word :=
 q7 w fun w =>
  List.rec [w] (fun a tail next =>
   @Bool.rec (fun _=>List Word) (a :: next) (w :: a :: tail) (Nat.ble w a)) ws
theorem uL (w : Word) (ws : List Word) : yh w ws=qB w ws:=by
 unfold yh;rw [ql]
 induction ws with
 | nil=>rfl
 | cons a ws ih =>
  change @Bool.rec (fun _=>List Word) (a :: List.rec [w] _ ws) (w :: a :: ws) (Nat.ble w a) =
   if w ≤ a then w :: a :: ws else a :: qB w ws
  rw [ih]
  cases h : Nat.ble w a
  · have hlt : ¬ w ≤ a:=fun hle=>Bool.noConfusion ((Nat.ble_eq.mpr hle).symm.trans h)
    simp [hlt]
  · simp [Nat.ble_eq.mp h]
def vR (ws : List Word) (i : Nat) : Word :=
 (List.rec (motive:=fun _=>Nat → Word) (fun _=>0)
  (fun a _ next k => @Nat.rec (fun _=>Word) a (fun j _=>next j) k) ws) i
theorem uM (ws : List Word) (i : Nat) : vR ws i=ws.getD i 0:=by
 induction ws generalizing i with
 | nil=>rfl
 | cons a ws ih =>
  cases i with
  | zero=>rfl
  | succ j=>exact ih j
def qn (tags : List qU) (i : Nat) : qU :=
 (List.rec (motive:=fun _=>Nat → qU) (fun _=>(0,0))
  (fun a _ next k => @Nat.rec (fun _=>qU) a (fun j _=>next j) k) tags) i
def zp (bank : List qb) (i : Nat) : qb :=
 (List.rec (motive:=fun _=>Nat → qb) (fun _=>(0,0,0))
  (fun a _ next k => @Nat.rec (fun _=>qb) a (fun j _=>next j) k) bank) i
def uW (as bs : List Word) : Bool :=
 (List.rec (motive:=fun _=>List Word → Bool)
  (fun bs=>List.rec true (fun _ _ _=>false) bs)
  (fun a _ next bs=>List.rec false (fun b bs' _=>qS (Nat.beq a b) (next bs')) bs) as) bs
theorem q4X (as bs : List Word) : uW as bs=(as==bs):=by
 induction as generalizing bs with
 | nil=>cases bs <;> rfl
 | cons a as ih =>
  cases bs with
  | nil=>rfl
  | cons b bs =>
   change qS (Nat.beq a b) (uW as bs)=((a==b)&&(as==bs))
   rw [qR,ih];rfl
def zz (ws : List Word) : Nat :=
 List.rec 0 (fun _ _ n=>Nat.add n 1) ws
theorem yd (ws : List Word) : zz ws=ws.length:=by
 induction ws with
 | nil=>rfl
 | cons _ _ ih=>change zz _+1=_;rw [ih];rfl
def k9 (ws : List Word) : List Word :=
 List.rec [] (fun w _ rest => @Bool.rec (fun _=>List Word) (w :: rest) rest (qZ w rest)) ws
theorem q8p {w : Word} {ws : List Word} : w ∈ k9 ws ↔ w ∈ ws:=by
 induction ws with
 | nil=>simp [k9]
 | cons a ws ih =>
  change w ∈ @Bool.rec (fun _=>List Word) (a :: k9 ws) (k9 ws) (qZ a (k9 ws)) ↔ _
  rw [za]
  cases hc : (k9 ws).contains a
  · simp [ih]
  · have ha : a ∈ k9 ws:=List.contains_iff_mem.mp hc
    constructor
    · intro hw;exact List.mem_cons_of_mem a (ih.mp hw)
    · intro hw
      rcases List.mem_cons.mp hw with rfl | htail
      · exact ha
      · exact ih.mpr htail
theorem q74 (ws : List Word) : (k9 ws).Nodup:=by
 induction ws with
 | nil=>exact List.nodup_nil
 | cons a ws ih =>
  change (@Bool.rec (fun _=>List Word) (a :: k9 ws) (k9 ws) (qZ a (k9 ws))).Nodup
  rw [za]
  cases hc : (k9 ws).contains a
  · refine List.nodup_cons.mpr ⟨?_,ih⟩
    intro hm;have:=List.contains_iff_mem.mpr hm;rw [hc] at this;exact Bool.noConfusion this
  · exact ih
def zD (w i : Word) : Bool :=
 kq (Nat.beq (Nat.land (Nat.shiftRight w i) 1) 0)
theorem vO (w i : Word) : zD w i=w.testBit i:=by
 unfold zD;rw [uP];exact q0.q9y w i
def y9 (kV qV index : Nat) : Nat :=
 Nat.land (Nat.shiftRight kV (Nat.mul qV index)) (Nat.sub (Nat.shiftLeft 1 qV) 1)
theorem q4V (kV qV index : Nat) : y9 kV qV index=z3 kV qV index:=rfl
def zf (parentWidth qV kV index : Nat) : Nat × Nat :=
 q7 (y9 kV qV index) fun kt =>
  (Nat.land kt (Nat.sub (Nat.shiftLeft 1 parentWidth) 1),Nat.shiftRight kt parentWidth)
def k3 (mask : Word) (ws : List Word) : Word → Bool :=
 List.rec (motive:=fun _=>Word → Bool) (fun _=>true)
  (fun w _ next p=>qS (Nat.blt p w) (qS (Nat.beq (Nat.land w mask) w) (next w))) ws
def q1q (mask : Word) (ws : List Word) : Bool :=
 List.rec true (fun w tail _=>qS (Nat.beq (Nat.land w mask) w) (k3 mask tail w)) ws
theorem q0g {mask : Word} {ws : List Word} {p : Word}
 (h : k3 mask ws p=true) :
 (∀ w ∈ ws,p < w) ∧ ws.Nodup ∧ (∀ w ∈ ws,qm mask w):=by
 induction ws generalizing p with
 | nil=>exact ⟨by simp,List.nodup_nil,by simp⟩
 | cons a ws ih =>
  change qS (Nat.blt p a) (qS (Nat.beq (Nat.land a mask) a) (k3 mask ws a))=true at h
  rw [qR,qR,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq,Nat.beq_eq] at h
  obtain ⟨hpa,ham,hrest⟩:=h
  obtain ⟨hlt,hnd,hms⟩:=ih hrest
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hpa
    · exact Nat.lt_trans hpa (hlt w hw)
  · refine List.nodup_cons.mpr ⟨?_,hnd⟩
    intro hm;exact Nat.lt_irrefl a (hlt a hm)
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ham
    · exact hms w hw
theorem q1L {mask : Word} {ws : List Word} (h : q1q mask ws=true) :
 ws.Nodup ∧ ∀ w ∈ ws,qm mask w:=by
 cases ws with
 | nil=>exact ⟨List.nodup_nil,by simp⟩
 | cons a ws =>
  change qS (Nat.beq (Nat.land a mask) a) (k3 mask ws a)=true at h
  rw [qR,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hlt,hnd,hms⟩:=q0g h.2
  refine ⟨List.nodup_cons.mpr ⟨fun hm=>Nat.lt_irrefl a (hlt a hm),hnd⟩, ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact h.1
  · exact hms w hw
def q0I (m : qg) (w : Word) : Word :=
 q7 w fun w =>
  let left:=List.rec 0 (fun p _ acc=>Nat.lor (Nat.shiftLeft (Nat.land w p.1) p.2) acc) m.1
  let right:=List.rec 0 (fun p _ acc=>Nat.lor (Nat.shiftRight (Nat.land w p.1) p.2) acc) m.2
  Nat.lor left right
theorem q7L (m : qg) (w : Word) : q0I m w=wE m w:=by
 unfold q0I wE;rw [ql];rfl
def vQ (move : z0) (w : Word) : Word :=
 (List.rec (motive:=fun _=>Word → Word) (fun v=>v)
  (fun step _ next v=>q7 (q0I step v) next) move) w
theorem q0J (move : z0) (w : Word) : vQ move w=yG move w:=by
 induction move generalizing w with
 | nil=>rfl
 | cons s ss ih =>
  change q7 (q0I s w) (vQ ss)=yG ss (wE s w)
  rw [ql,q7L,ih]
def vH (m : z0) (ws : List Word) : List Word :=
 List.rec [] (fun w _ next=>yh (vQ m w) next) ws
theorem q33 (m : z0) (ws : List Word) : vH m ws=jc m ws:=by
 induction ws with
 | nil=>rfl
 | cons w ws ih =>
  change yh (vQ m w) (vH m ws)=qB (yG m w) (jc m ws)
  rw [uL,q0J,ih]
noncomputable def uX : {f : z0 → List Word → List Word // f=vH}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta vH yh vQ q0I
  beta_reduce
  exact rfl
noncomputable def vz : z0 → List Word → List Word:=uX.1
theorem q19 (m : z0) (ws : List Word) : vz m ws=jc m ws :=
 (congrFun (congrFun uX.2 m) ws).trans (q33 m ws)
def zw (save : Bool) (w : Word) (ws : List Word) : List Word :=
 @Bool.rec (fun _=>List Word) (q32 w ws) ws save
theorem ja (save : Bool) (w : Word) (ws : List Word) : zw save w ws=zu save w ws:=by
 cases save
 · exact q9u w ws
 · rfl
def zA (mask op x y : Word) : Word :=
 @Bool.rec (fun _=>Word)
  (@Bool.rec (fun _=>Word) (Nat.xor mask x) (Nat.lor x y) (Nat.beq op 1))
  (Nat.land x y) (Nat.beq op 0)
theorem q2s (mask op x y : Word) : zA mask op x y=zg mask op x y:=by
 unfold zA zg
 cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> rfl
def ko (keep : Bool) (w : Word) (bank : List qb) : List qb :=
 @Bool.rec (fun _=>List qb)
  (List.rec [] (fun tag tail next => @Bool.rec (fun _=>List qb) (tag :: next) tail (Nat.beq tag.1 w)) bank)
  bank keep
def vw (tag : qb) (bank : List qb) : List qb :=
 List.rec [tag] (fun old tail next => @Bool.rec (fun _=>List qb) (old :: next) (tag :: old :: tail) (Nat.ble tag.1 old.1)) bank
def wi (mask qp q5 : Word) (bank : List qb) : List qb :=
 q7 (Nat.mod q5 4) fun keep =>
  q7 (Nat.mod (Nat.div q5 4) 3) fun op =>
   let x:=zp bank (Nat.div q5 768)
   let y:=zp bank (Nat.mod (Nat.div q5 12) 64)
   q7 (zA mask op x.1 y.1) fun w =>
    q7 (zA qp op x.2.1 y.2.1) fun up =>
     q7 (zA qp op x.2.2 y.2.2) fun dn =>
      vw (w,up,dn)
       (ko (zn (Nat.beq op 2) (zD keep 1)) y.1
        (ko (zD keep 0) x.1 bank))
noncomputable def k0 : {f : Word → Word → Word → List qb → List qb // f=wi}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta wi vw ko zp zA zD zn kq
  beta_reduce
  exact rfl
def kn (bank : List qb) (q5 : Nat) : List qb :=
 (List.rec (motive:=fun _=>Nat → List qb) (fun _=>[])
  (fun tag _ next k =>
   q7 (Nat.shiftRight k 1) fun hi =>
    @Bool.rec (fun _=>List qb) (tag :: next hi) (next hi) (Nat.beq (Nat.land k 1) 0)) bank) q5
noncomputable def qG (mask qV : Word) (root : List qb) (q8 : Nat) (q3 : zj)
  (i : Nat) : List qU :=
 let qp:=Nat.sub (Nat.shiftLeft 1 qV) 1
 let tags:=(Nat.rec (motive:=fun _=>Nat → List qb) (fun _=>[])
  (fun _ previous j =>
   let pt:=q3 j
   q7 pt.1 fun qz =>
    q7 pt.2 fun q5 =>
     @Bool.rec (fun _=>List qb)
      (q7 (Nat.sub qz 1) fun p1=>k0.1 mask qp q5 (previous p1))
      (kn root q5)
      (Nat.beq qz 0)) (Nat.add q8 1)) i
 List.rec [] (fun tag _ rest=>tag.2 :: rest) tags
def kQ (mask q5 : Nat) (state : qc) : Option qc :=
 let (q8,nots,ws,history):=state
 q7 (Nat.mod q5 4) fun keep =>
  q7 (Nat.mod (Nat.div q5 4) 3) fun op =>
   q7 (Nat.div q5 768) fun a =>
    q7 (Nat.mod (Nat.div q5 12) 64) fun b =>
     let badOp := @Bool.rec (fun _=>Bool)
      (Nat.ble b a)
      (zn (kq (Nat.beq a b)) (zn (Nat.ble 2 keep) (Nat.beq nots 0)))
      (Nat.beq op 2)
     @Bool.rec (fun _=>Option qc)
      (q7 (vR ws a) fun x =>
       q7 (vR ws b) fun y =>
        q7 (zA mask op x y) fun w =>
         @Bool.rec (fun _=>Option qc)
          (let kp0:=zD keep 0
           let kp1:=zn (Nat.beq op 2) (zD keep 1)
           let zJ := @Bool.rec (fun _=>Nat) nots (Nat.sub nots 1) (Nat.beq op 2)
           q7 (Nat.sub q8 1) fun nf =>
            q7 zJ fun nn =>
             ye (yh w (zw kp1 y (zw kp0 x ws))) fun nws =>
              some (nf,nn,nws,(w,x,y) :: history))
          none
          (zn (Nat.beq w 0) (zn (Nat.beq w mask) (qZ w ws))))
      none
      (zn (Nat.beq q8 0) (zn (Nat.ble (zz ws) b) badOp))
theorem q0M (mask q5 : Nat) (state : qc) :
 kQ mask q5 state=qL mask q5 state:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 unfold kQ qL
 simp only [ql,zV,zQ,uP,uM,q2s,
  za,vO,uL,ja,yd,zg,zu]
 rw [show Nat.div q5 768=q5 / (4*3*64) from rfl,
  show Nat.mod (Nat.div q5 12) 64=q5 / (4*3) % 64 from rfl,
  show Nat.mod (Nat.div q5 4) 3=q5 / 4 % 3 from rfl,
  show Nat.mod q5 4=q5 % 4 from rfl]
 have hbad : (Nat.beq q8 0||(Nat.ble ws.length (q5 / (4*3) % 64) ||
  @Bool.rec (fun _=>Bool) (Nat.ble (q5 / (4*3) % 64) (q5 / (4*3*64)))
   (!Nat.beq (q5 / (4*3*64)) (q5 / (4*3) % 64)||(Nat.ble 2 (q5 % 4)||Nat.beq nots 0))
   (Nat.beq (q5 / 4 % 3) 2))) =
  ((q8==0)||decide (q5 / (4*3) % 64 ≥ ws.length) ||
   if (q5 / 4 % 3==2)=true then
    ((q5 / (4*3*64) != q5 / (4*3) % 64)||decide (q5 % 4 ≥ 2)||(nots==0))
   else decide (q5 / (4*3*64) ≥ q5 / (4*3) % 64)):=by
  rw [uK,uK,uK,qA,qA,qA,qA]
  cases (q5 / 4 % 3==2) <;> simp [bne,Bool.or_assoc]
 cases hb : (Nat.beq q8 0||(Nat.ble ws.length (q5 / (4*3) % 64) ||
  @Bool.rec (fun _=>Bool) (Nat.ble (q5 / (4*3) % 64) (q5 / (4*3*64)))
   (!Nat.beq (q5 / (4*3*64)) (q5 / (4*3) % 64)||(Nat.ble 2 (q5 % 4)||Nat.beq nots 0))
   (Nat.beq (q5 / 4 % 3) 2)))
 · have hb2:=hbad.symm.trans hb
   rw [hb2];simp only [Bool.false_eq_true, ↓reduceIte]
   have hweq : (if Nat.beq (q5 / 4 % 3) 0=true then ws.getD (q5 / (4*3*64)) 0&&&ws.getD (q5 / (4*3) % 64) 0
    else if Nat.beq (q5 / 4 % 3) 1=true then ws.getD (q5 / (4*3*64)) 0|||ws.getD (q5 / (4*3) % 64) 0
    else mask^^^ws.getD (q5 / (4*3*64)) 0) =
    (if (q5 / 4 % 3==0)=true then ws.getD (q5 / (4*3*64)) 0&&&ws.getD (q5 / (4*3) % 64) 0
    else if (q5 / 4 % 3==1)=true then ws.getD (q5 / (4*3*64)) 0|||ws.getD (q5 / (4*3) % 64) 0
    else mask^^^ws.getD (q5 / (4*3*64)) 0):=rfl
   rw [hweq]
   generalize (if (q5 / 4 % 3==0)=true then ws.getD (q5 / (4*3*64)) 0&&&ws.getD (q5 / (4*3) % 64) 0
    else if (q5 / 4 % 3==1)=true then ws.getD (q5 / (4*3*64)) 0|||ws.getD (q5 / (4*3) % 64) 0
    else mask^^^ws.getD (q5 / (4*3*64)) 0)=w
   have hst : (Nat.beq w 0||(Nat.beq w mask||ws.contains w))=((w==0)||(w==mask)||ws.contains w):=by
    rw [qA,qA,Bool.or_assoc]
   rw [hst]
   cases (w==0)||(w==mask)||ws.contains w
   · simp only [Bool.false_eq_true, ↓reduceIte]
     rw [qA]
     cases (q5 / 4 % 3==2) <;> rfl
   · rfl
 · rw [hbad.symm.trans hb];rfl
noncomputable def q0c : {f : Nat → Nat → qc → Option qc // f=kQ}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta kQ zA zw yh q32 qZ vR zz zD zn qS kq
  beta_reduce
  exact rfl
noncomputable def uN : Nat → Nat → qc → Option qc:=q0c.1
theorem q2u (mask q5 : Nat) (state : qc) :
  uN mask q5 state=qL mask q5 state :=
 (congrFun (congrFun (congrFun q0c.2 mask) q5) state).trans (q0M mask q5 state)
abbrev qy:=Nat × Nat × List Word
def vT (mask q5 : Nat) (state : qy) : Option qy :=
 let (q8,nots,ws):=state
 q7 (Nat.mod q5 4) fun keep =>
  q7 (Nat.mod (Nat.div q5 4) 3) fun op =>
   q7 (Nat.div q5 768) fun a =>
    q7 (Nat.mod (Nat.div q5 12) 64) fun b =>
     let badOp := @Bool.rec (fun _=>Bool)
      (Nat.ble b a)
      (zn (kq (Nat.beq a b)) (zn (Nat.ble 2 keep) (Nat.beq nots 0)))
      (Nat.beq op 2)
     @Bool.rec (fun _=>Option qy)
      (q7 (vR ws a) fun x =>
       q7 (vR ws b) fun y =>
        q7 (zA mask op x y) fun w =>
         @Bool.rec (fun _=>Option qy)
          (let kp0:=zD keep 0
           let kp1:=zn (Nat.beq op 2) (zD keep 1)
           let zJ := @Bool.rec (fun _=>Nat) nots (Nat.sub nots 1) (Nat.beq op 2)
           q7 (Nat.sub q8 1) fun nf =>
            q7 zJ fun nn =>
             ye (yh w (zw kp1 y (zw kp0 x ws))) fun nws =>
              some (nf,nn,nws))
          none
          (zn (Nat.beq w 0) (zn (Nat.beq w mask) (qZ w ws))))
      none
      (zn (Nat.beq q8 0) (zn (Nat.ble (zz ws) b) badOp))
theorem q50 (mask q5 : Nat) (state : qc) :
 vT mask q5 (state.1,state.2.1,state.2.2.1) =
  (kQ mask q5 state).map (fun s=>(s.1,s.2.1,s.2.2.1)):=by
 obtain ⟨q8,nots,ws,history⟩:=state
 unfold vT kQ
 simp only [ql,zV]
 cases zn (Nat.beq q8 0) (zn (Nat.ble (zz ws) (Nat.mod (Nat.div q5 12) 64))
  (@Bool.rec (fun _=>Bool) (Nat.ble (Nat.mod (Nat.div q5 12) 64) (Nat.div q5 768))
   (zn (kq (Nat.beq (Nat.div q5 768) (Nat.mod (Nat.div q5 12) 64)))
    (zn (Nat.ble 2 (Nat.mod q5 4)) (Nat.beq nots 0)))
   (Nat.beq (Nat.mod (Nat.div q5 4) 3) 2)))
 · dsimp only
   cases zn (Nat.beq (zA mask (Nat.mod (Nat.div q5 4) 3) (vR ws (Nat.div q5 768)) (vR ws (Nat.mod (Nat.div q5 12) 64))) 0)
    (zn (Nat.beq (zA mask (Nat.mod (Nat.div q5 4) 3) (vR ws (Nat.div q5 768)) (vR ws (Nat.mod (Nat.div q5 12) 64))) mask)
     (qZ (zA mask (Nat.mod (Nat.div q5 4) 3) (vR ws (Nat.div q5 768)) (vR ws (Nat.mod (Nat.div q5 12) 64))) ws)) <;> rfl
 · rfl
noncomputable def q0d : {f : Nat → Nat → qy → Option qy // f=vT}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta vT zA zw yh q32 qZ vR zz zD zn qS kq
  beta_reduce
  exact rfl
noncomputable def vo : Nat → Nat → qy → Option qy:=q0d.1
theorem q2v (mask q5 : Nat) (state : qc) :
  vo mask q5 (state.1,state.2.1,state.2.2.1) =
   (qL mask q5 state).map (fun s=>(s.1,s.2.1,s.2.2.1)):=by
 rw [show vo=vT from q0d.2,q50,q0M]
def yp (base : List Word) (q5 : Nat) : List Word :=
 (List.rec (motive:=fun _=>Nat → List Word) (fun _=>[])
  (fun word _ next bits =>
   q7 (Nat.shiftRight bits 1) fun hi =>
    @Bool.rec (fun _=>List Word) (word :: next hi) (next hi) (Nat.beq (Nat.land bits 1) 0)) base) q5
theorem wa (base : List Word) (q5 : Nat) : yp base q5=yW base q5:=by
 induction base generalizing q5 with
 | nil=>rfl
 | cons w ws ih =>
  change q7 (Nat.shiftRight q5 1) (fun hi =>
   @Bool.rec (fun _=>List Word) (w :: yp ws hi) (yp ws hi) (Nat.beq (Nat.land q5 1) 0)) =
   if (q5&&&1==0)=true then yW ws (q5>>>1) else w :: yW ws (q5>>>1)
  rw [ql,ih]
  have hq : Nat.beq (Nat.land q5 1) 0=(q5&&&1==0):=rfl
  rw [hq]
  cases (q5&&&1==0) <;> rfl
def zb (mask : Word) (stock : List Word) (q8 q9 : Nat) (q3 : zj) (n : Nat) :
  Nat → Option qc :=
 Nat.rec (motive:=fun _=>Nat → Option qc) (fun _=>none)
  (fun _ previous j =>
   let (qz,q5):=q3 j
   if qz==0 then
    if q5 < 2 ^ stock.length then some (zO stock q8 q9 q5) else none
   else (previous (qz - 1)).bind (qL mask q5)) n
theorem vA {mask q5 : Nat} {s child : qc}
 (h : qL mask q5 s=some child) : 0 < s.1 ∧ child.1=s.1 - 1:=by
 obtain ⟨q8,nots,ws,history⟩:=s
 let keep:=q5 % 4
 let op:=q5 / 4 % 3
 let a:=q5 / (4*3*64)
 let b:=q5 / (4*3) % 64
 let x:=ws.getD a 0
 let y:=ws.getD b 0
 let w:=if op==0 then x&&&y else if op==1 then x|||y else mask^^^x
 let bad : Bool:=q8==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
 let stale : Bool:=w==0||w==mask||ws.contains w
 change (if bad then none else if stale then none else
  some (q8 - 1,if op==2 then nots - 1 else nots,
   qB w (if op==2||keep.testBit 1 then (if keep.testBit 0 then ws else ws.erase x) else (if keep.testBit 0 then ws else ws.erase x).erase y),
   (w,x,y) :: history))=some child at h
 by_cases hb : bad=true
 · simp [hb] at h
 by_cases hs : stale=true
 · simp [hb,hs] at h
 have heq : (q8 - 1,if op==2 then nots - 1 else nots,
  qB w (if op==2||keep.testBit 1 then (if keep.testBit 0 then ws else ws.erase x) else (if keep.testBit 0 then ws else ws.erase x).erase y),
  (w,x,y) :: history)=child:=by simpa [hb,hs] using h
 have hpos : 0 < q8:=by
  by_contra! hz
  have h0 : q8=0:=by omega
  exact hb (by simp [bad,h0])
 exact ⟨hpos,by rw [← heq]⟩
theorem q53 {mask : Word} {stock : List Word} {q8 q9 : Nat} {q3 : zj}
 {n m j : Nat} {st : qc} (hle : n ≤ m)
 (h : zb mask stock q8 q9 q3 n j=some st) :
 zb mask stock q8 q9 q3 m j=some st:=by
 induction n generalizing m j st with
 | zero=>simp [zb] at h
 | succ n ih =>
  cases m with
  | zero=>omega
  | succ m =>
   change (if (q3 j).1==0 then
    if (q3 j).2 < 2 ^ stock.length then some (zO stock q8 q9 (q3 j).2) else none
    else (zb mask stock q8 q9 q3 n ((q3 j).1 - 1)).bind (qL mask (q3 j).2))=some st at h
   change (if (q3 j).1==0 then
    if (q3 j).2 < 2 ^ stock.length then some (zO stock q8 q9 (q3 j).2) else none
    else (zb mask stock q8 q9 q3 m ((q3 j).1 - 1)).bind (qL mask (q3 j).2))=some st
   by_cases hp : ((q3 j).1==0)=true
   · simpa [hp] using h
   · simp only [hp,Bool.false_eq_true, ↓reduceIte] at h ⊢
     cases hprev : zb mask stock q8 q9 q3 n ((q3 j).1 - 1) with
     | none=>rw [hprev] at h;simp at h
     | some pst =>
      rw [hprev] at h
      rw [ih (by omega) hprev]
      exact h
theorem q3R {mask : Word} {stock : List Word} {q8 q9 : Nat} {q3 : zj}
 {n j : Nat} {st : qc}
 (h : zb mask stock q8 q9 q3 n j=some st) :
 st.1 ≤ q8 ∧ zb mask stock q8 q9 q3 (q8+1 - st.1) j=some st:=by
 induction n generalizing j st with
 | zero=>simp [zb] at h
 | succ n ih =>
  change (if (q3 j).1==0 then
   if (q3 j).2 < 2 ^ stock.length then some (zO stock q8 q9 (q3 j).2) else none
   else (zb mask stock q8 q9 q3 n ((q3 j).1 - 1)).bind (qL mask (q3 j).2))=some st at h
  by_cases hp : ((q3 j).1==0)=true
  · simp only [hp, ↓reduceIte] at h
    by_cases ht : (q3 j).2 < 2 ^ stock.length
    · simp only [ht, ↓reduceIte,Option.some.injEq] at h
      subst st
      refine ⟨Nat.le_refl _, ?_⟩
      have h1 : q8+1 - q8=1:=by omega
      change zb mask stock q8 q9 q3 (q8+1 - q8) j=_
      rw [h1]
      change (if (q3 j).1==0 then
       if (q3 j).2 < 2 ^ stock.length then some (zO stock q8 q9 (q3 j).2) else none else _)=_
      simp [hp,ht]
    · simp [ht] at h
  · simp only [hp,Bool.false_eq_true, ↓reduceIte] at h
    cases hprev : zb mask stock q8 q9 q3 n ((q3 j).1 - 1) with
    | none=>rw [hprev] at h;simp at h
    | some pst =>
     rw [hprev] at h
     obtain ⟨hpLe,hpTight⟩:=ih hprev
     obtain ⟨hpPos,hsEq⟩:=vA h
     refine ⟨by omega, ?_⟩
     have hstep : q8+1 - st.1=(q8+1 - pst.1)+1:=by omega
     rw [hstep]
     change (if (q3 j).1==0 then _
      else (zb mask stock q8 q9 q3 (q8+1 - pst.1) ((q3 j).1 - 1)).bind (qL mask (q3 j).2))=some st
     simp only [hp,Bool.false_eq_true, ↓reduceIte,hpTight]
     exact h
theorem q1a {mask : Word} {stock : List Word} {q8 q9 i dest q5 : Nat}
  {q3 : zj} {s child : qc}
  (hs : jr mask stock q8 q9 q3 i=some s)
  (heval : qL mask q5 s=some child)
  (hfor : q3 dest=(i+1,q5)) :
  jr mask stock q8 q9 q3 dest=some child:=by
 obtain ⟨hLe,hTight⟩:=q3R (show zb mask stock q8 q9 q3 (q8+1) i=some s from hs)
 obtain ⟨hPos,_⟩:=vA heval
 have hFuel : zb mask stock q8 q9 q3 q8 i=some s :=
  q53 (by omega) hTight
 change (if (q3 dest).1==0 then _
  else (zb mask stock q8 q9 q3 q8 ((q3 dest).1 - 1)).bind (qL mask (q3 dest).2))=some child
 rw [hfor]
 have hne : ((i+1 : Nat)==0)=false:=rfl
 simp only [hne,Bool.false_eq_true, ↓reduceIte,Nat.add_sub_cancel,hFuel]
 exact heval
theorem q1P {mask : Word} {stock : List Word} {q8 q9 dest q5 : Nat}
  {q3 : zj} (ht : q5 < 2 ^ stock.length) (hfor : q3 dest=(0,q5)) :
  jr mask stock q8 q9 q3 dest=some (zO stock q8 q9 q5):=by
 change (if (q3 dest).1==0 then
  if (q3 dest).2 < 2 ^ stock.length then some (zO stock q8 q9 (q3 dest).2) else none else _)=_
 rw [hfor]
 simp [ht]
noncomputable def zx (mask : Word) (stock : List Word) (q8 q9 : Nat) (q3 : zj)
  (i : Nat) : Option qc :=
 let lim:=Nat.shiftLeft 1 (zz stock)
 (Nat.rec (motive:=fun _=>Nat → Option qc) (fun _=>none)
  (fun _ previous j =>
   let pt:=q3 j
   q7 pt.1 fun qz =>
    q7 pt.2 fun q5 =>
     @Bool.rec (fun _=>Option qc)
      (q7 (Nat.sub qz 1) fun p1 =>
       @Option.rec qc (fun _=>Option qc) none (uN mask q5) (previous p1))
      (@Bool.rec (fun _=>Option qc) none (some (q8,q9,yp stock q5,[]))
       (Nat.blt q5 lim))
      (Nat.beq qz 0)) (Nat.add q8 1)) i
theorem q75 (mask : Word) (stock : List Word) (q8 q9 : Nat) (q3 : zj) (i : Nat) :
 zx mask stock q8 q9 q3 i=jr mask stock q8 q9 q3 i:=by
 have hlim : Nat.shiftLeft 1 (zz stock)=2 ^ stock.length:=by
  rw [yd]
  change 1<<<stock.length=2 ^ stock.length
  rw [Nat.shiftLeft_eq,Nat.one_mul]
 suffices h : ∀ n j,
  (Nat.rec (motive:=fun _=>Nat → Option qc) (fun _=>none)
   (fun _ previous j =>
    let pt:=q3 j
    q7 pt.1 fun qz =>
     q7 pt.2 fun q5 =>
      @Bool.rec (fun _=>Option qc)
       (q7 (Nat.sub qz 1) fun p1 =>
        @Option.rec qc (fun _=>Option qc) none (uN mask q5) (previous p1))
       (@Bool.rec (fun _=>Option qc) none (some (q8,q9,yp stock q5,[]))
        (Nat.blt q5 (Nat.shiftLeft 1 (zz stock))))
       (Nat.beq qz 0)) n) j =
  zb mask stock q8 q9 q3 n j from h (q8+1) i
 intro n
 induction n with
 | zero=>intro _;rfl
 | succ n ih =>
  intro j
  change _=(if (q3 j).1==0 then
   if (q3 j).2 < 2 ^ stock.length then some (zO stock q8 q9 (q3 j).2) else none
   else (zb mask stock q8 q9 q3 n ((q3 j).1 - 1)).bind (qL mask (q3 j).2))
  dsimp only
  rw [ql,ql]
  cases hp : Nat.beq (q3 j).1 0
  · dsimp only
    rw [ql,ih]
    have hne : ((q3 j).1==0)=false:=hp
    simp only [hne,Bool.false_eq_true, ↓reduceIte]
    cases zb mask stock q8 q9 q3 n ((q3 j).1 - 1) with
    | none=>rfl
    | some st=>exact q2u mask (q3 j).2 st
  · dsimp only
    have heq : ((q3 j).1==0)=true:=hp
    simp only [heq, ↓reduceIte,hlim,wa,zO]
    cases hlt : Nat.blt (q3 j).2 (2 ^ stock.length)
    · have : ¬ (q3 j).2 < 2 ^ stock.length:=fun h=>Bool.noConfusion ((Nat.blt_eq.mpr h).symm.trans hlt)
      simp [this]
    · simp [Nat.blt_eq.mp hlt]
noncomputable def qr (mask : Word) (stock : List Word) (q8 q9 : Nat) (q3 : zj)
  (i : Nat) : Option qy :=
 let lim:=Nat.shiftLeft 1 (zz stock)
 (Nat.rec (motive:=fun _=>Nat → Option qy) (fun _=>none)
  (fun _ previous j =>
   let pt:=q3 j
   q7 pt.1 fun qz =>
    q7 pt.2 fun q5 =>
     @Bool.rec (fun _=>Option qy)
      (q7 (Nat.sub qz 1) fun p1 =>
       @Option.rec qy (fun _=>Option qy) none (vo mask q5) (previous p1))
      (@Bool.rec (fun _=>Option qy) none (some (q8,q9,yp stock q5))
       (Nat.blt q5 lim))
      (Nat.beq qz 0)) (Nat.add q8 1)) i
theorem q2t (mask : Word) (stock : List Word) (q8 q9 : Nat) (q3 : zj) (i : Nat) :
 qr mask stock q8 q9 q3 i =
  (jr mask stock q8 q9 q3 i).map (fun s=>(s.1,s.2.1,s.2.2.1)):=by
 have hlim : Nat.shiftLeft 1 (zz stock)=2 ^ stock.length:=by
  rw [yd];change 1<<<stock.length=2 ^ stock.length;rw [Nat.shiftLeft_eq,Nat.one_mul]
 suffices h : ∀ n j,
  (Nat.rec (motive:=fun _=>Nat → Option qy) (fun _=>none)
   (fun _ previous j =>
    let pt:=q3 j
    q7 pt.1 fun qz =>
     q7 pt.2 fun q5 =>
      @Bool.rec (fun _=>Option qy)
       (q7 (Nat.sub qz 1) fun p1 =>
        @Option.rec qy (fun _=>Option qy) none (vo mask q5) (previous p1))
       (@Bool.rec (fun _=>Option qy) none (some (q8,q9,yp stock q5))
        (Nat.blt q5 (Nat.shiftLeft 1 (zz stock))))
       (Nat.beq qz 0)) n) j =
  (zb mask stock q8 q9 q3 n j).map (fun s=>(s.1,s.2.1,s.2.2.1)) from h (q8+1) i
 intro n
 induction n with
 | zero=>intro _;rfl
 | succ n ih =>
  intro j
  change _=(if (q3 j).1==0 then
   if (q3 j).2 < 2 ^ stock.length then some (zO stock q8 q9 (q3 j).2) else none
   else (zb mask stock q8 q9 q3 n ((q3 j).1 - 1)).bind (qL mask (q3 j).2)).map (fun s=>(s.1,s.2.1,s.2.2.1))
  dsimp only
  rw [ql,ql]
  cases hp : Nat.beq (q3 j).1 0
  · dsimp only
    rw [ql,ih]
    have hne : ((q3 j).1==0)=false:=hp
    simp only [hne,Bool.false_eq_true, ↓reduceIte]
    cases zb mask stock q8 q9 q3 n ((q3 j).1 - 1) with
    | none=>rfl
    | some st=>exact q2v mask (q3 j).2 st
  · dsimp only
    have heq : ((q3 j).1==0)=true:=hp
    simp only [heq, ↓reduceIte,hlim,wa,zO]
    cases hlt : Nat.blt (q3 j).2 (2 ^ stock.length)
    · have : ¬ (q3 j).2 < 2 ^ stock.length:=fun h=>Bool.noConfusion ((Nat.blt_eq.mpr h).symm.trans hlt)
      simp [this]
    · simp [Nat.blt_eq.mp hlt]
def yf (mask : Word) (bank : List Word) (w : Word) : Bool :=
 zn (Nat.beq w 0) (zn (Nat.beq w mask) (qZ w bank))
theorem jT (mask : Word) (bank : List Word) (w : Word) :
  yf mask bank w=qC mask bank w:=by
 unfold yf qC
 rw [zQ,zQ,za,qA,qA,Bool.or_assoc]
def q2r {α : Type} (xs : List α) : List α :=
 (List.rec (motive:=fun _=>List α → List α) (fun acc=>acc) (fun x _ next acc=>next (x :: acc)) xs) []
theorem q7M {α : Type} (xs : List α) : q2r xs=xs.reverse:=by
 suffices h : ∀ acc,
   (List.rec (motive:=fun _=>List α → List α) (fun acc=>acc) (fun x _ next acc=>next (x :: acc)) xs) acc =
   xs.reverse ++ acc by
  have h0:=h []
  simpa [q2r] using h0
 induction xs with
 | nil=>intro _;rfl
 | cons x xs ih=>intro acc;dsimp only;rw [ih];simp
def jQ (mask : Word) (bank : List Word) (v a b : Word) : Bool :=
 qS (yf mask bank a)
  (qS (yf mask bank b) (zn (Nat.beq v (Nat.land a b)) (Nat.beq v (Nat.lor a b))))
theorem q2q (mask : Word) (bank : List Word) (v a b : Word) :
  jQ mask bank v a b=y8 mask bank v a b:=by
 unfold jQ y8
 rw [qR,qR,zQ,jT,jT,qA,qA,Bool.and_assoc];rfl
def zK (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
  (bank : List Word) (notsLeft : Nat) : List Word × Nat :=
 (List.rec (motive:=fun _=>List Word → Nat → List Word × Nat) (fun _ _=>([],0))
  (fun rec _ next bank nl =>
   q7 (Nat.land rec.1 mask) fun v =>
    @Bool.rec (fun _=>List Word × Nat) (next bank nl)
     (q7 (Nat.land rec.2.1 mask) fun am =>
      q7 (Nat.land rec.2.2 mask) fun bm =>
       @Bool.rec (fun _=>List Word × Nat)
        (@Bool.rec (fun _=>List Word × Nat) (next bank nl)
         (let r:=next (v :: bank) (Nat.sub nl 1);(v :: r.1,Nat.add r.2 1))
         (qS (Nat.blt 0 nl) (qS (yf mask bank am) (Nat.beq v (Nat.xor mask am)))))
        (let r:=next (v :: bank) nl;(v :: r.1,r.2))
        (jQ mask bank v am bm))
     (qS (qZ v needed) (kq (yf mask bank v)))) recipes) bank notsLeft
theorem wJ (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
 (bank : List Word) (nl : Nat) :
 zK mask needed recipes bank nl=qd mask needed recipes bank nl:=by
 induction recipes generalizing bank nl with
 | nil=>rfl
 | cons rec rest ih =>
  obtain ⟨w,a,b⟩:=rec
  change q7 (Nat.land w mask) (fun v =>
   @Bool.rec (fun _=>List Word × Nat) (zK mask needed rest bank nl)
    (q7 (Nat.land a mask) fun am =>
     q7 (Nat.land b mask) fun bm =>
      @Bool.rec (fun _=>List Word × Nat)
       (@Bool.rec (fun _=>List Word × Nat) (zK mask needed rest bank nl)
        (let r:=zK mask needed rest (v :: bank) (Nat.sub nl 1);(v :: r.1,Nat.add r.2 1))
        (qS (Nat.blt 0 nl) (qS (yf mask bank am) (Nat.beq v (Nat.xor mask am)))))
       (let r:=zK mask needed rest (v :: bank) nl;(v :: r.1,r.2))
       (jQ mask bank v am bm))
    (qS (qZ v needed) (kq (yf mask bank v)))) =
   qq (w&&&mask) (fun v =>
    if needed.contains v && !qC mask bank v then
     qq (a&&&mask) (fun am =>
      qq (b&&&mask) (fun bm =>
       if y8 mask bank v am bm then
        let r:=qd mask needed rest (v :: bank) nl
        (v :: r.1,r.2)
       else if nl > 0&&qC mask bank am&&v==(mask^^^am) then
        let r:=qd mask needed rest (v :: bank) (nl - 1)
        (v :: r.1,r.2+1)
       else qd mask needed rest bank nl))
    else qd mask needed rest bank nl)
  rw [ql,zG,qR,za,uP,jT]
  cases needed.contains (w&&&mask) && !qC mask bank (w&&&mask)
  · simp only [Bool.false_eq_true, ↓reduceIte];exact ih bank nl
  · simp only [↓reduceIte,ql,zG,q2q]
    cases y8 mask bank (w&&&mask) (a&&&mask) (b&&&mask)
    · simp only [Bool.false_eq_true, ↓reduceIte,qR,jT]
      have hc : (Nat.blt 0 nl&&(qC mask bank (Nat.land a mask)&&Nat.beq (Nat.land w mask) (Nat.xor mask (Nat.land a mask)))) =
       (decide (nl > 0)&&qC mask bank (a&&&mask)&&((w&&&mask)==(mask^^^(a&&&mask)))):=by
       rw [q4W,qA,Bool.and_assoc];rfl
      rw [hc]
      cases decide (nl > 0)&&qC mask bank (a&&&mask)&&((w&&&mask)==(mask^^^(a&&&mask)))
      · simp only [Bool.false_eq_true, ↓reduceIte];exact ih bank nl
      · simp only [↓reduceIte];rw [ih _ _];rfl
    · simp only [↓reduceIte];rw [ih _ _];rfl
def q11 (cut : Word) (bank ws : List Word) : Bool :=
 List.rec true (fun w _ next=>qS (yf cut bank (Nat.land w cut)) next) ws
theorem q78 (cut : Word) (bank ws : List Word) :
  q11 cut bank ws=ws.all (fun w=>qC cut bank (w&&&cut)):=by
 induction ws with
 | nil=>rfl
 | cons w ws ih =>
  change qS (yf cut bank (Nat.land w cut)) (q11 cut bank ws) =
   (qC cut bank (w&&&cut)&&ws.all (fun w=>qC cut bank (w&&&cut)))
  rw [qR,jT,ih];rfl
def q77 (xs ys : List Word) : List Word :=
 List.rec ys (fun x _ next=>x :: next) xs
theorem q8q (xs ys : List Word) : q77 xs ys=xs ++ ys:=by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>exact congrArg (x :: ·) ih
def qad (a b : Nat) : Nat := @Bool.rec (fun _=>Nat) b a (Nat.ble a b)
theorem qac (a b : Nat) : qad a b=min a b:=by
 unfold qad
 cases h : Nat.ble a b
 · have : ¬ a ≤ b:=fun hl=>Bool.noConfusion ((Nat.ble_eq.mpr hl).symm.trans h)
   exact (Nat.min_eq_right (Nat.le_of_not_ge this)).symm
 · exact (Nat.min_eq_left (Nat.ble_eq.mp h)).symm
def qaf (a b : Nat) : Nat := @Bool.rec (fun _=>Nat) a b (Nat.ble a b)
theorem qae (a b : Nat) : qaf a b=max a b:=by
 unfold qaf
 cases h : Nat.ble a b
 · have : ¬ a ≤ b:=fun hl=>Bool.noConfusion ((Nat.ble_eq.mpr hl).symm.trans h)
   exact (Nat.max_eq_left (Nat.le_of_not_ge this)).symm
 · exact (Nat.max_eq_right (Nat.ble_eq.mp h)).symm
def wL (cut : Word) (stock words : List Word) (sl : Nat) : Option (Nat × List Word × Nat) :=
 (List.rec (motive:=fun _=>Nat → List Word → Nat → Option (Nat × List Word × Nat))
  (fun fl seen rem=>some (fl,seen,rem))
  (fun w _ next fl seen rem =>
   q7 (Nat.land w cut) fun v =>
    @Bool.rec (fun _=>Option (Nat × List Word × Nat))
     (@Bool.rec (fun _=>Option (Nat × List Word × Nat))
      (@Nat.rec (fun _=>Option (Nat × List Word × Nat)) none
       (fun r1 _ => @Nat.rec (fun _=>Option (Nat × List Word × Nat)) none
        (fun r2 _=>next fl (v :: seen) r2) r1) rem)
      (@Nat.rec (fun _=>Option (Nat × List Word × Nat)) none
       (fun r1 _=>next fl seen r1) rem)
      (zn (qZ v stock) (qZ v seen)))
     (next (Nat.add fl 1) seen rem)
     (zn (Nat.beq v 0) (Nat.beq v cut)))
  words) 0 [] sl
theorem q3Q {cut : Word} {stock words : List Word} {sl fl remOut : Nat} {seenOut : List Word}
 (h : wL cut stock words sl=some (fl,seenOut,remOut)) :
 fl=z5 cut words ∧
 seenOut=zC cut stock words ∧
 words.length+seenOut.length+remOut=fl+sl:=by
 suffices gen : ∀ (l : List Word) (fl0 : Nat) (seen0 : List Word) (rem0 : Nat),
  (List.rec (motive:=fun _=>Nat → List Word → Nat → Option (Nat × List Word × Nat))
   (fun f s r=>some (f,s,r))
   (fun w _ next f s r =>
    q7 (Nat.land w cut) fun v =>
     @Bool.rec (fun _=>Option (Nat × List Word × Nat))
      (@Bool.rec (fun _=>Option (Nat × List Word × Nat))
       (@Nat.rec (fun _=>Option (Nat × List Word × Nat)) none
        (fun r1 _ => @Nat.rec (fun _=>Option (Nat × List Word × Nat)) none
         (fun r2 _=>next f (v :: s) r2) r1) r)
       (@Nat.rec (fun _=>Option (Nat × List Word × Nat)) none
        (fun r1 _=>next f s r1) r)
       (zn (qZ v stock) (qZ v s)))
      (next (Nat.add f 1) s r)
      (zn (Nat.beq v 0) (Nat.beq v cut)))
   l) fl0 seen0 rem0=some (fl,seenOut,remOut) →
  fl=fl0+z5 cut l ∧
  seenOut=(List.rec (motive:=fun _=>List Word → List Word) id
   (fun w _ next s=>next (zv cut stock s w)) l) seen0 ∧
  l.length+seenOut.length+remOut=z5 cut l+seen0.length+rem0 by
  have h0:=gen words 0 [] sl h
  exact ⟨by simpa using h0.1,h0.2.1,by simpa [h0.1] using h0.2.2⟩
 intro l
 induction l with
 | nil =>
  intro fl0 seen0 rem0 hr
  have heq:=Option.some.inj hr
  have h1 : fl0=fl:=congrArg Prod.fst heq
  have h2 : seen0=seenOut:=congrArg (fun p=>p.2.1) heq
  have h3 : rem0=remOut:=congrArg (fun p=>p.2.2) heq
  subst h1;subst h2;subst h3
  exact ⟨rfl,rfl,by simp [z5]⟩
 | cons w ws ih =>
  intro fl0 seen0 rem0 hr
  dsimp only at hr
  rw [ql] at hr
  have hmf : zn (Nat.beq (Nat.land w cut) 0) (Nat.beq (Nat.land w cut) cut)=qW cut w:=by
   rw [zQ];rfl
  rw [hmf] at hr
  cases hm : qW cut w
  · rw [hm] at hr;dsimp only at hr
    have hfc : z5 cut (w :: ws)=z5 cut ws:=by
     change (if qW cut w then z5 cut ws+1 else z5 cut ws)=_;rw [hm];rfl
    have hflat0 : ((w&&&cut==0)||(w&&&cut==cut))=false:=by
     simpa [qW] using hm
    rw [zQ,za,za] at hr
    cases hmem : (stock.contains (Nat.land w cut)||seen0.contains (Nat.land w cut))
    · rw [hmem] at hr;dsimp only at hr
      cases rem0 with
      | zero=>exact nomatch hr
      | succ r1 =>
       cases r1 with
       | zero=>exact nomatch hr
       | succ r2 =>
        obtain ⟨h1,h2,h3⟩:=ih fl0 ((Nat.land w cut) :: seen0) r2 hr
        have hsw : zv cut stock seen0 w=(Nat.land w cut) :: seen0:=by
         dsimp only [zv]
         have hcond : (((w&&&cut==0)||(w&&&cut==cut))||stock.contains (w&&&cut)||seen0.contains (w&&&cut))=false:=by
          rw [hflat0,Bool.false_or];simpa [Bool.or_assoc] using hmem
         rw [hcond];rfl
        dsimp only
        rw [hfc,hsw]
        exact ⟨h1,h2,by simp only [List.length_cons] at h3 ⊢;omega⟩
    · rw [hmem] at hr;dsimp only at hr
      cases rem0 with
      | zero=>exact nomatch hr
      | succ r1 =>
       obtain ⟨h1,h2,h3⟩:=ih fl0 seen0 r1 hr
       have hsw : zv cut stock seen0 w=seen0:=by
        dsimp only [zv]
        have hcond : (((w&&&cut==0)||(w&&&cut==cut))||stock.contains (w&&&cut)||seen0.contains (w&&&cut))=true:=by
         rw [hflat0,Bool.false_or];simpa [Bool.or_assoc] using hmem
        rw [hcond];rfl
       dsimp only
       rw [hfc,hsw]
       exact ⟨h1,h2,by simp only [List.length_cons] at h3 ⊢;omega⟩
  · rw [hm] at hr;dsimp only at hr
    obtain ⟨h1,h2,h3⟩:=ih (Nat.add fl0 1) seen0 rem0 hr
    have hfc : z5 cut (w :: ws)=z5 cut ws+1:=by
     change (if qW cut w then z5 cut ws+1 else z5 cut ws)=_;rw [hm];rfl
    have hsw : zv cut stock seen0 w=seen0:=by
     dsimp only [zv]
     have hflat1 : ((w&&&cut==0)||(w&&&cut==cut))=true:=by
      simpa [qW] using hm
     rw [hflat1];rfl
    dsimp only
    rw [hfc,hsw]
    exact ⟨by change fl=fl0+1+z5 cut ws at h1;omega,h2,by simp only [List.length_cons] at h3 ⊢;omega⟩
theorem q22 (mask : Word) (stock : List Word) (history : List (Word × Word × Word)) :
  zc mask stock history []=[]:=by
 induction history with
 | nil=>rfl
 | cons r rest ih =>
  change zc mask stock rest (if ([] : List Word).contains (r.1&&&mask) then _ else [])=[]
  exact ih
theorem wv (mask : Word) (recipes : List (Word × Word × Word)) (bank : List Word) (nl : Nat) :
  qd mask [] recipes bank nl=([],0):=by
 unfold qd
 induction recipes generalizing bank nl with
 | nil=>rfl
 | cons r rest ih =>
  dsimp only
  rw [zG]
  simp only [List.contains_nil,Bool.false_and, ↓reduceIte]
  exact ih bank nl
theorem ul {mask : Word} {stock words : List Word}
 (h : zC mask stock words=[]) :
 words.all (fun w=>qC mask stock (w&&&mask))=true:=by
 suffices gen : ∀ (l seen : List Word),
  (List.rec (motive:=fun _=>List Word → List Word) id
   (fun w _ next s=>next (zv mask stock s w)) l) seen=[] →
  seen=[] ∧ l.all (fun w=>qC mask stock (w&&&mask))=true from (gen words [] h).2
 intro l
 induction l with
 | nil=>intro seen hs;exact ⟨hs,rfl⟩
 | cons w ws ih =>
  intro seen hs
  obtain ⟨hsw,hall⟩:=ih (zv mask stock seen w) hs
  dsimp only [zv] at hsw
  cases hc : (((w&&&mask==0)||(w&&&mask==mask))||stock.contains (w&&&mask)||seen.contains (w&&&mask))
  · rw [hc] at hsw;simp at hsw
  · rw [hc] at hsw
    have hse : seen=[]:=by simpa using hsw
    subst hse
    have hav : qC mask stock (w&&&mask)=true:=by
     unfold qC
     simpa [List.contains_nil,Bool.or_false] using hc
    exact ⟨rfl,by simp [hav,hall]⟩
def yS (mask : Word) (stock : List Word) (word : Word) (seen : List Word) (rem : Nat) :
  Option (List Word × Nat) :=
 q7 (Nat.land word mask) fun v =>
  @Bool.rec (fun _=>Option (List Word × Nat))
   (@Nat.rec (fun _=>Option (List Word × Nat)) none (fun r' _=>some (v :: seen,r')) rem)
   (some (seen,rem))
   (zn (Nat.beq v 0) (zn (Nat.beq v mask) (zn (qZ v stock) (qZ v seen))))
theorem uI {mask : Word} {stock : List Word} {word : Word} {seen seenOut : List Word} {rem remOut : Nat}
 (h : yS mask stock word seen rem=some (seenOut,remOut)) :
 seenOut=zv mask stock seen word:=by
 unfold yS at h
 rw [ql,zQ,zQ,zQ,za,za] at h
 have hcEq : (Nat.beq (Nat.land word mask) 0||(Nat.beq (Nat.land word mask) mask ||
  (stock.contains (Nat.land word mask)||seen.contains (Nat.land word mask)))) =
  (((word&&&mask==0)||(word&&&mask==mask))||stock.contains (word&&&mask)||seen.contains (word&&&mask)):=by
  rw [qA,qA,Bool.or_assoc,Bool.or_assoc];rfl
 rw [hcEq] at h
 dsimp only [zv]
 cases hc : (((word&&&mask==0)||(word&&&mask==mask))||stock.contains (word&&&mask)||seen.contains (word&&&mask))
 · rw [hc] at h;dsimp only at h
   cases rem with
   | zero=>exact nomatch h
   | succ r'=>exact (congrArg Prod.fst (Option.some.inj h)).symm
 · rw [hc] at h;dsimp only at h
   exact (congrArg Prod.fst (Option.some.inj h)).symm
def yO (mask : Word) (stock : List Word) (history : List (Word × Word × Word))
  (start : List Word) (rem : Nat) : Option (List Word) :=
 (List.rec (motive:=fun _=>List Word → Nat → Option (List Word))
  (fun s _=>some s)
  (fun rec _ next seen r =>
   q7 (Nat.land rec.1 mask) fun vm =>
    @Bool.rec (fun _=>Option (List Word))
     (next seen r)
     (@Option.rec (List Word × Nat) (fun _=>Option (List Word)) none
      (fun p1 => @Option.rec (List Word × Nat) (fun _=>Option (List Word)) none
       (fun p2=>next p2.1 p2.2)
       (yS mask stock rec.2.2 p1.1 p1.2))
      (yS mask stock rec.2.1 seen r))
     (qZ vm seen))
  history) start rem
theorem wK {mask : Word} {stock : List Word} {history : List (Word × Word × Word)}
 {start res : List Word} {rem : Nat}
 (h : yO mask stock history start rem=some res) :
 res=zc mask stock history start:=by
 unfold yO at h
 induction history generalizing start rem with
 | nil=>exact (Option.some.inj h).symm
 | cons rec rest ih =>
  obtain ⟨out,a,b⟩:=rec
  dsimp only at h
  rw [ql,za] at h
  change _=zc mask stock rest (if start.contains (out&&&mask) then zv mask stock (zv mask stock start a) b else start)
  have hl : Nat.land out mask=out&&&mask:=rfl
  rw [hl] at h
  cases hc : start.contains (out&&&mask)
  · rw [hc] at h;dsimp only at h;exact ih h
  · rw [hc] at h;dsimp only at h
    cases h1 : yS mask stock a start rem with
    | none=>rw [h1] at h;exact nomatch h
    | some p1 =>
     rw [h1] at h;dsimp only at h
     cases h2 : yS mask stock b p1.1 p1.2 with
     | none=>rw [h2] at h;exact nomatch h
     | some p2 =>
      rw [h2] at h;dsimp only at h
      have heq1:=uI h1
      have heq2:=uI h2
      simp only [↓reduceIte]
      rw [ih h,heq2,heq1]
def yr (q4 : Bool) (n : Nat) (state : qc) (bound : q2) : Bool :=
 let (cut,stock,qY,y0,_):=bound
 let (q8,nots,ws,history):=state
 let lower1Eff:=qad y0 (Nat.add qY 1)
 let maxLower :=
  @Bool.rec (fun _=>Nat)
   (@Bool.rec (fun _=>Nat) qY (qaf qY lower1Eff) q4)
   lower1Eff
   (Nat.beq nots 1)
 let need:=Nat.add q8 1
 let lim:=Nat.add n maxLower
 @Bool.rec (fun _=>Bool) false
  (@Option.rec (Nat × List Word × Nat) (fun _=>Bool) false
   (fun fs =>
    let flats:=fs.1
    let start:=fs.2.1
    let remSl:=fs.2.2
    q7 (Nat.sub q8 flats) fun yX =>
     @List.rec Word (fun _=>Bool)
      (Nat.blt yX (@Bool.rec (fun _=>Nat) qY lower1Eff (Nat.beq nots 1)))
      (fun _ _ _ =>
       @Option.rec (List Word) (fun _=>Bool) false
        (fun needed =>
         @Bool.rec (fun _=>Bool) false
          (let nl := @Bool.rec (fun _=>Nat) 0 1 (qS (Nat.beq nots 0) q4)
           let res:=zK cut needed (q2r history) stock nl
           ye res.1 fun replay =>
            let effLower := @Bool.rec (fun _=>Nat) qY lower1Eff
             (zn (Nat.beq nots 1) (kq (Nat.beq res.2 0)))
            qS (Nat.blt (Nat.add (zz replay) yX) effLower)
             (q11 cut (q77 replay stock) ws))
          (Nat.blt (Nat.add (zz needed) yX) maxLower))
        (yO cut stock history start remSl))
      start)
   (wL cut stock ws (Nat.sub lim need)))
  (Nat.ble need lim)
theorem uS {q4 : Bool} {target : Word} {state : qc} {bound : q2}
 (hgoal : (((target&&&bound.1)==bound.2.2.2.2)&&(bound.2.2.2.2 != 0)&&(bound.2.2.2.2 != bound.1))=true)
 (hok : yr q4 state.2.2.1.length state bound=true) :
 y4 q4 target state bound=true:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 obtain ⟨cut,stock,qY,y0,goal⟩:=bound
 unfold yr at hok
 unfold y4
 simp only [ql,zV,zG,wm,
  qR,zQ,uP,q7M,wJ,yd,q78,q8q,qac,qae] at hok ⊢
 have hmax : (@Bool.rec (fun _=>Nat)
  (@Bool.rec (fun _=>Nat) qY (max qY (min y0 (qY+1))) q4)
  (min y0 (qY+1)) (Nat.beq nots 1)) =
  (if (nots==1)=true then min y0 (qY+1)
   else if q4=true then max qY (min y0 (qY+1)) else qY):=by
  rw [qA];cases (nots==1) <;> cases q4 <;> rfl
 have hnl : (@Bool.rec (fun _=>Nat) 0 1 (Nat.beq nots 0&&q4)) =
  (if ((nots==0)&&q4)=true then 1 else 0):=by
  rw [qA];cases (nots==0) <;> cases q4 <;> rfl
 have hbrec : ∀ b : Bool,(@Bool.rec (fun _=>Nat) qY (min y0 (qY+1)) b) =
  (if b=true then min y0 (qY+1) else qY):=fun b=>by cases b <;> rfl
 rw [hmax] at hok
 have hEffLe : (if (nots==1)=true then min y0 (qY+1) else qY) ≤
  (if (nots==1)=true then min y0 (qY+1)
   else if q4=true then max qY (min y0 (qY+1)) else qY):=by
  cases (nots==1) <;> cases q4 <;> simp [Nat.le_max_left]
 generalize hmaxDef : (if (nots==1)=true then min y0 (qY+1)
  else if q4=true then max qY (min y0 (qY+1)) else qY)=maxL at hok hEffLe ⊢
 cases hle : Nat.ble (Nat.add q8 1) (Nat.add ws.length maxL)
 · rw [hle] at hok;exact Bool.noConfusion hok
 · rw [hle] at hok;dsimp only at hok
   cases hfs : wL cut stock ws (Nat.sub (Nat.add ws.length maxL) (Nat.add q8 1)) with
   | none=>rw [hfs] at hok;exact Bool.noConfusion hok
   | some fs =>
    obtain ⟨fl,start,remSl⟩:=fs
    rw [hfs] at hok;dsimp only at hok
    obtain ⟨hfeq,hseq,_⟩:=q3Q hfs
    subst fl
    cases hstNil : start with
    | nil =>
     rw [hstNil] at hok hseq;dsimp only at hok
     have hstEmpty : zC cut stock ws=[]:=hseq.symm
     rw [qA,hbrec] at hok
     have hltEff : q8 - z5 cut ws < (if (nots==1)=true then min y0 (qY+1) else qY) :=
      Nat.blt_eq.mp hok
     have hltMax : q8 - z5 cut ws < maxL:=Nat.lt_of_lt_of_le hltEff hEffLe
     have hremT : Nat.blt (q8 - z5 cut ws) maxL=true:=Nat.blt_eq.mpr hltMax
     have hav : ws.all (fun w=>qC cut ([] ++ stock) (w&&&cut))=true :=
      ul hstEmpty
     rw [hgoal,hstEmpty,q22,wv]
     simp only [Bool.true_and,hremT,List.length_nil,Nat.zero_add, ↓reduceIte,bne_self_eq_false,Bool.or_false,
      Nat.blt_eq.mpr hltEff,hav]
    | cons w0 ws0 =>
     rw [hstNil] at hok hseq;dsimp only at hok
     cases hcl : yO cut stock history (w0 :: ws0) remSl with
     | none=>rw [hcl] at hok;exact Bool.noConfusion hok
     | some needed =>
      rw [hcl] at hok;dsimp only at hok
      have hneedEq : needed=zc cut stock history (zC cut stock ws):=by
       rw [← hseq];exact wK hcl
      subst hneedEq
      have hndEq : Nat.blt (Nat.add (zc cut stock history (zC cut stock ws)).length (Nat.sub q8 (z5 cut ws))) maxL =
       Nat.blt ((zc cut stock history (zC cut stock ws)).length+(q8 - z5 cut ws)) maxL:=rfl
      rw [hndEq] at hok
      cases hnd : Nat.blt ((zc cut stock history (zC cut stock ws)).length+(q8 - z5 cut ws)) maxL
      · rw [hnd] at hok;exact Bool.noConfusion hok
      · rw [hnd] at hok;simp only [↓reduceIte] at hok
        have hltNd : (zc cut stock history (zC cut stock ws)).length+(q8 - z5 cut ws) < maxL:=Nat.blt_eq.mp hnd
        have hstartLe : (zC cut stock ws).length ≤ (zc cut stock history (zC cut stock ws)).length:=by
         suffices hgen : ∀ (hist : List (Word × Word × Word)) (s : List Word),s.length ≤ (zc cut stock hist s).length from hgen history _
         intro hist
         induction hist with
         | nil=>intro s;exact Nat.le_refl _
         | cons r rs ih =>
          intro s
          change s.length ≤ (zc cut stock rs (if s.contains (r.1&&&cut) then zv cut stock (zv cut stock s r.2.1) r.2.2 else s)).length
          have hswLe : ∀ t x,t.length ≤ (zv cut stock t x).length:=fun t x=>by
           dsimp only [zv];split <;> simp
          cases s.contains (r.1&&&cut)
          · exact ih s
          · exact Nat.le_trans (Nat.le_trans (hswLe s r.2.1) (hswLe _ r.2.2)) (ih _)
        have hremT : Nat.blt (q8 - z5 cut ws) maxL=true:=Nat.blt_eq.mpr (by omega)
        have hstT : Nat.blt ((zC cut stock ws).length+(q8 - z5 cut ws)) maxL=true:=Nat.blt_eq.mpr (by omega)
        rw [hgoal];simp only [Bool.true_and,hremT,hstT,hnd, ↓reduceIte]
        rw [hnl] at hok
        have heff : (@Bool.rec (fun _=>Nat) qY (min y0 (qY+1))
         (Nat.beq nots 1 || !Nat.beq (qd cut (zc cut stock history (zC cut stock ws)) history.reverse stock (if ((nots==0)&&q4)=true then 1 else 0)).2 0)) =
         (if ((nots==1)||((qd cut (zc cut stock history (zC cut stock ws)) history.reverse stock (if ((nots==0)&&q4)=true then 1 else 0)).2 != 0))=true
          then min y0 (qY+1) else qY):=by
         rw [qA,qA];simp only [bne];exact hbrec _
        rw [heff] at hok
        exact hok
noncomputable def yi : {f : Bool → Nat → qc → q2 → Bool // f=yr}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta yr wL yO yS zK
   jQ yf q11 q77 q2r zz qZ qad qaf qS zn kq
  beta_reduce
  exact rfl
noncomputable def qk (q4 : Bool) (bounds : List q2)
  (state : qc) : Bool :=
 q7 (zz state.2.2.1) fun n =>
  List.rec false (fun bound _ later=>zn (yi.1 q4 n state bound) later) bounds
theorem wl {q4 : Bool} {target : Word} {bounds : List q2} {state : qc}
 (hgoals : ∀ b ∈ bounds,(((target&&&b.1)==b.2.2.2.2)&&(b.2.2.2.2 != 0)&&(b.2.2.2.2 != b.1))=true)
 (hok : qk q4 bounds state=true) :
 k5 q4 target bounds state=true:=by
 unfold qk at hok
 rw [ql,yd] at hok
 induction bounds with
 | nil=>exact Bool.noConfusion hok
 | cons b bs ih =>
  change zn (yi.1 q4 state.2.2.1.length state b) _=true at hok
  rw [zQ,Bool.or_eq_true,show yi.1=yr from yi.2] at hok
  change (y4 q4 target state b||k5 q4 target bs state)=true
  rw [Bool.or_eq_true]
  rcases hok with hb | hbs
  · exact Or.inl (uS (hgoals b List.mem_cons_self) hb)
  · exact Or.inr (ih (fun x hx=>hgoals x (List.mem_cons_of_mem b hx)) hbs)
def kK (bounds : List q2) (idx : Nat) : Option q2 :=
 (List.rec (motive:=fun _=>Nat → Option q2) (fun _=>none)
  (fun b _ next k => @Nat.rec (fun _=>Option q2) (some b) (fun j _=>next j) k) bounds) idx
theorem q4Y {bounds : List q2} {idx : Nat} {b : q2}
  (h : kK bounds idx=some b) : b ∈ bounds:=by
 induction bounds generalizing idx with
 | nil=>exact nomatch h
 | cons a bs ih =>
  cases idx with
  | zero=>exact Option.some.inj h ▸ List.mem_cons_self
  | succ j=>exact List.mem_cons_of_mem a (ih h)
def j0 (bounds : List q2) (q1h code : Nat) : List q2 :=
 (Nat.rec (motive:=fun _=>Nat → List q2) (fun _=>[])
  (fun _ next c =>
   @Bool.rec (fun _=>List q2)
    (q7 (Nat.sub (Nat.land c 31) 1) fun idx =>
     @Option.rec q2 (fun _=>List q2)
      (next (Nat.shiftRight c 5))
      (fun b=>b :: next (Nat.shiftRight c 5))
      (kK bounds idx))
    []
    (Nat.beq c 0)) q1h) code
theorem q1M {bounds : List q2} {q1h code : Nat} {b : q2}
 (h : b ∈ j0 bounds q1h code) : b ∈ bounds:=by
 induction q1h generalizing code with
 | zero=>exact nomatch h
 | succ s ih =>
  unfold j0 at h;dsimp only at h
  cases hc : Nat.beq code 0
  · rw [hc] at h;dsimp only at h;rw [ql] at h
    cases hg : kK bounds (Nat.sub (Nat.land code 31) 1) with
    | none=>rw [hg] at h;exact ih h
    | some a =>
     rw [hg] at h
     rcases List.mem_cons.mp h with rfl | ht
     · exact q4Y hg
     · exact ih ht
  · rw [hc] at h;exact nomatch h
def vl (bounds : List q2) (q1h code : Nat) (k : List q2 → Bool) : Bool :=
 (Nat.rec (motive:=fun _=>Nat → (List q2 → Bool) → Bool) (fun _ acc=>acc [])
  (fun _ next c acc =>
   @Bool.rec (fun _=>Bool)
    (q7 (Nat.sub (Nat.land c 31) 1) fun idx =>
     q7 (Nat.shiftRight c 5) fun c' =>
      @Option.rec q2 (fun _=>Bool)
       (next c' acc)
       (fun b=>next c' (fun rest=>acc (b :: rest)))
       (kK bounds idx))
    (acc [])
    (Nat.beq c 0)) q1h) code k
theorem q2p (bounds : List q2) (q1h code : Nat) (k : List q2 → Bool) :
 vl bounds q1h code k=k (j0 bounds q1h code):=by
 induction q1h generalizing code k with
 | zero=>rfl
 | succ s ih =>
  change @Bool.rec (fun _=>Bool)
   (q7 (Nat.sub (Nat.land code 31) 1) fun idx =>
    q7 (Nat.shiftRight code 5) fun c' =>
     @Option.rec q2 (fun _=>Bool)
      (vl bounds s c' k)
      (fun b=>vl bounds s c' (fun rest=>k (b :: rest)))
      (kK bounds idx))
   (k [])
   (Nat.beq code 0) =
   k (@Bool.rec (fun _=>List q2)
    (q7 (Nat.sub (Nat.land code 31) 1) fun idx =>
     @Option.rec q2 (fun _=>List q2)
      (j0 bounds s (Nat.shiftRight code 5))
      (fun b=>b :: j0 bounds s (Nat.shiftRight code 5))
      (kK bounds idx))
    []
    (Nat.beq code 0))
  cases Nat.beq code 0
  · dsimp only;rw [ql,ql,ql]
    cases kK bounds (Nat.sub (Nat.land code 31) 1) with
    | none=>exact ih (Nat.shiftRight code 5) k
    | some a=>exact ih (Nat.shiftRight code 5) (fun rest=>k (a :: rest))
  · rfl
def uJ (qJ : Bool) (ws : List Word) : Word → Word → Bool :=
 List.rec
  (fun p n=>zn (Nat.beq p 0) (Nat.beq n 0))
  (fun w _ rest p n =>
   zn (Nat.beq p 0) (zn (Nat.beq n 0)
    (q7 (Nat.land p w) fun up =>
     q7 (Nat.land n w) fun down =>
      qS (rest up down)
       (q7 (Nat.xor p up) fun offP =>
        q7 (@Bool.rec (fun _=>Word) (Nat.xor n down) n qJ) (rest offP))))) ws
theorem q5I (qJ : Bool) (ws : List Word) (p n : Word) :
  uJ qJ ws p n=zF qJ ws p n:=by
 induction ws generalizing p n with
 | nil=>change zn (Nat.beq p 0) (Nat.beq n 0)=(Nat.beq p 0||Nat.beq n 0);rw [zQ]
 | cons w ws ih =>
  change zn (Nat.beq p 0) (zn (Nat.beq n 0)
    (q7 (Nat.land p w) fun up =>
     q7 (Nat.land n w) fun down =>
      qS (uJ qJ ws up down)
       (q7 (Nat.xor p up) fun offP =>
        q7 (@Bool.rec (fun _=>Word) (Nat.xor n down) n qJ) (uJ qJ ws offP)))) =
   (Nat.beq p 0||Nat.beq n 0 ||
    qq (p&&&w) (fun up =>
     qq (n&&&w) (fun down =>
      zF qJ ws up down &&
       qq (p^^^up) (fun offP =>
        qq (if qJ then n else n^^^down) (zF qJ ws offP)))))
  simp only [zQ,qR,ql,zG,ih,Bool.or_assoc]
  cases qJ <;> rfl
noncomputable def q0H : {f : Bool → List Word → Word → Word → Bool // f=uJ}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta uJ zn qS
  beta_reduce
  exact rfl
noncomputable def vG : Bool → List Word → Word → Word → Bool:=q0H.1
theorem q31 (qJ : Bool) (ws : List Word) (p n : Word) :
  vG qJ ws p n=zF qJ ws p n :=
 (congrFun (congrFun (congrFun (congrFun q0H.2 qJ) ws) p) n).trans (q5I qJ ws p n)
noncomputable def q1r : {f : List Word → Bool // f=q0.vk}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta q0.vk q0.uh q0.q8i' q0.vg'
   q0.tw' q0.ya q0.vN q0.q0a q0.vZ q0.ua
   q0.orS q0.q2e q0.q6G q0.qp q0.qD'
   q0.kN q0.vu q0.rect' q0.tb'
   q0.q8v q0.bor q0.qah z3
  beta_reduce
  exact rfl
noncomputable def q6i : List Word → Bool:=q1r.1
theorem q73 (ws : List Word) : q6i ws=q0.q21 ws :=
 (congrFun q1r.2 ws).trans (q0.q2Z ws)
def q7O (base : Word) (items : List (Word × Word)) : Word → Word → Word → Bool :=
 List.rec
  (fun _ u1 c1=>q0.q13 (q0.vN u1) (Nat.lor base c1))
  (fun ah _ next u0 u1 c1 =>
   zn
    (qS (Nat.beq (Nat.land u0 ah.2) 0)
     (q7 (Nat.lor u0 ah.2) fun u0'=>next u0' u1 c1))
    (qS (Nat.beq (Nat.land u1 ah.2) 0)
     (q7 (Nat.lor u1 ah.2) fun u1' =>
      q7 (Nat.lor c1 ah.1) fun c1'=>next u0 u1' c1')))
  items
def q6h (base : Word) (items : List (Word × Word)) : Word → Word → Word → Word → Word → Bool :=
 List.rec
  (fun _ u1 u2 c1 c2 =>
   q7 (Nat.lor base c1) fun cov1 =>
    qS (q0.q13 (q0.vN u1) cov1)
     (q0.q13 (q0.vN u2) (Nat.lor cov1 c2)))
  (fun ah _ next u0 u1 u2 c1 c2 =>
   zn
    (qS (Nat.beq (Nat.land u0 ah.2) 0)
     (q7 (Nat.lor u0 ah.2) fun u0'=>next u0' u1 u2 c1 c2))
    (zn
     (qS (Nat.beq (Nat.land u1 ah.2) 0)
      (q7 (Nat.lor u1 ah.2) fun u1' =>
       q7 (Nat.lor c1 ah.1) fun c1'=>next u0 u1' u2 c1' c2))
     (qS (Nat.beq (Nat.land u2 ah.2) 0)
      (q7 (Nat.lor u2 ah.2) fun u2' =>
       q7 (Nat.lor c2 ah.1) fun c2'=>next u0 u1 u2' c1 c2'))))
  items
def vx (t : Word) (rs : List Word) :
  Nat → Word → Word → List (Word × Word) → (Nat → Word → List (Word × Word) → Bool) → Bool :=
 List.rec
  (fun p _ t2 acc k=>k p t2 acc)
  (fun a _ next p o2 t2 acc k =>
   q7 (Nat.land (Nat.land a (Nat.xor t q0.qp)) q0.qp) fun raw =>
    @Bool.rec (fun _=>Bool)
     (q7 (q0.q0a raw) fun h =>
      qS (q0.q13 h a)
       (q7 (Nat.lor o2 h) fun o2' =>
        q7 (Nat.lor t2 (Nat.land o2 h)) fun t2' =>
         next (Nat.add p 1) o2' t2' ((Nat.land a q0.qp,h) :: acc) k))
     (next p o2 t2 ((Nat.land a q0.qp,0) :: acc) k)
     (Nat.beq raw 0))
  rs
def vP (t2 : Word) (ahs : List (Word × Word)) :
  Word → List (Word × Word) → (Word → List (Word × Word) → Bool) → Bool :=
 List.rec
  (fun base items k=>k base items)
  (fun ah _ next base items k =>
   @Bool.rec (fun _=>Bool)
    (next base (ah :: items) k)
    (q7 (Nat.lor base ah.1) fun base'=>next base' items k)
    (Nat.beq (Nat.land ah.2 t2) 0))
  ahs
def jS (maxK K t2 : Word) (ahs : List (Word × Word)) : Bool :=
 @Bool.rec (fun _=>Bool)
  (@Bool.rec (fun _=>Bool)
   (@Bool.rec (fun _=>Bool)
    (vP t2 ahs 0 [] fun base items =>
     @Bool.rec (fun _=>Bool)
      (@Bool.rec (fun _=>Bool) true (q6h base items 0 0 0 0 0) (Nat.beq K 2))
      (q7O base items 0 0 0)
      (Nat.beq K 1))
    false
    (Nat.beq K 0))
   true
   (Nat.blt maxK K))
  true
  (Nat.beq t2 0)
def uO (w : Word) (rows : List Nat) : Word :=
 List.rec 0 (fun r _ kV=>Nat.lor (Nat.land (Nat.shiftRight w r) 1) (Nat.shiftLeft kV 1)) rows
theorem q5K (w : Word) (rows : List Nat) : uO w rows=yJ w rows:=by
 induction rows with
 | nil=>rfl
 | cons r rs ih =>
  change Nat.lor (Nat.land (Nat.shiftRight w r) 1) (Nat.shiftLeft (uO w rs) 1) =
   (((w>>>r)&&&1)|||(yJ w rs<<<1))
  rw [ih];rfl
def q0Z (rows : List Nat) (ws : List Word) : List Word :=
 List.rec [] (fun w _ next=>uO w rows :: next) ws
theorem q71 (c : qw) (ws : List Word) : q0Z c.val ws=ws.map (zy c):=by
 induction ws with
 | nil=>rfl
 | cons w ws ih =>
  change uO w c.val :: q0Z c.val ws=zy c w :: ws.map (zy c)
  rw [q5K,ih];rfl
noncomputable def q10 (maxK : Nat) (rows : List Nat) (q8 : Nat) (ws : List Word) : Bool :=
 ye (q0Z rows ws) fun cws =>
  @Bool.rec (fun _=>Bool)
   (ye (k9 cws) fun l =>
    @Bool.rec (fun _=>Bool)
     (ye (q0.q8i' l) fun rs =>
      q7 (q0.tw' rs 0 0) fun t =>
       vx t rs 0 0 0 [] fun p t2 ahs =>
        qS (Nat.ble p (Nat.add q8 1))
         (jS maxK (Nat.sub (Nat.add q8 1) p) t2 ahs))
     true
     (Nat.blt maxK (Nat.sub (Nat.add q8 1) (zz l))))
   (q6i cws)
   (Nat.beq (zz ws) (Nat.add q8 1))
theorem q1n : q0.q0a 0=0:=by decide +kernel
theorem q3P {t : Word} {rs : List Word}
 (hsub : ∀ a ∈ rs,q0.q13 (q0.ya t a) a=true) :
 ∀ p o2 t2 acc k,
  vx t rs p o2 t2 acc k =
   k (p+(rs.filter (fun a => !Nat.beq (Nat.land (Nat.land a (Nat.xor t q0.qp)) q0.qp) 0)).length)
    (q0.tw (rs.map (q0.ya t)) o2 t2)
    ((rs.map (fun a=>(Nat.land a q0.qp,q0.ya t a))).reverse ++ acc):=by
 induction rs with
 | nil=>intro p o2 t2 acc k;simp [vx,q0.tw]
 | cons a rs ih =>
  intro p o2 t2 acc k
  change q7 (Nat.land (Nat.land a (Nat.xor t q0.qp)) q0.qp) (fun raw =>
   @Bool.rec (fun _=>Bool)
    (q7 (q0.q0a raw) fun h =>
     qS (q0.q13 h a)
      (q7 (Nat.lor o2 h) fun o2' =>
       q7 (Nat.lor t2 (Nat.land o2 h)) fun t2' =>
        vx t rs (Nat.add p 1) o2' t2' ((Nat.land a q0.qp,h) :: acc) k))
    (vx t rs p o2 t2 ((Nat.land a q0.qp,0) :: acc) k)
    (Nat.beq raw 0))=_
  rw [ql]
  have hsubA:=hsub a List.mem_cons_self
  have hsubR : ∀ x ∈ rs,q0.q13 (q0.ya t x) x=true:=fun x hx=>hsub x (List.mem_cons_of_mem _ hx)
  cases hz : Nat.beq (Nat.land (Nat.land a (Nat.xor t q0.qp)) q0.qp) 0
  · dsimp only
    rw [ql]
    have hpriv : q0.q0a (Nat.land (Nat.land a (Nat.xor t q0.qp)) q0.qp)=q0.ya t a:=rfl
    rw [hpriv,hsubA,qR,Bool.true_and,ql,ql,ih hsubR]
    simp only [List.filter_cons,hz,Bool.not_false, ↓reduceIte,List.length_cons,q0.tw,List.map_cons,
     List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1;change p+1+_=p+(_+1);omega
  · dsimp only
    have hraw0 : Nat.land (Nat.land a (Nat.xor t q0.qp)) q0.qp=0:=Nat.beq_eq.mp hz
    have hpriv0 : q0.ya t a=0:=by
     change q0.q0a (Nat.land (Nat.land a (Nat.xor t q0.qp)) q0.qp)=0
     rw [hraw0];exact q1n
    rw [ih hsubR]
    have ho2 : Nat.lor o2 0=o2:=Nat.or_zero o2
    have ht2 : Nat.lor t2 (Nat.land o2 0)=t2:=by change t2|||(o2&&&0)=t2;simp
    simp only [List.filter_cons,hz,Bool.not_true,Bool.false_eq_true, ↓reduceIte,q0.tw,
     List.map_cons,hpriv0,ho2,ht2,List.reverse_cons,List.append_assoc,List.singleton_append]
theorem q30 {t2 : Word} {ahs : List (Word × Word)} :
 ∀ base items k,
  vP t2 ahs base items k =
   k (ahs.foldl (fun b ah=>if Nat.beq (Nat.land ah.2 t2) 0 then Nat.lor b ah.1 else b) base)
    ((ahs.filter (fun ah => !Nat.beq (Nat.land ah.2 t2) 0)).reverse ++ items):=by
 induction ahs with
 | nil=>intro base items k;rfl
 | cons ah ahs ih =>
  intro base items k
  change @Bool.rec (fun _=>Bool)
   (vP t2 ahs base (ah :: items) k)
   (q7 (Nat.lor base ah.1) fun base'=>vP t2 ahs base' items k)
   (Nat.beq (Nat.land ah.2 t2) 0)=_
  cases hz : Nat.beq (Nat.land ah.2 t2) 0
  · dsimp only;rw [ih]
    simp only [List.foldl_cons,hz,Bool.false_eq_true, ↓reduceIte,List.filter_cons,Bool.not_false,
     List.reverse_cons,List.append_assoc,List.singleton_append]
  · dsimp only;rw [ql,ih]
    simp only [List.foldl_cons,hz, ↓reduceIte,List.filter_cons,Bool.not_true,Bool.false_eq_true]
theorem q9t {base : Word} {M : Word × Word × Nat → Prop}
 (hcov : ∀ q,
  (∃ U : Word,(∀ r,U.testBit r=true → ∃ p,M p ∧ p.2.2=1 ∧ p.2.1.testBit r=true) ∧
   (q0.vN U).testBit q=true) →
  base.testBit q=true ∨ ∃ p,M p ∧ p.2.2=1 ∧ p.1.testBit q=true) :
 ∀ (rest : List (Word × Word × Nat)) (u0 u1 c1 : Word),
  (∀ p ∈ rest,M p) → (∀ p ∈ rest,p.2.2 ≤ 1) →
  rest.Pairwise (fun p r=>p.2.2=r.2.2 → Nat.land p.2.1 r.2.1=0) →
  (∀ r ∈ rest,r.2.2=0 → Nat.land u0 r.2.1=0) →
  (∀ r ∈ rest,r.2.2=1 → Nat.land u1 r.2.1=0) →
  (∀ q,u1.testBit q=true → ∃ p,M p ∧ p.2.2=1 ∧ p.2.1.testBit q=true) →
  (∀ p,M p → p.2.2=1 → p ∈ rest ∨ ∀ q,p.1.testBit q=true → c1.testBit q=true) →
  q7O base (rest.map (fun p=>(p.1,p.2.1))) u0 u1 c1=true:=by
 intro rest
 induction rest with
 | nil =>
  intro u0 u1 c1 _ _ _ _ _ Iu1 Ic1
  change q0.q13 (q0.vN u1) (Nat.lor base c1)=true
  unfold q0.q13
  have hsub : Nat.land (q0.vN u1) (Nat.lor base c1)=q0.vN u1:=by
   apply q0.q0B;intro q hq;rw [q0.qX]
   rcases hcov q ⟨u1,Iu1,hq⟩ with hb | ⟨p,hp,hp1,hpq⟩
   · rw [hb];rfl
   · rcases Ic1 p hp hp1 with hm | hc
     · simp at hm
     · rw [hc q hpq];exact Bool.or_true _
  rw [hsub];exact Nat.beq_refl _
 | cons it rest ih =>
  intro u0 u1 c1 hM hK hP Iu0 Iu1 Iu1b Ic1
  have hP':=List.pairwise_cons.mp hP
  have hit : it ∈ it :: rest:=List.mem_cons_self
  have hk:=hK it hit
  change zn
   (qS (Nat.beq (Nat.land u0 it.2.1) 0)
    (q7 (Nat.lor u0 it.2.1) fun u0'=>q7O base (rest.map (fun p=>(p.1,p.2.1))) u0' u1 c1))
   (qS (Nat.beq (Nat.land u1 it.2.1) 0)
    (q7 (Nat.lor u1 it.2.1) fun u1' =>
     q7 (Nat.lor c1 it.1) fun c1'=>q7O base (rest.map (fun p=>(p.1,p.2.1))) u0 u1' c1'))=true
  rw [zQ,qR,qR,ql,ql,ql,Bool.or_eq_true]
  by_cases h0 : it.2.2=0
  · left
    rw [Bool.and_eq_true,Iu0 it hit h0,Nat.beq_refl]
    refine ⟨rfl,ih (Nat.lor u0 it.2.1) u1 c1 (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
     (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_ ?_ Iu1b ?_⟩
    · intro r hr hr0
      apply q0.kO;intro q h1 h2
      rw [q0.qX,Bool.or_eq_true] at h1
      rcases h1 with h1 | h1
      · exact q0.zU _ _ q (Iu0 r (List.mem_cons_of_mem _ hr) hr0) h1 h2
      · exact q0.zU _ _ q (hP'.1 r hr (h0.trans hr0.symm)) h1 h2
    · intro r hr hr1;exact Iu1 r (List.mem_cons_of_mem _ hr) hr1
    · intro p hp hp1
      rcases Ic1 p hp hp1 with hm | hc
      · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
      · exact Or.inr hc
  · right
    have h1 : it.2.2=1:=by omega
    rw [Bool.and_eq_true,Iu1 it hit h1,Nat.beq_refl]
    refine ⟨rfl,ih u0 (Nat.lor u1 it.2.1) (Nat.lor c1 it.1) (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
     (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_ ?_ ?_ ?_⟩
    · intro r hr hr0;exact Iu0 r (List.mem_cons_of_mem _ hr) hr0
    · intro r hr hr1
      apply q0.kO;intro q h1' h2'
      rw [q0.qX,Bool.or_eq_true] at h1'
      rcases h1' with h1' | h1'
      · exact q0.zU _ _ q (Iu1 r (List.mem_cons_of_mem _ hr) hr1) h1' h2'
      · exact q0.zU _ _ q (hP'.1 r hr (h1.trans hr1.symm)) h1' h2'
    · intro q hq
      rw [q0.qX,Bool.or_eq_true] at hq
      rcases hq with hq | hq
      · exact Iu1b q hq
      · exact ⟨it,hM it hit,h1,hq⟩
    · intro p hp hp1
      rcases Ic1 p hp hp1 with hm | hc
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact Or.inr (fun q hq=>by rw [q0.qX,hq];exact Bool.or_true _)
        · exact Or.inl hm
      · exact Or.inr (fun q hq=>by rw [q0.qX,hc q hq];rfl)
theorem q9s {base : Word} {M : Word × Word × Nat → Prop}
 (hcov1 : ∀ q,
  (∃ U : Word,(∀ r,U.testBit r=true → ∃ p,M p ∧ p.2.2=1 ∧ p.2.1.testBit r=true) ∧
   (q0.vN U).testBit q=true) →
  base.testBit q=true ∨ ∃ p,M p ∧ p.2.2=1 ∧ p.1.testBit q=true)
 (hcov2 : ∀ q,
  (∃ U : Word,(∀ r,U.testBit r=true → ∃ p,M p ∧ p.2.2=2 ∧ p.2.1.testBit r=true) ∧
   (q0.vN U).testBit q=true) →
  base.testBit q=true ∨ ∃ p,M p ∧ (p.2.2=1 ∨ p.2.2=2) ∧ p.1.testBit q=true) :
 ∀ (rest : List (Word × Word × Nat)) (u0 u1 u2 c1 c2 : Word),
  (∀ p ∈ rest,M p) → (∀ p ∈ rest,p.2.2 ≤ 2) →
  rest.Pairwise (fun p r=>p.2.2=r.2.2 → Nat.land p.2.1 r.2.1=0) →
  (∀ r ∈ rest,r.2.2=0 → Nat.land u0 r.2.1=0) →
  (∀ r ∈ rest,r.2.2=1 → Nat.land u1 r.2.1=0) →
  (∀ r ∈ rest,r.2.2=2 → Nat.land u2 r.2.1=0) →
  (∀ q,u1.testBit q=true → ∃ p,M p ∧ p.2.2=1 ∧ p.2.1.testBit q=true) →
  (∀ q,u2.testBit q=true → ∃ p,M p ∧ p.2.2=2 ∧ p.2.1.testBit q=true) →
  (∀ p,M p → p.2.2=1 → p ∈ rest ∨ ∀ q,p.1.testBit q=true → c1.testBit q=true) →
  (∀ p,M p → p.2.2=2 → p ∈ rest ∨ ∀ q,p.1.testBit q=true → c2.testBit q=true) →
  q6h base (rest.map (fun p=>(p.1,p.2.1))) u0 u1 u2 c1 c2=true:=by
 intro rest
 induction rest with
 | nil =>
  intro u0 u1 u2 c1 c2 _ _ _ _ _ _ Iu1b Iu2b Ic1 Ic2
  change q7 (Nat.lor base c1) (fun cov1 =>
   qS (q0.q13 (q0.vN u1) cov1)
    (q0.q13 (q0.vN u2) (Nat.lor cov1 c2)))=true
  rw [ql,qR,Bool.and_eq_true]
  constructor
  · unfold q0.q13
    have hsub : Nat.land (q0.vN u1) (Nat.lor base c1)=q0.vN u1:=by
     apply q0.q0B;intro q hq;rw [q0.qX]
     rcases hcov1 q ⟨u1,Iu1b,hq⟩ with hb | ⟨p,hp,hp1,hpq⟩
     · rw [hb];rfl
     · rcases Ic1 p hp hp1 with hm | hc;simp at hm;rw [hc q hpq];exact Bool.or_true _
    rw [hsub];exact Nat.beq_refl _
  · unfold q0.q13
    have hsub : Nat.land (q0.vN u2) (Nat.lor (Nat.lor base c1) c2)=q0.vN u2:=by
     apply q0.q0B;intro q hq;rw [q0.qX,q0.qX]
     rcases hcov2 q ⟨u2,Iu2b,hq⟩ with hb | ⟨p,hp,hp1 | hp2,hpq⟩
     · rw [hb];rfl
     · rcases Ic1 p hp hp1 with hm | hc;simp at hm;rw [hc q hpq];simp
     · rcases Ic2 p hp hp2 with hm | hc;simp at hm;rw [hc q hpq];simp
    rw [hsub];exact Nat.beq_refl _
 | cons it rest ih =>
  intro u0 u1 u2 c1 c2 hM hK hP Iu0 Iu1 Iu2 Iu1b Iu2b Ic1 Ic2
  have hP':=List.pairwise_cons.mp hP
  have hit : it ∈ it :: rest:=List.mem_cons_self
  have hk:=hK it hit
  change zn
   (qS (Nat.beq (Nat.land u0 it.2.1) 0)
    (q7 (Nat.lor u0 it.2.1) fun u0'=>q6h base (rest.map (fun p=>(p.1,p.2.1))) u0' u1 u2 c1 c2))
   (zn
    (qS (Nat.beq (Nat.land u1 it.2.1) 0)
     (q7 (Nat.lor u1 it.2.1) fun u1' =>
      q7 (Nat.lor c1 it.1) fun c1'=>q6h base (rest.map (fun p=>(p.1,p.2.1))) u0 u1' u2 c1' c2))
    (qS (Nat.beq (Nat.land u2 it.2.1) 0)
     (q7 (Nat.lor u2 it.2.1) fun u2' =>
      q7 (Nat.lor c2 it.1) fun c2'=>q6h base (rest.map (fun p=>(p.1,p.2.1))) u0 u1 u2' c1 c2')))=true
  simp only [zQ,qR,ql,Bool.or_eq_true,Bool.and_eq_true]
  by_cases h0 : it.2.2=0
  · left
    rw [Iu0 it hit h0,Nat.beq_refl]
    refine ⟨rfl,ih (Nat.lor u0 it.2.1) u1 u2 c1 c2 (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
     (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_
     (fun r hr hr1=>Iu1 r (List.mem_cons_of_mem _ hr) hr1)
     (fun r hr hr2=>Iu2 r (List.mem_cons_of_mem _ hr) hr2) Iu1b Iu2b ?_ ?_⟩
    · intro r hr hr0
      apply q0.kO;intro q h1 h2
      rw [q0.qX,Bool.or_eq_true] at h1
      rcases h1 with h1 | h1
      · exact q0.zU _ _ q (Iu0 r (List.mem_cons_of_mem _ hr) hr0) h1 h2
      · exact q0.zU _ _ q (hP'.1 r hr (h0.trans hr0.symm)) h1 h2
    · intro p hp hp1;rcases Ic1 p hp hp1 with hm | hc
      · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
      · exact Or.inr hc
    · intro p hp hp2;rcases Ic2 p hp hp2 with hm | hc
      · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
      · exact Or.inr hc
  · by_cases h1 : it.2.2=1
    · right;left
      rw [Iu1 it hit h1,Nat.beq_refl]
      refine ⟨rfl,ih u0 (Nat.lor u1 it.2.1) u2 (Nat.lor c1 it.1) c2 (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
       (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2
       (fun r hr hr0=>Iu0 r (List.mem_cons_of_mem _ hr) hr0) ?_
       (fun r hr hr2=>Iu2 r (List.mem_cons_of_mem _ hr) hr2) ?_ Iu2b ?_ ?_⟩
      · intro r hr hr1
        apply q0.kO;intro q ha hb
        rw [q0.qX,Bool.or_eq_true] at ha
        rcases ha with ha | ha
        · exact q0.zU _ _ q (Iu1 r (List.mem_cons_of_mem _ hr) hr1) ha hb
        · exact q0.zU _ _ q (hP'.1 r hr (h1.trans hr1.symm)) ha hb
      · intro q hq;rw [q0.qX,Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Iu1b q hq
        · exact ⟨it,hM it hit,h1,hq⟩
      · intro p hp hp1;rcases Ic1 p hp hp1 with hm | hc
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inr (fun q hq=>by rw [q0.qX,hq];exact Bool.or_true _)
          · exact Or.inl hm
        · exact Or.inr (fun q hq=>by rw [q0.qX,hc q hq];rfl)
      · intro p hp hp2;rcases Ic2 p hp hp2 with hm | hc
        · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
        · exact Or.inr hc
    · right;right
      have h2 : it.2.2=2:=by omega
      rw [Iu2 it hit h2,Nat.beq_refl]
      refine ⟨rfl,ih u0 u1 (Nat.lor u2 it.2.1) c1 (Nat.lor c2 it.1) (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
       (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2
       (fun r hr hr0=>Iu0 r (List.mem_cons_of_mem _ hr) hr0)
       (fun r hr hr1=>Iu1 r (List.mem_cons_of_mem _ hr) hr1) ?_ Iu1b ?_ ?_ ?_⟩
      · intro r hr hr2
        apply q0.kO;intro q ha hb
        rw [q0.qX,Bool.or_eq_true] at ha
        rcases ha with ha | ha
        · exact q0.zU _ _ q (Iu2 r (List.mem_cons_of_mem _ hr) hr2) ha hb
        · exact q0.zU _ _ q (hP'.1 r hr (h2.trans hr2.symm)) ha hb
      · intro q hq;rw [q0.qX,Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Iu2b q hq
        · exact ⟨it,hM it hit,h2,hq⟩
      · intro p hp hp1;rcases Ic1 p hp hp1 with hm | hc
        · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
        · exact Or.inr hc
      · intro p hp hp2;rcases Ic2 p hp hp2 with hm | hc
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inr (fun q hq=>by rw [q0.qX,hq];exact Bool.or_true _)
          · exact Or.inl hm
        · exact Or.inr (fun q hq=>by rw [q0.qX,hc q hq];rfl)
theorem q5J (t2 : Word) (ahs : List (Word × Word)) (b q : Word) :
 (ahs.foldl (fun acc ah=>if Nat.beq (Nat.land ah.2 t2) 0 then Nat.lor acc ah.1 else acc) b).testBit q=true ↔
  b.testBit q=true ∨ ∃ ah ∈ ahs,Nat.beq (Nat.land ah.2 t2) 0=true ∧ ah.1.testBit q=true:=by
 induction ahs generalizing b with
 | nil=>simp
 | cons ah ahs ih =>
  simp only [List.foldl_cons,ih,List.mem_cons]
  cases hz : Nat.beq (Nat.land ah.2 t2) 0
  · simp only [hz,Bool.false_eq_true, ↓reduceIte]
    constructor
    · rintro (hb | ⟨x,hx,h1,h2⟩)
      · exact Or.inl hb
      · exact Or.inr ⟨x,Or.inr hx,h1,h2⟩
    · rintro (hb | ⟨x,rfl | hx,h1,h2⟩)
      · exact Or.inl hb
      · rw [hz] at h1;exact Bool.noConfusion h1
      · exact Or.inr ⟨x,hx,h1,h2⟩
  · simp only [hz, ↓reduceIte,q0.qX,Bool.or_eq_true,true_and]
    constructor
    · rintro ((hb | ha) | ⟨x,hx,h1,h2⟩)
      · exact Or.inl hb
      · exact Or.inr ⟨ah,Or.inl rfl,hz,ha⟩
      · exact Or.inr ⟨x,Or.inr hx,h1,h2⟩
    · rintro (hb | ⟨x,rfl | hx,h1,h2⟩)
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨x,hx,h1,h2⟩
theorem q1N (t t2 : Word) (rs : List Word) :
 ((rs.map (fun a=>(Nat.land a q0.qp,q0.ya t a))).reverse.foldl
  (fun acc ah=>if Nat.beq (Nat.land ah.2 t2) 0 then Nat.lor acc ah.1 else acc) 0) =
 Nat.land (q0.q1K t t2 rs) q0.qp:=by
 apply Nat.eq_of_testBit_eq;intro q
 apply Bool.eq_iff_iff.mpr
 rw [q5J,q0.qM,Bool.and_eq_true,q0.jZ,decide_eq_true_eq]
 simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,List.mem_reverse,List.mem_map]
 constructor
 · rintro ⟨ah,⟨a,ha,rfl⟩,hdisj,hq⟩
   rw [q0.qM,q0.jZ,Bool.and_eq_true,decide_eq_true_eq] at hq
   exact ⟨q0.q9j t t2 q rs a ha hdisj hq.1,hq.2⟩
 · rintro ⟨hf,hq144⟩
   suffices h : ∀ xs : List Word,(q0.q1K t t2 xs).testBit q=true →
    ∃ a ∈ xs,Nat.beq (Nat.land (q0.ya t a) t2) 0=true ∧ a.testBit q=true by
    obtain ⟨a,ha,hd,hqa⟩:=h rs hf
    exact ⟨(Nat.land a q0.qp,q0.ya t a),⟨a,ha,rfl⟩,hd,
     by rw [q0.qM,q0.jZ,hqa,decide_eq_true hq144];rfl⟩
   intro xs
   induction xs with
   | nil=>intro h;simp [q0.q1K] at h
   | cons a xs ih =>
    intro h
    change (cond (Nat.beq (Nat.land (q0.ya t a) t2) 0)
     (Nat.lor a (q0.q1K t t2 xs)) (q0.q1K t t2 xs)).testBit q=true at h
    cases hd : Nat.beq (Nat.land (q0.ya t a) t2) 0
    · rw [hd] at h
      obtain ⟨x,hx,hxd,hxq⟩:=ih h
      exact ⟨x,List.mem_cons_of_mem _ hx,hxd,hxq⟩
    · rw [hd] at h
      change (Nat.lor a (q0.q1K t t2 xs)).testBit q=true at h
      rw [q0.qX,Bool.or_eq_true] at h
      rcases h with ha | hr
      · exact ⟨a,List.mem_cons_self,hd,ha⟩
      · obtain ⟨x,hx,hxd,hxq⟩:=ih hr
        exact ⟨x,List.mem_cons_of_mem _ hx,hxd,hxq⟩
theorem q0L {maxK : Nat} {l : List Word} {K : Nat} {c : Nat → Nat}
 (hCL : q0.vV l K c) :
 jS maxK K
  (q0.tw ((l.map q0.qD).map (q0.ya (q0.tw (l.map q0.qD) 0 0))) 0 0)
  (((l.map q0.qD).map (fun a=>(Nat.land a q0.qp,q0.ya (q0.tw (l.map q0.qD) 0 0) a))).reverse)=true:=by
 let rs:=l.map q0.qD
 let t:=q0.tw rs 0 0
 let t2:=q0.tw (rs.map (q0.ya t)) 0 0
 let ahs:=(rs.map (fun a=>(Nat.land a q0.qp,q0.ya t a))).reverse
 change jS maxK K t2 ahs=true
 unfold jS
 cases ht2 : Nat.beq t2 0
 · dsimp only
   have ht2ne : t2 ≠ 0:=fun hz=>Bool.noConfusion ((Nat.beq_eq.mpr hz).symm.trans ht2)
   cases hcap : Nat.blt maxK K
   · dsimp only
     cases hK0 : Nat.beq K 0
     · dsimp only
       rw [q30]
       have hitems_eq : (ahs.filter (fun ah => !Nat.beq (Nat.land ah.2 t2) 0)).reverse ++ [] =
        (l.filter (fun x => !Nat.beq (Nat.land (q0.k7 l x) t2) 0)).map
         (fun x=>(Nat.land (q0.qD x) q0.qp,q0.k7 l x)):=by
        simp only [ahs,rs,List.append_nil,List.filter_reverse,List.reverse_reverse,List.filter_map,List.map_map]
        rfl
       have hbase_eq : ahs.foldl (fun b ah=>if Nat.beq (Nat.land ah.2 t2) 0 then Nat.lor b ah.1 else b) 0 =
        Nat.land (q0.q1K t t2 rs) q0.qp:=q1N t t2 rs
       rw [hitems_eq,hbase_eq]
       let fl:=l.filter (fun x => !Nat.beq (Nat.land (q0.k7 l x) t2) 0)
       let all:=fl.map (fun x=>(Nat.land (q0.qD x) q0.qp,q0.k7 l x,c x))
       have hall_map : all.map (fun p=>(p.1,p.2.1)) =
        fl.map (fun x=>(Nat.land (q0.qD x) q0.qp,q0.k7 l x)):=by
        simp only [all,List.map_map];rfl
       have ht2_def : t2=q0.qal l:=rfl
       have hmem_all : ∀ p ∈ all, ∃ x ∈ l,q0.jO l x ∧
        p=(Nat.land (q0.qD x) q0.qp,q0.k7 l x,c x):=by
        intro p hp
        obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hp
        obtain ⟨hxl,hxf⟩:=List.mem_filter.mp hx
        refine ⟨x,hxl, ?_,rfl⟩
        apply q0.wR
        rw [← ht2_def]
        cases hb : Nat.beq (Nat.land (q0.k7 l x) t2) 0
        · rfl
        · rw [hb] at hxf;exact Bool.noConfusion hxf
       have hall_pw : all.Pairwise (fun p r=>p.2.2=r.2.2 → Nat.land p.2.1 r.2.1=0):=by
        rw [List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter _ hCL.ne)
        intro x y hx hy hxy hceq
        have hcx : q0.jO l x:=q0.wR (by
         rw [← ht2_def];have:=(List.mem_filter.mp hx).2
         cases hb : Nat.beq (Nat.land (q0.k7 l x) t2) 0;rfl;rw [hb] at this;exact Bool.noConfusion this)
        have hcy : q0.jO l y:=q0.wR (by
         rw [← ht2_def];have:=(List.mem_filter.mp hy).2
         cases hb : Nat.beq (Nat.land (q0.k7 l y) t2) 0;rfl;rw [hb] at this;exact Bool.noConfusion this)
        exact hxy hcx hcy hceq
       have hall_K : ∀ p ∈ all,p.2.2 ≤ K:=by
        intro p hp;obtain ⟨x,hx,hcx,rfl⟩:=hmem_all p hp;exact hCL.le x hx hcx
       have hcov_gen : ∀ i,1 ≤ i → i ≤ K → ∀ q,
        (∃ U : Word,(∀ r,U.testBit r=true → ∃ p,p ∈ all ∧ p.2.2=i ∧ p.2.1.testBit r=true) ∧
         (q0.vN U).testBit q=true) →
        (Nat.land (q0.q1K t t2 rs) q0.qp).testBit q=true ∨
         ∃ p,p ∈ all ∧ (1 ≤ p.2.2 ∧ p.2.2 ≤ i) ∧ p.1.testBit q=true:=by
        intro i hi1 hiK q ⟨U,hU,hUq⟩
        have hq144 : q < 144:=(q0.wh U q hUq).1
        obtain ⟨y,hy,hyq,hyc⟩:=hCL.cov i U hi1 hiK (by
         intro r hr;obtain ⟨p,hp,hpi,hpr⟩:=hU r hr
         obtain ⟨x,hx,hcx,rfl⟩:=hmem_all p hp
         exact ⟨x,hx,hcx,hpi,hpr⟩) q hUq
        cases hb : Nat.beq (Nat.land (q0.k7 l y) t2) 0
        · right
          have hcy : q0.jO l y:=q0.wR (by rwa [← ht2_def])
          refine ⟨(Nat.land (q0.qD y) q0.qp,q0.k7 l y,c y), ?_,hyc hcy, ?_⟩
          · exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hy,by rw [hb];rfl⟩)
          · rw [q0.qM,q0.jZ,hyq,decide_eq_true hq144];rfl
        · left
          rw [q0.qM,q0.jZ,decide_eq_true hq144,Bool.and_true]
          exact q0.q9j t t2 q rs (q0.qD y) (List.mem_map_of_mem hy) hb hyq
       cases hK1 : Nat.beq K 1
       · dsimp only
         cases hK2 : Nat.beq K 2
         · rfl
         · dsimp only
           have hKe2 : K=2:=Nat.beq_eq.mp hK2
           rw [← hall_map]
           apply q9s (M:=(· ∈ all))
           · intro q hq
             rcases hcov_gen 1 (by omega) (by omega) q hq with hl | ⟨p,hp,⟨hp1,hp2⟩,hpq⟩
             · exact Or.inl hl
             · exact Or.inr ⟨p,hp,by omega,hpq⟩
           · intro q hq
             rcases hcov_gen 2 (by omega) (by omega) q hq with hl | ⟨p,hp,⟨hp1,hp2⟩,hpq⟩
             · exact Or.inl hl
             · exact Or.inr ⟨p,hp,by omega,hpq⟩
           · exact fun p hp=>hp
           · intro p hp;have:=hall_K p hp;omega
           · exact hall_pw
           · intro _ _ _;simp
           · intro _ _ _;simp
           · intro _ _ _;simp
           · intro _ h;simp at h
           · intro _ h;simp at h
           · exact fun p hp _=>Or.inl hp
           · exact fun p hp _=>Or.inl hp
       · dsimp only
         have hKe1 : K=1:=Nat.beq_eq.mp hK1
         rw [← hall_map]
         apply q9t (M:=(· ∈ all))
         · intro q hq
           rcases hcov_gen 1 (by omega) (by omega) q hq with hl | ⟨p,hp,⟨hp1,hp2⟩,hpq⟩
           · exact Or.inl hl
           · exact Or.inr ⟨p,hp,by omega,hpq⟩
         · exact fun p hp=>hp
         · intro p hp;have:=hall_K p hp;omega
         · exact hall_pw
         · intro _ _ _;simp
         · intro _ _ _;simp
         · intro _ h;simp at h
         · exact fun p hp _=>Or.inl hp
     · exfalso
       have hKe0 : K=0:=Nat.beq_eq.mp hK0
       have ht2_def : t2=q0.qal l:=rfl
       have hex : ∃ q,t2.testBit q=true:=by
        by_contra! hall;apply ht2ne;apply Nat.eq_of_testBit_eq;intro q
        have hq:=hall q;cases h : t2.testBit q <;> simp_all
       obtain ⟨q,hq⟩:=hex
       have hpw : (rs.map (q0.ya t)).Pairwise (fun a b => ¬(a.testBit q=true ∧ b.testBit q=true)):=by
        rw [List.pairwise_map,List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ hCL.ne
        intro a b ha hb hne ⟨haq,hbq⟩
        have haq' : (q0.k7 l a).testBit q=true:=haq
        have hbq' : (q0.k7 l b).testBit q=true:=hbq
        have hca : q0.jO l a:=fun hz=>by
         have:=congrArg (fun n : Nat=>n.testBit q) hz
         rw [q0.qM, ← ht2_def,haq',hq,Nat.zero_testBit] at this;exact Bool.noConfusion this
        have hcb : q0.jO l b:=fun hz=>by
         have:=congrArg (fun n : Nat=>n.testBit q) hz
         rw [q0.qM, ← ht2_def,hbq',hq,Nat.zero_testBit] at this;exact Bool.noConfusion this
        have h0a:=hCL.le a ha hca
        have h0b:=hCL.le b hb hcb
        have hdisj:=hne hca hcb (by omega)
        exact q0.zU _ _ q hdisj haq hbq
       have hzero : ∀ (xs : List Word) (o tt : Word),
        tt.testBit q=false → (o.testBit q=true → ∀ a ∈ xs,a.testBit q=false) →
        xs.Pairwise (fun a b => ¬(a.testBit q=true ∧ b.testBit q=true)) →
        (q0.tw xs o tt).testBit q=false:=by
        intro xs;induction xs with
        | nil=>intro o tt htt _ _;exact htt
        | cons a xs ih =>
         intro o tt htt ho hpx
         obtain ⟨ha,hxs⟩:=List.pairwise_cons.mp hpx
         apply ih (Nat.lor o a) (Nat.lor tt (Nat.land o a))
         · rw [q0.qX,Bool.or_eq_false_iff,q0.qM]
           refine ⟨htt, ?_⟩
           cases hox : o.testBit q
           · simp
           · simp [ho hox a List.mem_cons_self]
         · intro hox b hb
           rw [q0.qX,Bool.or_eq_true] at hox
           rcases hox with h1 | h2
           · exact ho h1 b (List.mem_cons_of_mem _ hb)
           · cases hbq : b.testBit q
             · rfl
             · exact False.elim (ha b hb ⟨h2,hbq⟩)
         · exact hxs
       have hf:=hzero _ 0 0 (by simp) (by simp) hpw
       rw [hf] at hq;exact Bool.noConfusion hq
   · rfl
 · rfl
noncomputable def q6g : {f : Nat → List Nat → Nat → List Word → Bool // f=q10}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta q10 q0Z uO k9 qZ jS vx vP
   q7O q6h zz
   q0.q8i' q0.tw' q0.q13 q0.vN q0.q0a
   q0.vZ q0.ua q0.orS q0.q2e q0.q6G
   q0.qp q0.qD' q0.kN q0.vu
   q0.rect' q0.tb' q0.q8v q0.bor q0.qah qS zn kq z3
  beta_reduce
  exact rfl
noncomputable def q9V : Nat → List Nat → Nat → List Word → Bool:=q6g.1
theorem q7N {maxK : Nat} {mask goal : Word} {c : qw} {ws : List Word} {k q8 : Nat}
 (ok : jD goal c) (nd : ws.Nodup) (cap : k ≤ q8)
 (y1 : qf mask goal k 0 ws.toFinset) :
 q9V maxK c.val q8 ws=true:=by
 rw [show q9V=q10 from q6g.2]
 unfold q10
 rw [zV,q71,yd]
 cases htight : Nat.beq ws.length (Nat.add q8 1)
 · dsimp only
   rw [zV,yd]
   cases Nat.blt maxK (Nat.sub (Nat.add q8 1) (k9 (ws.map (zy c))).length)
   · dsimp only
     rw [zV,q0.q0A,ql,q0.q4k]
     obtain ⟨k',S',hk',hsub,hR⟩:=q2Q ok y1
     let l:=k9 (ws.map (zy c))
     have hndL : l.Nodup:=q74 _
     have hsubL : S' ⊆ l.toFinset:=fun x hx=>by
      rw [List.mem_toFinset,q8p];exact List.mem_toFinset.mp (by simpa using hsub hx)
     let l':=S'.toList
     have hnd' : l'.Nodup:=Finset.nodup_toList S'
     have hset' : l'.toFinset=S':=by ext x;simp [l']
     have hlen' : l'.length=S'.card:=Finset.length_toList S'
     obtain ⟨col,hVL⟩:=q0.q4p hnd' (hset'.symm ▸ hR)
     have hsub' : ∀ x ∈ l',x ∈ l:=fun x hx=>List.mem_toFinset.mp (hsubL (Finset.mem_toList.mp hx))
     let tL:=q0.tw (l.map q0.qD) 0 0
     have hprivSub : ∀ x q,(q0.k7 l x).testBit q=true →
      (q0.ya (q0.tw (l'.map q0.qD) 0 0) (q0.qD x)).testBit q=true:=by
      intro x q hq
      apply q70 _ hq
      intro r hr144 hr
      rw [q0.qM,q0.j7,Bool.and_eq_true] at hr ⊢
      refine ⟨hr.1, ?_⟩
      have h1 : tL.testBit r=false:=by
       have:=hr.2;rw [q0.jZ,decide_eq_true hr144] at this
       dsimp only [tL] at this ⊢
       cases h : (q0.tw (l.map q0.qD) 0 0).testBit r <;> simp_all
      have h2 : (q0.tw (l'.map q0.qD) 0 0).testBit r=false:=by
       by_contra ht
       have ht1 : (q0.tw (l'.map q0.qD) 0 0).testBit r=true:=by
        cases h : (q0.tw (l'.map q0.qD) 0 0).testBit r <;> simp_all
       have:=q9l hnd' hsub' ht1
       rw [h1] at this;exact Bool.noConfusion this
      rw [h2,q0.jZ,decide_eq_true hr144];rfl
     have hprivMem : ∀ x ∈ l,
      Nat.land (Nat.land (q0.qD x) (Nat.xor tL q0.qp)) q0.qp ≠ 0 → x ∈ S':=by
      intro x hx hne
      have hex : ∃ q,(Nat.land (Nat.land (q0.qD x) (Nat.xor tL q0.qp)) q0.qp).testBit q=true:=by
       by_contra! hall;apply hne;apply Nat.eq_of_testBit_eq;intro q
       have hq:=hall q;cases h : (Nat.land (Nat.land (q0.qD x) (Nat.xor tL q0.qp)) q0.qp).testBit q <;> simp_all
      obtain ⟨q,hq⟩:=hex
      rw [q0.qM,q0.qM,q0.j7,q0.jZ,
       Bool.and_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hq
      obtain ⟨⟨hrx,htx⟩,hq144⟩:=hq
      have htf : tL.testBit q=false:=by cases h : tL.testBit q <;> simp_all
      obtain ⟨y,hyS,hry⟩:=q0.qa5 hR q hq144
      have hyL : y ∈ l:=List.mem_toFinset.mp (hsubL hyS)
      have hpw:=List.pairwise_map.mp (q0.q40 q (l.map q0.qD) 0 0 htf).2.2
      have hxy : x=y:=by by_contra hne';exact wf hpw hx hyL hne' ⟨hrx,hry⟩
      rwa [hxy]
     have hsubAll : ∀ a ∈ l.map q0.qD,q0.q13 (q0.ya tL a) a=true:=by
      intro a ha;obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
      unfold q0.q13
      apply Nat.beq_eq.mpr
      apply q0.q0B
      intro q hq
      by_cases hnz : Nat.land (Nat.land (q0.qD x) (Nat.xor tL q0.qp)) q0.qp=0
      · exfalso
        have hp0 : q0.ya tL (q0.qD x)=0:=by
         change q0.q0a (Nat.land (Nat.land (q0.qD x) (Nat.xor tL q0.qp)) q0.qp)=0
         rw [hnz];exact q1n
        rw [hp0,Nat.zero_testBit] at hq;exact Bool.noConfusion hq
      · have hx' : x ∈ l':=Finset.mem_toList.mpr (hprivMem x hx hnz)
        exact hVL.2.2.2 x hx' q (hprivSub x q hq)
     rw [q3P hsubAll,qR,Bool.and_eq_true]
     have hpEq : (0+((l.map q0.qD).filter (fun a => !Nat.beq (Nat.land (Nat.land a (Nat.xor tL q0.qp)) q0.qp) 0)).length)=yY l:=by
      unfold yY;dsimp only;rw [q0.q0A,q0.q4k];simp [tL]
     rw [hpEq]
     have hpLe : yY l ≤ q8+1:=by
      let lP:=l.filter (fun x => !Nat.beq (Nat.land (Nat.land (q0.qD x) (Nat.xor tL q0.qp)) q0.qp) 0)
      have hfeq : yY l=lP.length:=by
       unfold yY;dsimp only;rw [q0.q0A,q0.q4k,List.filter_map,List.length_map];rfl
      have hlPsub : lP.toFinset ⊆ S':=fun x hx=>by
       have hf:=List.mem_filter.mp (List.mem_toFinset.mp hx)
       exact hprivMem x hf.1 (fun hz=>by have hf2:=hf.2;rw [hz] at hf2;exact Bool.noConfusion hf2)
      have hpS : lP.length ≤ S'.card:=by
       rw [← List.toFinset_card_of_nodup (hndL.filter _)];exact Finset.card_le_card hlPsub
      have hScard : S'.card ≤ k'+1:=hR.card
      omega
     refine ⟨Nat.ble_eq.mpr hpLe, ?_⟩
     have hconfIn : ∀ x ∈ l,q0.jO l x → x ∈ l':=by
      intro x hx hconf
      apply Finset.mem_toList.mpr;apply hprivMem x hx;intro hz;apply hconf
      apply Nat.eq_of_testBit_eq;intro q;rw [q0.qM,Nat.zero_testBit]
      cases hp : (q0.k7 l x).testBit q
      · simp
      · obtain ⟨hql,i,_,hi,_,h1,_⟩:=q0.wh _ q hp
        have hbit:=congrArg (fun n : Nat=>n.testBit (12*(q / 12)+i)) hz
        have hlt : 12*(q / 12)+i < 144:=by omega
        rw [q0.qM,q0.jZ,decide_eq_true hlt,Bool.and_true,Nat.zero_testBit] at hbit
        rw [hbit] at h1;exact Bool.noConfusion h1
     have hpLeS : yY l ≤ S'.card:=by
      let lP:=l.filter (fun x => !Nat.beq (Nat.land (Nat.land (q0.qD x) (Nat.xor tL q0.qp)) q0.qp) 0)
      have hlPsub : lP.toFinset ⊆ S':=fun x hx=>by
       have hf:=List.mem_filter.mp (List.mem_toFinset.mp hx)
       exact hprivMem x hf.1 (fun hz=>by have hf2:=hf.2;rw [hz] at hf2;simp at hf2)
      have hfeq : yY l=lP.length:=by
       unfold yY;dsimp only;rw [q0.q0A,q0.q4k,List.filter_map,List.length_map];rfl
      rw [hfeq, ← List.toFinset_card_of_nodup (hndL.filter _)]
      exact Finset.card_le_card hlPsub
     have hScard : S'.card ≤ k'+1:=hR.card
     have hKge : Nat.sub (Nat.succ k') l'.length ≤ Nat.sub (Nat.add q8 1) (yY l):=by
      change (k'+1) - l'.length ≤ (q8+1) - yY l;omega
     have hCL : q0.vV l (Nat.sub (Nat.add q8 1) (yY l)) col:=by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx hconf;exact Nat.le_trans (hVL.1 x (hconfIn x hx hconf)) hKge
      · refine List.Pairwise.imp_of_mem ?_ hndL
        intro x y hx hy hne hcx hcy hceq
        have hdisj:=hVL.2.1 x (hconfIn x hx hcx) y (hconfIn y hy hcy) hne hceq
        apply q0.kO;intro q h1 h2
        have hb:=congrArg (fun n : Nat=>n.testBit q) hdisj
        rw [q0.qM,hprivSub x q h1,hprivSub y q h2,Nat.zero_testBit] at hb
        exact Bool.noConfusion hb
      · intro i U hi1 _ hU q hq
        have hU' : ∀ r,U.testBit r=true →
         ∃ x ∈ l',col x=i ∧ (q0.ya (q0.tw (l'.map q0.qD) 0 0) (q0.qD x)).testBit r=true:=by
         intro r hr;obtain ⟨x,hx,hcx,hceq,hpx⟩:=hU r hr
         exact ⟨x,hconfIn x hx hcx,hceq,hprivSub x r hpx⟩
        obtain ⟨y,hy',hc1,hci,hry⟩:=hVL.2.2.1 i U hi1 hU' q hq
        exact ⟨y,hsub' y hy',hry,fun _=>⟨hc1,hci⟩⟩
     simpa only [List.append_nil] using q0L (maxK:=maxK) hCL
   · rfl
 · dsimp only
   rw [q73]
   have hlen : ws.length=q8+1:=Nat.beq_eq.mp htight
   have hcard:=(wF y1).2
   rw [List.toFinset_card_of_nodup nd] at hcard
   have hk : ws.toFinset.card=k+1:=by
    have:=List.toFinset_card_of_nodup nd;omega
   exact q3V ok nd (q8k y1 hk)
noncomputable def vn (maxK : Nat) (is24 : Bool) (chart : Option qw) (q8 : Nat) (ws : List Word) : Bool :=
 @Bool.rec (fun _=>Bool)
  (@Option.rec qw (fun _=>Bool) true (fun c=>q9V maxK c.val q8 ws) chart)
  true
  is24
theorem q72 {maxK : Nat} {is24 : Bool} {mask goal : Word} {chart : Option qw}
 {ws : List Word} {k q8 : Nat}
 (uC : is24=true → mask=16777215 ∧ goal=4095)
 (w1 : ∀ c,chart=some c → jD goal c)
 (nd : ws.Nodup) (cap : k ≤ q8) (y1 : qf mask goal k 0 ws.toFinset) :
 vn maxK is24 chart q8 ws=true:=by
 unfold vn
 cases h24 : is24
 · dsimp only
   cases hc : chart with
   | none=>rfl
   | some c=>exact q7N (w1 c hc) nd cap y1
 · rfl
noncomputable def jq (maxK : Nat) (is24 : Bool) (mask goal : Word) (chart : Option qw)
  (cut : k6) (state : qc) : Bool :=
 let (q8,nots,ws,_):=state
 let n:=zz ws
 zn (Nat.blt (Nat.add q8 1) (Nat.add n nots))
  (@Bool.rec (fun _=>Bool)
   (zn (Nat.beq q8 0)
    (@Bool.rec (fun _=>Bool)
     (zn (cut state) (kq (vG false ws goal (Nat.xor mask goal))))
     (@Bool.rec (fun _=>Bool)
      (zn (cut state)
       (zn (kq (vn maxK is24 chart q8 ws))
        (kq (vG true ws goal (Nat.xor mask goal)))))
      (zn (kq (vn maxK is24 chart q8 ws))
       (zn (cut state)
        (kq (vG true ws goal (Nat.xor mask goal)))))
      (Nat.beq n (Nat.add q8 1)))
     (Nat.beq nots 0)))
   false
   (qS (Nat.beq nots 0) (qZ goal ws)))
theorem q1s {maxK : Nat} {is24 : Bool} {mask goal : Word} {chart : Option qw}
 {cut : k6} {state : qc}
 (uC : is24=true → mask=16777215 ∧ goal=4095)
 (zM : qm mask goal) (w1 : ∀ c,chart=some c → jD goal c)
 (j6 : zZ mask goal state) (noCut : cut state=false) :
 jq maxK is24 mask goal chart cut state=false:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 obtain ⟨nd,k,cap,y1⟩:=j6
 change k ≤ q8 at cap
 have card:=(wF y1).2
 rw [List.toFinset_card_of_nodup nd] at card
 change ws.length+nots ≤ k+1 at card
 unfold jq
 simp only [yd,zQ,qR,uP,za,q31]
 have hfit : Nat.blt (Nat.add q8 1) (Nat.add ws.length nots)=false:=by
  cases h : Nat.blt (Nat.add q8 1) (Nat.add ws.length nots)
  · rfl
  · have hlt : q8+1 < ws.length+nots:=Nat.blt_eq.mp h;omega
 rw [hfit,Bool.false_or]
 cases hhit : (Nat.beq nots 0&&ws.contains goal)
 · dsimp only
   have hfp : Nat.beq q8 0=false:=by
    cases hz : Nat.beq q8 0
    · rfl
    · exfalso
      have hfz : q8=0:=Nat.beq_eq.mp hz
      have kz : k=0:=by omega
      subst k
      obtain ⟨ht0,eq,_⟩:=y1
      change nots=0 at ht0
      have hm : goal ∈ ws:=List.mem_toFinset.mp (by rw [eq];simp)
      have : (Nat.beq nots 0&&ws.contains goal)=true:=by
       rw [ht0,Nat.beq_refl,List.contains_iff_mem.mpr hm];rfl
      rw [this] at hhit;exact Bool.noConfusion hhit
   rw [hfp,Bool.false_or]
   cases hn0 : Nat.beq nots 0
   · dsimp only
     have hpart : zF false ws goal (Nat.xor mask goal)=true :=
      uZ (qJ:=false) zM y1 (fun h=>Bool.noConfusion h)
     rw [noCut,hpart];rfl
   · dsimp only
     have ht0 : nots=0:=Nat.beq_eq.mp hn0
     subst ht0
     have hpart : zF true ws goal (Nat.xor mask goal)=true :=
      uZ (qJ:=true) zM y1 (fun _=>rfl)
     have hkw:=q72 (maxK:=maxK) uC w1 nd cap y1
     cases Nat.beq ws.length (Nat.add q8 1) <;> dsimp only <;> rw [noCut,hpart,hkw] <;> rfl
 · rfl
abbrev yq:=Nat → Option jo
abbrev z2:=Nat → (yq → Bool) → Bool
def z1 (zR : z2) : Prop :=
 ∀ p k,zR p k=true → ∃ f : yq,k f=true
def q1v (entries : List (Nat × Nat × Nat)) (q5 : Nat) : Option jo :=
 List.rec none (fun e _ next =>
  @Bool.rec (fun _=>Option jo)
   (@Bool.rec (fun _=>Option jo) next none (Nat.blt q5 e.1))
   (some (e.2.1,e.2.2))
   (Nat.beq q5 e.1)) entries
def kE (data qV yj yI yH destMask autoShift : Nat)
  (size w7 : Nat) (k : List (Nat × Nat × Nat) → Bool) : Bool :=
 (Nat.rec (motive:=fun _=>Nat → (List (Nat × Nat × Nat) → Bool) → Bool)
  (fun _ f=>f [])
  (fun _ next idx f =>
   q7 (Nat.land (Nat.shiftRight data (Nat.mul qV idx)) yj) fun code =>
    q7 (Nat.land code yH) fun tok =>
     q7 (Nat.land (Nat.shiftRight code yI) destMask) fun dest =>
      q7 (Nat.shiftRight code autoShift) fun auto =>
       next (Nat.add idx 1) (fun rest=>f ((tok,dest,auto) :: rest)))
  size) w7 k
theorem q1O (data qV yj yI yH destMask autoShift size w7 : Nat)
  (k : List (Nat × Nat × Nat) → Bool)
  (h : kE data qV yj yI yH destMask autoShift size w7 k=true) :
  ∃ entries,k entries=true:=by
 induction size generalizing w7 k with
 | zero=>exact ⟨[],h⟩
 | succ s ih =>
  have h1 : kE data qV yj yI yH destMask autoShift s (Nat.add w7 1)
    (fun rest=>k ((Nat.land (Nat.land (Nat.shiftRight data (Nat.mul qV w7)) yj) yH,
     Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight data (Nat.mul qV w7)) yj) yI) destMask,
     Nat.shiftRight (Nat.land (Nat.shiftRight data (Nat.mul qV w7)) yj) autoShift) :: rest))=true:=by
   unfold kE at h ⊢
   dsimp only at h
   simp only [ql] at h ⊢
   exact h
  obtain ⟨rest,hr⟩:=ih _ _ h1
  exact ⟨_ :: rest,hr⟩
def q7b (data qV yj yI yH destMask autoShift trials lo hi q5 : Nat) :
  Option jo :=
 (Nat.rec (motive:=fun _=>Nat → Nat → Option jo) (fun _ _=>none)
  (fun _ next l h =>
   @Bool.rec (fun _=>Option jo) none
    (q7 (Nat.div (Nat.add l h) 2) fun mid =>
     q7 (Nat.land (Nat.shiftRight data (Nat.mul qV mid)) yj) fun code =>
      q7 (Nat.land code yH) fun key =>
       @Bool.rec (fun _=>Option jo)
        (@Bool.rec (fun _=>Option jo)
         (q7 (Nat.add mid 1) fun mid1=>next mid1 h)
         (next l mid)
         (Nat.blt q5 key))
        (some (Nat.land (Nat.shiftRight code yI) destMask,Nat.shiftRight code autoShift))
        (Nat.beq q5 key))
    (Nat.blt l h))
  trials) lo hi
def qv (index data indexWidth indexMask sizeBits sizeMask qV yj
  yI yH destMask autoShift trials : Nat) (qz : Nat) (k : yq → Bool) : Bool :=
 q7 (Nat.land (Nat.shiftRight index (Nat.mul indexWidth qz)) indexMask) fun kt =>
  q7 (Nat.land kt sizeMask) fun size =>
   @Bool.rec (fun _=>Bool)
    (q7 (Nat.shiftRight kt sizeBits) fun off =>
     @Bool.rec (fun _=>Bool)
      (q7 (Nat.add off size) fun hi =>
       k (q7b data qV yj yI yH destMask autoShift trials off hi))
      (kE data qV yj yI yH destMask autoShift size off fun entries =>
       k (q1v entries))
      (Nat.ble size 8))
    (k (fun _=>none))
    (Nat.beq size 0)
theorem qt (index data indexWidth indexMask sizeBits sizeMask qV yj
 yI yH destMask autoShift trials : Nat) :
 z1 (qv index data indexWidth indexMask sizeBits sizeMask qV yj
  yI yH destMask autoShift trials):=by
 intro qz k h
 unfold qv at h
 simp only [ql] at h
 cases h0 : Nat.beq (Nat.land (Nat.land (Nat.shiftRight index (Nat.mul indexWidth qz)) indexMask) sizeMask) 0
 · rw [h0] at h;dsimp only at h
   cases hle : Nat.ble (Nat.land (Nat.land (Nat.shiftRight index (Nat.mul indexWidth qz)) indexMask) sizeMask) 8
   · rw [hle] at h;dsimp only at h;exact ⟨_,h⟩
   · rw [hle] at h;dsimp only at h
     obtain ⟨entries,he⟩:=q1O _ _ _ _ _ _ _ _ _ _ h
     exact ⟨q1v entries,he⟩
 · rw [h0] at h;exact ⟨fun _=>none,h⟩
abbrev zt:=Nat → Option z0
def qP (mask goal : Word) (qV : Nat) (z8 : zt) : Prop :=
 ∀ (a : Nat) (m : z0),z8 a=some m →
  ∃ zi : Fin qV → Fin qV,q7i mask goal zi ∧
   ∀ w,qm mask w → yG m w=z9 zi w
noncomputable def kP (qQ : Nat) (q3 : zj)
  (qx : Nat → Option qy) (z8 : zt)
  (qz : Nat) (bucket : yq) (q5 : Nat) (state : qc) : Bool :=
 @Option.rec jo (fun _=>Bool) false
  (fun lnk =>
   qS (Nat.blt lnk.1 qQ)
    (zn
     (qS (Nat.beq lnk.2 0)
      (let pt:=q3 lnk.1
       qS (Nat.beq pt.1 qz) (Nat.beq pt.2 q5)))
     (@Option.rec qy (fun _=>Bool) false
      (fun saved =>
        qS (Nat.beq saved.1 state.1)
         (qS (Nat.beq saved.2.1 state.2.1)
          (@Bool.rec (fun _=>Bool)
           (@Option.rec z0 (fun _=>Bool) false
            (fun m=>uW saved.2.2 (vz m state.2.2.1))
            (z8 lnk.2))
           (uW saved.2.2 state.2.2.1)
           (Nat.beq lnk.2 0))))
      (qx lnk.1))))
  (bucket q5)
noncomputable def u6 :
  {f : Nat → zj → (Nat → Option qy) → zt → Nat → yq → Nat → qc → Bool // f=kP}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta kP uW qS zn
  beta_reduce
  exact rfl
noncomputable def jR:=u6.1
theorem q0K {mask goal : Word} {qV q8 q9 qQ qz q5 : Nat}
 {stock : List Word} {q3 : zj} {z8 : zt} {bucket : yq}
 {state : qc}
 (hTree : ∀ dest,q3 dest=(qz,q5) →
  jr mask stock q8 q9 q3 dest=some state)
 (bounds : qm (qI qV) mask)
 (valid : qP mask goal qV z8)
 (zM : ∀ w ∈ state.2.2.1,qm mask w)
 (ok : jR qQ q3 (qr mask stock q8 q9 q3) z8 qz bucket q5 state=true)
 {k : Nat} (y1 : qf mask goal k state.2.1 state.2.2.1.toFinset) :
 ∃ i saved,i < qQ ∧ jr mask stock q8 q9 q3 i=some saved ∧
  saved.1=state.1 ∧ saved.2.1=state.2.1 ∧
  qf mask goal k saved.2.1 saved.2.2.1.toFinset:=by
 rw [show jR=kP from u6.2] at ok
 unfold kP at ok
 cases hb : bucket q5 with
 | none=>rw [hb] at ok;exact Bool.noConfusion ok
 | some lnk =>
  obtain ⟨dest,auto⟩:=lnk
  rw [hb] at ok;dsimp only at ok
  rw [qR,zQ,Bool.and_eq_true,Nat.blt_eq,Bool.or_eq_true] at ok
  obtain ⟨hdest,htree | hslow⟩:=ok
  · rw [qR,qR,Bool.and_eq_true,Bool.and_eq_true,Nat.beq_eq,Nat.beq_eq,Nat.beq_eq] at htree
    obtain ⟨_,hp,ht⟩:=htree
    have hfor : q3 dest=(qz,q5):=Prod.ext hp ht
    exact ⟨dest,state,hdest,hTree dest hfor,rfl,rfl,y1⟩
  · rw [q2t] at hslow
    cases hs : jr mask stock q8 q9 q3 dest with
    | none=>rw [hs] at hslow;exact Bool.noConfusion hslow
    | some saved =>
     rw [hs] at hslow;dsimp only [Option.map] at hslow
     rw [qR,qR,Bool.and_eq_true,Bool.and_eq_true,Nat.beq_eq,Nat.beq_eq] at hslow
     obtain ⟨hf,hn,hws⟩:=hslow
     refine ⟨dest,saved,hdest,hs,hf,hn, ?_⟩
     rw [hn]
     cases ha : Nat.beq auto 0
     · rw [ha] at hws;dsimp only at hws
       cases hm : z8 auto with
       | none=>rw [hm] at hws;exact Bool.noConfusion hws
       | some m =>
        rw [hm] at hws;dsimp only at hws
        rw [q4X,q19] at hws
        have same : saved.2.2.1=jc m state.2.2.1:=beq_iff_eq.mp hws
        obtain ⟨zi,autoOk,agree⟩:=valid auto m hm
        rw [same,q8s (fun w hw=>agree w (zM w hw))]
        exact q3D autoOk bounds y1 (fun w hw=>zM _ (List.mem_toFinset.mp hw))
     · rw [ha] at hws;dsimp only at hws
       rw [q4X] at hws
       have same : saved.2.2.1=state.2.2.1:=beq_iff_eq.mp hws
       rwa [same]
def q6 (qJ : Bool) (qp : Word) (tag : qU) : Word :=
 @Bool.rec (fun _=>Word) (Nat.xor tag.1 tag.2) (Nat.land tag.1 (Nat.xor tag.2 qp)) qJ
def vS (qJ : Bool) (qp : Word) (tags : List qU)
  (use : wS → Bool) : Bool :=
 (List.rec (motive:=fun _=>(wS → Bool) → Bool) (fun k=>k (0,0,0))
  (fun tag _ more k =>
   q7 (q6 qJ qp tag) fun column =>
    more fun acc =>
     q7 (Nat.lor acc.1 column) fun once =>
      q7 (Nat.lor acc.2.1 (Nat.land acc.1 column)) fun twice =>
       q7 (Nat.lor acc.2.2 (Nat.land acc.2.1 column)) fun thrice=>k (once,twice,thrice))
  tags) use
theorem q4Z (qJ : Bool) (qp : Word) (tags : List qU) (use : wS → Bool) :
  vS qJ qp tags use =
   use (tags.foldr (fun tag acc =>
    let c:=q6 qJ qp tag
    (Nat.lor acc.1 c,Nat.lor acc.2.1 (Nat.land acc.1 c),Nat.lor acc.2.2 (Nat.land acc.2.1 c))) (0,0,0)):=by
 induction tags generalizing use with
 | nil=>rfl
 | cons tag tags ih =>
  change q7 (q6 qJ qp tag) (fun column =>
   vS qJ qp tags (fun acc =>
    q7 (Nat.lor acc.1 column) (fun once =>
     q7 (Nat.lor acc.2.1 (Nat.land acc.1 column)) (fun twice =>
      q7 (Nat.lor acc.2.2 (Nat.land acc.2.1 column)) (fun thrice=>use (once,twice,thrice))))))=_
  simp only [ql,ih];rfl
def j3 (mask goal : Word) (sample : qH) : Prop :=
 ∀ idx < sample.2,
  let code:=z3 sample.1 18 idx
  let p:=Nat.land code 511
  let n:=Nat.shiftRight code 9
  goal.testBit p=true ∧ mask.testBit n=true ∧ goal.testBit n=false
def wd (mask goal : Word) (sample : qH) : Bool :=
 qE 0 sample.2 fun idx =>
  let code:=y9 sample.1 18 idx
  let p:=Nat.land code 511
  let n:=Nat.shiftRight code 9
  zD goal p&&zD mask n && !zD goal n
theorem q1z {mask goal : Word} {sample : qH}
  (ok : wd mask goal sample=true) :
  j3 mask goal sample:=by
 intro idx hidx
 have h:=zN ok (Nat.zero_le idx) (by simpa using hidx)
 simp only [q4V,vO,Bool.and_eq_true,Bool.not_eq_true'] at h
 exact ⟨h.1.1,h.1.2,h.2⟩
def zr (sample : qH) (w : Word) (sig : qU) : Prop :=
 (∀ k ≥ sample.2,sig.1.testBit k=false ∧ sig.2.testBit k=false) ∧
 (∀ q < sample.2,
  let code:=z3 sample.1 18 q
  sig.1.testBit q=w.testBit (Nat.land code 511) ∧
  sig.2.testBit q=w.testBit (Nat.shiftRight code 9))
def vK (sample : qH) (stock : List Word) (root : List qb) : Prop :=
 root.map (·.1)=stock ∧ ∀ t ∈ root,zr sample t.1 t.2
def kG (sample : qH) (stock : List Word) (root : List qb) : Bool :=
 (root.map (·.1)==stock) &&
 root.all fun t =>
  Nat.blt t.2.1 (Nat.shiftLeft 1 sample.2) &&
  Nat.blt t.2.2 (Nat.shiftLeft 1 sample.2) &&
  qE 0 sample.2 fun q =>
   let code:=y9 sample.1 18 q
   (zD t.2.1 q==zD t.1 (Nat.land code 511)) &&
   (zD t.2.2 q==zD t.1 (Nat.shiftRight code 9))
theorem kM {x s k : Nat} (hx : x < 2 ^ s) (hk : k ≥ s) : x.testBit k=false:=by
 have hlt : x < 2 ^ k:=Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hk)
 exact Nat.testBit_lt_two_pow hlt
theorem q0q {sample : qH} {stock : List Word} {root : List qb}
  (ok : kG sample stock root=true) :
  vK sample stock root:=by
 unfold kG at ok
 rw [Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at ok
 refine ⟨ok.1,fun t ht => ?_⟩
 have h:=ok.2 t ht
 simp only [Bool.and_eq_true,Nat.blt_eq] at h
 have hpow : Nat.shiftLeft 1 sample.2=2 ^ sample.2:=by
  change 1<<<sample.2=2 ^ sample.2;rw [Nat.shiftLeft_eq,Nat.one_mul]
 refine ⟨fun k hk=>⟨kM (hpow ▸ h.1.1) hk,kM (hpow ▸ h.1.2) hk⟩, ?_⟩
 intro q hq
 have hq':=zN h.2 (Nat.zero_le q) (by simpa using hq)
 simp only [q4V,vO,Bool.and_eq_true,beq_iff_eq] at hq'
 exact hq'
theorem q5H {sample : qH} {root : List qb} {q5 : Nat}
 (hroot : ∀ t ∈ root,zr sample t.1 t.2) :
 (kn root q5).map (·.1)=yp (root.map (·.1)) q5 ∧
 ∀ t ∈ kn root q5,zr sample t.1 t.2:=by
 induction root generalizing q5 with
 | nil=>exact ⟨rfl,fun _ h=>False.elim (List.not_mem_nil h)⟩
 | cons tag rest ih =>
  have hrest : ∀ t ∈ rest,zr sample t.1 t.2:=fun t ht=>hroot t (List.mem_cons_of_mem _ ht)
  obtain ⟨hm,hv⟩:=ih hrest (q5:=Nat.shiftRight q5 1)
  have h1 : kn (tag :: rest) q5 =
   @Bool.rec (fun _=>List qb) (tag :: kn rest (Nat.shiftRight q5 1))
    (kn rest (Nat.shiftRight q5 1)) (Nat.beq (Nat.land q5 1) 0):=by
   unfold kn;simp only [ql]
  have h2 : yp ((tag :: rest).map (·.1)) q5 =
   @Bool.rec (fun _=>List Word) (tag.1 :: yp (rest.map (·.1)) (Nat.shiftRight q5 1))
    (yp (rest.map (·.1)) (Nat.shiftRight q5 1)) (Nat.beq (Nat.land q5 1) 0):=by
   unfold yp;simp only [List.map_cons,ql]
  rw [h1,h2]
  cases Nat.beq (Nat.land q5 1) 0
  · refine ⟨by rw [List.map_cons,hm],fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact hroot t List.mem_cons_self
    · exact hv t ht'
  · exact ⟨hm,hv⟩
theorem q1p {kp : Bool} {w : Word} {bank : List qb} :
 (ko kp w bank).map (·.1)=zw kp w (bank.map (·.1)) ∧
 ∀ t ∈ ko kp w bank,t ∈ bank:=by
 cases kp with
 | true=>exact ⟨rfl,fun _ h=>h⟩
 | false =>
  induction bank with
  | nil=>exact ⟨rfl,fun _ h=>h⟩
  | cons tag rest ih =>
   have h1 : ko false w (tag :: rest) =
    @Bool.rec (fun _=>List qb) (tag :: ko false w rest) rest (Nat.beq tag.1 w):=rfl
   have h2 : zw false w ((tag :: rest).map (·.1)) =
    @Bool.rec (fun _=>List Word) (tag.1 :: zw false w (rest.map (·.1))) (rest.map (·.1)) (Nat.beq tag.1 w):=rfl
   rw [h1,h2]
   cases Nat.beq tag.1 w
   · refine ⟨by simp [ih.1],fun t ht => ?_⟩
     rcases List.mem_cons.mp ht with rfl | ht'
     · exact List.mem_cons_self
     · exact List.mem_cons_of_mem _ (ih.2 t ht')
   · exact ⟨rfl,fun t ht=>List.mem_cons_of_mem _ ht⟩
theorem q3O {tag : qb} {bank : List qb} :
 (vw tag bank).map (·.1)=yh tag.1 (bank.map (·.1)) ∧
 ∀ t ∈ vw tag bank,t=tag ∨ t ∈ bank:=by
 induction bank with
 | nil=>exact ⟨by unfold yh;rw [ql];rfl,fun t ht=>Or.inl (List.mem_singleton.mp ht)⟩
 | cons old rest ih =>
  have h1 : vw tag (old :: rest) =
   @Bool.rec (fun _=>List qb) (old :: vw tag rest) (tag :: old :: rest) (Nat.ble tag.1 old.1):=rfl
  have h2 : yh tag.1 ((old :: rest).map (·.1)) =
   @Bool.rec (fun _=>List Word) (old.1 :: yh tag.1 (rest.map (·.1))) (tag.1 :: old.1 :: rest.map (·.1)) (Nat.ble tag.1 old.1):=by
   unfold yh;rw [ql,ql];rfl
  rw [h1,h2]
  cases Nat.ble tag.1 old.1
  · refine ⟨by simp [ih.1],fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact Or.inr List.mem_cons_self
    · rcases ih.2 t ht' with rfl | hm
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ hm)
  · refine ⟨rfl,fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact Or.inl rfl
    · exact Or.inr ht'
theorem vy {bank : List qb} {i : Nat} (hi : i < bank.length) :
 (zp bank i).1=(bank.map (·.1)).getD i 0 ∧ zp bank i ∈ bank:=by
 induction bank generalizing i with
 | nil=>simp at hi
 | cons tag rest ih =>
  cases i with
  | zero=>exact ⟨rfl,List.mem_cons_self⟩
  | succ j =>
   obtain ⟨h1,h2⟩:=ih (Nat.lt_of_succ_lt_succ hi)
   exact ⟨h1,List.mem_cons_of_mem _ h2⟩
theorem jW {mask goal : Word} {sample : qH} {op : Nat} {x y : qb}
 (jA : j3 mask goal sample) (hgm : qm mask goal)
 (hx : zr sample x.1 x.2) (hy : zr sample y.1 y.2) :
 let qp:=Nat.sub (Nat.shiftLeft 1 sample.2) 1
 zr sample (zA mask op x.1 y.1)
  (zA qp op x.2.1 y.2.1,zA qp op x.2.2 y.2.2):=by
 dsimp only
 have hfull : Nat.sub (Nat.shiftLeft 1 sample.2) 1=2 ^ sample.2 - 1:=by
  change (1<<<sample.2) - 1=2 ^ sample.2 - 1;rw [Nat.shiftLeft_eq,Nat.one_mul]
 have hfullBit : ∀ j,(Nat.sub (Nat.shiftLeft 1 sample.2) 1).testBit j=decide (j < sample.2):=by
  intro j;rw [hfull,Nat.testBit_two_pow_sub_one]
 unfold zA
 cases h0 : Nat.beq op 0
 · cases h1 : Nat.beq op 1
   · refine ⟨fun k hk => ?_,fun q hq => ?_⟩
     · have hfk : (Nat.sub (Nat.shiftLeft 1 sample.2) 1).testBit k=false:=by
        rw [hfullBit];simp [Nat.not_lt.mpr hk]
       exact ⟨by rw [q0.j7,hfk,(hx.1 k hk).1];rfl,
        by rw [q0.j7,hfk,(hx.1 k hk).2];rfl⟩
     · have hfq : (Nat.sub (Nat.shiftLeft 1 sample.2) 1).testBit q=true:=by
        rw [hfullBit];simp [hq]
       obtain ⟨hp,mn,_⟩:=jA q hq
       have mp : mask.testBit (Nat.land (z3 sample.1 18 q) 511)=true:=kU hgm hp
       exact ⟨by rw [q0.j7,q0.j7,hfq,mp,(hx.2 q hq).1],
        by rw [q0.j7,q0.j7,hfq,mn,(hx.2 q hq).2]⟩
   · refine ⟨fun k hk=>⟨by rw [q0.qX,(hx.1 k hk).1,(hy.1 k hk).1];rfl,
      by rw [q0.qX,(hx.1 k hk).2,(hy.1 k hk).2];rfl⟩,
      fun q hq=>⟨by rw [q0.qX,q0.qX,(hx.2 q hq).1,(hy.2 q hq).1],
       by rw [q0.qX,q0.qX,(hx.2 q hq).2,(hy.2 q hq).2]⟩⟩
 · refine ⟨fun k hk=>⟨by rw [q0.qM,(hx.1 k hk).1,(hy.1 k hk).1];rfl,
    by rw [q0.qM,(hx.1 k hk).2,(hy.1 k hk).2];rfl⟩,
    fun q hq=>⟨by rw [q0.qM,q0.qM,(hx.2 q hq).1,(hy.2 q hq).1],
     by rw [q0.qM,q0.qM,(hx.2 q hq).2,(hy.2 q hq).2]⟩⟩
theorem q5G {mask goal : Word} {sample : qH} {q5 : Nat}
 {st child : qc} {bank : List qb}
 (jA : j3 mask goal sample) (hgm : qm mask goal)
 (heval : qL mask q5 st=some child)
 (hmap : bank.map (·.1)=st.2.2.1)
 (hval : ∀ t ∈ bank,zr sample t.1 t.2) :
 let qp:=Nat.sub (Nat.shiftLeft 1 sample.2) 1
 (wi mask qp q5 bank).map (·.1)=child.2.2.1 ∧
 ∀ t ∈ wi mask qp q5 bank,zr sample t.1 t.2:=by
 obtain ⟨q8,nots,ws,history⟩:=st
 change bank.map (·.1)=ws at hmap
 have hlen : bank.length=ws.length:=by rw [← hmap,List.length_map]
 let keep:=q5 % 4
 let op:=q5 / 4 % 3
 let a:=q5 / (4*3*64)
 let b:=q5 / (4*3) % 64
 let xw:=ws.getD a 0
 let yw:=ws.getD b 0
 let out:=if op==0 then xw&&&yw else if op==1 then xw|||yw else mask^^^xw
 let bad : Bool:=q8==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
 let stale : Bool:=out==0||out==mask||ws.contains out
 change (if bad then none else if stale then none else
  some (q8 - 1,if op==2 then nots - 1 else nots,
   qB out (if op==2||keep.testBit 1 then (if keep.testBit 0 then ws else ws.erase xw) else (if keep.testBit 0 then ws else ws.erase xw).erase yw),
   (out,xw,yw) :: history))=some child at heval
 by_cases hb : bad=true;simp [hb] at heval
 by_cases hs : stale=true;simp [hb,hs] at heval
 have heq : (q8 - 1,if op==2 then nots - 1 else nots,
  qB out (if op==2||keep.testBit 1 then (if keep.testBit 0 then ws else ws.erase xw) else (if keep.testBit 0 then ws else ws.erase xw).erase yw),
  (out,xw,yw) :: history)=child:=by simpa [hb,hs] using heval
 have hblt : b < ws.length:=by
  by_contra hge
  exact hb (by simp [bad,show b ≥ ws.length by omega])
 have halt : a < ws.length:=by
  by_cases hop2 : (op==2)=true
  · by_cases hab : a=b
    · omega
    · exfalso;exact hb (by simp [bad,hop2,hab])
  · by_contra hge
    exact hb (by simp [bad,hop2,show a ≥ b by omega])
 have haBank : Nat.div q5 768 < bank.length:=by rw [hlen];exact halt
 have hbBank : Nat.mod (Nat.div q5 12) 64 < bank.length:=by rw [hlen];exact hblt
 obtain ⟨hx1,hxMem⟩:=vy haBank
 obtain ⟨hy1,hyMem⟩:=vy hbBank
 rw [hmap] at hx1 hy1
 unfold wi
 simp only [ql]
 obtain ⟨hinsMap,hinsMem⟩:=q3O
  (tag:=(zA mask (Nat.mod (Nat.div q5 4) 3) (zp bank (Nat.div q5 768)).1 (zp bank (Nat.mod (Nat.div q5 12) 64)).1,
   zA (Nat.sub (Nat.shiftLeft 1 sample.2) 1) (Nat.mod (Nat.div q5 4) 3) (zp bank (Nat.div q5 768)).2.1 (zp bank (Nat.mod (Nat.div q5 12) 64)).2.1,
   zA (Nat.sub (Nat.shiftLeft 1 sample.2) 1) (Nat.mod (Nat.div q5 4) 3) (zp bank (Nat.div q5 768)).2.2 (zp bank (Nat.mod (Nat.div q5 12) 64)).2.2))
  (bank:=ko (zn (Nat.beq (Nat.mod (Nat.div q5 4) 3) 2) (zD (Nat.mod q5 4) 1)) (zp bank (Nat.mod (Nat.div q5 12) 64)).1
   (ko (zD (Nat.mod q5 4) 0) (zp bank (Nat.div q5 768)).1 bank))
 obtain ⟨hk2Map,hk2Mem⟩:=q1p (kp:=zn (Nat.beq (Nat.mod (Nat.div q5 4) 3) 2) (zD (Nat.mod q5 4) 1))
  (w:=(zp bank (Nat.mod (Nat.div q5 12) 64)).1)
  (bank:=ko (zD (Nat.mod q5 4) 0) (zp bank (Nat.div q5 768)).1 bank)
 obtain ⟨hk1Map,hk1Mem⟩:=q1p (kp:=zD (Nat.mod q5 4) 0)
  (w:=(zp bank (Nat.div q5 768)).1) (bank:=bank)
 refine ⟨?_,fun t ht => ?_⟩
 · rw [hinsMap,hk2Map,hk1Map,hmap,hx1,hy1,uL,ja,ja,
    q2s,zQ,vO,vO, ← heq]
   rfl
 · rcases hinsMem t ht with rfl | hm2
   · exact jW jA hgm (hval _ hxMem) (hval _ hyMem)
   · exact hval t (hk1Mem t (hk2Mem t hm2))
theorem q18 {mask goal : Word} {stock : List Word} {q8 q9 i : Nat}
 {q3 : zj} {sample : qH} {root : List qb} {st : qc}
 (jA : j3 mask goal sample) (hgm : qm mask goal)
 (hroot : vK sample stock root)
 (htr : jr mask stock q8 q9 q3 i=some st) :
 let tags:=qG mask sample.2 root q8 q3 i
 tags.length=st.2.2.1.length ∧
 ∀ j < st.2.2.1.length,zr sample (st.2.2.1.getD j 0) (qn tags j):=by
 let qp:=Nat.sub (Nat.shiftLeft 1 sample.2) 1
 let go:=fun n=>Nat.rec (motive:=fun _=>Nat → List qb) (fun _=>[])
  (fun _ previous j =>
   let pt:=q3 j
   q7 pt.1 fun qz =>
    q7 pt.2 fun q5 =>
     @Bool.rec (fun _=>List qb)
      (q7 (Nat.sub qz 1) fun p1=>k0.1 mask qp q5 (previous p1))
      (kn root q5)
      (Nat.beq qz 0)) n
 have hgo : ∀ n j st,zb mask stock q8 q9 q3 n j=some st →
  (go n j).map (·.1)=st.2.2.1 ∧ ∀ t ∈ go n j,zr sample t.1 t.2:=by
  intro n
  induction n with
  | zero=>intro _ _ h;simp [zb] at h
  | succ n ih =>
   intro j st h
   change (if (q3 j).1==0 then
    if (q3 j).2 < 2 ^ stock.length then some (zO stock q8 q9 (q3 j).2) else none
    else (zb mask stock q8 q9 q3 n ((q3 j).1 - 1)).bind (qL mask (q3 j).2))=some st at h
   have hstep : go (n+1) j =
    @Bool.rec (fun _=>List qb)
     (k0.1 mask qp (q3 j).2 (go n (Nat.sub (q3 j).1 1)))
     (kn root (q3 j).2) (Nat.beq (q3 j).1 0):=by
    change q7 (q3 j).1 (fun qz=>q7 (q3 j).2 fun q5 =>
     @Bool.rec (fun _=>List qb)
      (q7 (Nat.sub qz 1) fun p1=>k0.1 mask qp q5 (go n p1))
      (kn root q5) (Nat.beq qz 0))=_
    simp only [ql]
   rw [hstep]
   cases hp : Nat.beq (q3 j).1 0
   · dsimp only
     have hne : ((q3 j).1==0)=false:=hp
     simp only [hne,Bool.false_eq_true, ↓reduceIte] at h
     cases hprev : zb mask stock q8 q9 q3 n ((q3 j).1 - 1) with
     | none=>rw [hprev] at h;simp at h
     | some pst =>
      rw [hprev] at h
      obtain ⟨hm,hv⟩:=ih ((q3 j).1 - 1) pst hprev
      rw [show k0.1=wi from k0.2]
      exact q5G jA hgm h hm hv
   · dsimp only
     have heq : ((q3 j).1==0)=true:=hp
     simp only [heq, ↓reduceIte] at h
     by_cases ht : (q3 j).2 < 2 ^ stock.length
     · simp only [ht, ↓reduceIte,Option.some.injEq] at h
       subst st
       obtain ⟨hm,hv⟩:=q5H hroot.2 (q5:=(q3 j).2)
       rw [hroot.1,wa] at hm
       exact ⟨hm,hv⟩
     · simp [ht] at h
 obtain ⟨hm,hv⟩:=hgo (q8+1) i st htr
 have hmap : ∀ l : List qb,List.rec (motive:=fun _=>List qU) [] (fun tag _ rest=>tag.2 :: rest) l=l.map (·.2):=by
  intro l;induction l with | nil=>rfl | cons a b ih=>exact congrArg (a.2 :: ·) ih
 have htagsEq : qG mask sample.2 root q8 q3 i=(go (q8+1) i).map (·.2):=hmap _
 dsimp only
 rw [htagsEq]
 refine ⟨by rw [List.length_map, ← hm,List.length_map],fun j hj => ?_⟩
 have hjBank : j < (go (q8+1) i).length:=by rw [← hm,List.length_map] at hj;exact hj
 obtain ⟨h1,hmem⟩:=vy hjBank
 have h2 : ∀ (l : List qb) (idx : Nat),idx < l.length → qn (l.map (·.2)) idx=(zp l idx).2:=by
  intro l
  induction l with
  | nil=>intro _ h;simp at h
  | cons a bs ih =>
   intro idx hidx
   cases idx with
   | zero=>rfl
   | succ k=>exact ih k (by simpa using hidx)
 rw [h2 _ _ hjBank, ← hm, ← h1]
 exact hv _ hmem
theorem y2 {dir : Bool} {s k : Nat} {tag : qU}
 (hk : k ≥ s) (ht : tag.1.testBit k=false ∧ tag.2.testBit k=false) :
 (q6 dir (Nat.sub (Nat.shiftLeft 1 s) 1) tag).testBit k=false:=by
 unfold q6
 cases dir
 · rw [q0.j7,ht.1,ht.2];rfl
 · rw [q0.qM,ht.1];rfl
theorem k8 {dir : Bool} {s q : Nat} {tag : qU} (hq : q < s) :
 (q6 dir (Nat.sub (Nat.shiftLeft 1 s) 1) tag).testBit q =
  if dir then (tag.1.testBit q && !tag.2.testBit q) else Bool.xor (tag.1.testBit q) (tag.2.testBit q):=by
 have hfull : (Nat.sub (Nat.shiftLeft 1 s) 1).testBit q=true:=by
  change ((1<<<s) - 1).testBit q=true
  rw [Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow_sub_one];simp [hq]
 unfold q6
 cases dir
 · rw [q0.j7];rfl
 · rw [q0.qM,q0.j7,hfull];cases tag.2.testBit q <;> rfl
theorem k4 {dir : Bool} {s : Nat} {tags : List qU}
 (hhi : ∀ t ∈ tags, ∀ k ≥ s,t.1.testBit k=false ∧ t.2.testBit k=false) :
 let qp:=Nat.sub (Nat.shiftLeft 1 s) 1
 let cs:=tags.foldr (fun tag acc =>
  let c:=q6 dir qp tag
  (Nat.lor acc.1 c,Nat.lor acc.2.1 (Nat.land acc.1 c),Nat.lor acc.2.2 (Nat.land acc.2.1 c))) (0,0,0)
 (∀ k ≥ s,cs.1.testBit k=false ∧ cs.2.1.testBit k=false ∧ cs.2.2.testBit k=false) ∧
 (∀ q < s,
  let cnt:=tags.countP (fun t=>(q6 dir qp t).testBit q)
  cs.1.testBit q=decide (1 ≤ cnt) ∧ cs.2.1.testBit q=decide (2 ≤ cnt) ∧ cs.2.2.testBit q=decide (3 ≤ cnt)):=by
 induction tags with
 | nil =>
  refine ⟨fun _ _=>⟨Nat.zero_testBit _,Nat.zero_testBit _,Nat.zero_testBit _⟩,
   fun _ _=>⟨by simp,by simp,by simp⟩⟩
 | cons tag rest ih =>
  obtain ⟨ihHi,ihBit⟩:=ih (fun t ht=>hhi t (List.mem_cons_of_mem _ ht))
  refine ⟨fun k hk => ?_,fun q hq => ?_⟩
  · have hc:=y2 (dir:=dir) hk (hhi tag List.mem_cons_self k hk)
    obtain ⟨h1,h2,h3⟩:=ihHi k hk
    dsimp only [List.foldr]
    exact ⟨by rw [q0.qX,h1,hc];rfl,
     by rw [q0.qX,q0.qM,h2,h1,hc];rfl,
     by rw [q0.qX,q0.qM,h3,h2,hc];rfl⟩
  · obtain ⟨h1,h2,h3⟩:=ihBit q hq
    dsimp only [List.foldr]
    rw [List.countP_cons,q0.qX,q0.qX,q0.qM,q0.qX,q0.qM,h1,h2,h3]
    cases hbit : (q6 dir (Nat.sub (Nat.shiftLeft 1 s) 1) tag).testBit q
    · simp only [Bool.or_false,Bool.and_false,Bool.false_eq_true, ↓reduceIte,Nat.add_zero,and_self]
    · simp only [Bool.or_true,Bool.and_true, ↓reduceIte]
      generalize rest.countP (fun t=>(q6 dir (Nat.sub (Nat.shiftLeft 1 s) 1) t).testBit q)=cnt
      refine ⟨(decide_eq_true (Nat.succ_pos cnt)).symm, ?_, ?_⟩
      · cases cnt with
        | zero=>rfl
        | succ m=>simp [Nat.succ_le_succ_iff]
      · cases cnt with
        | zero=>rfl
        | succ m =>
         cases m with
         | zero=>rfl
         | succ k=>simp [Nat.succ_le_succ_iff]
theorem kL {α : Type} (l : List α) (p : α → Bool) :
 l.countP p=(Finset.univ.filter (fun i : Fin l.length=>p l[i]=true)).card:=by
 induction l with
 | nil=>simp
 | cons a bs ih =>
  rw [List.countP_cons,ih]
  have hsplit : (Finset.univ.filter (fun i : Fin (a :: bs).length=>p (a :: bs)[i]=true)).card =
   (if p a=true then 1 else 0)+(Finset.univ.filter (fun i : Fin bs.length=>p bs[i]=true)).card:=by
   let S:=Finset.univ.filter (fun i : Fin (a :: bs).length=>p (a :: bs)[i]=true)
   let T:=Finset.univ.filter (fun i : Fin bs.length=>p bs[i]=true)
   let f : Fin bs.length ↪ Fin (a :: bs).length:=⟨Fin.succ,Fin.succ_injective _⟩
   have hsub : T.map f=S.erase 0:=by
    ext x
    simp only [S,T,f,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,
     Finset.mem_erase,Function.Embedding.coeFn_mk]
    cases x using Fin.cases with
    | zero=>simp
    | succ j =>
     constructor
     · rintro ⟨i,hi,heq⟩;have:=Fin.succ_injective _ heq;subst i;exact ⟨Fin.succ_ne_zero _,hi⟩
     · rintro ⟨_,hj⟩;exact ⟨j,hj,rfl⟩
   have hcard : (S.erase 0).card=T.card:=by rw [← hsub,Finset.card_map]
   by_cases hp : p a=true
   · have h0 : (0 : Fin (a :: bs).length) ∈ S:=by simp [S,hp]
     rw [if_pos hp, ← hcard,Nat.add_comm,Finset.card_erase_add_one h0]
   · have h0 : (0 : Fin (a :: bs).length) ∉ S:=by simp [S,hp]
     rw [if_neg hp,Nat.zero_add, ← hcard,Finset.erase_eq_of_notMem h0]
  rw [hsplit];cases p a <;> simp [Nat.add_comm]
theorem vI {α : Type} {l : List α} {p : α → Bool} {i : Nat}
  (hi : i < l.length) (h : p l[i]=true) : 1 ≤ l.countP p:=by
 rw [kL]
 exact Finset.one_le_card.mpr ⟨⟨i,hi⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
theorem wc {α : Type} {l : List α} {p : α → Bool} {i j : Nat}
 (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j)
 (h1 : p l[i]=true) (h2 : p l[j]=true) : 2 ≤ l.countP p:=by
 rw [kL]
 have hsub : ({⟨i,hi⟩,⟨j,hj⟩} : Finset (Fin l.length)) ⊆ Finset.univ.filter (fun x : Fin l.length=>p l[x]=true):=by
  intro x hx;rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1⟩
  · rw [Finset.mem_singleton.mp hx'];exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2⟩
 have hneF : (⟨i,hi⟩ : Fin l.length) ≠ ⟨j,hj⟩:=fun h=>hne (congrArg Fin.val h)
 calc 2=({⟨i,hi⟩,⟨j,hj⟩} : Finset (Fin l.length)).card:=by rw [Finset.card_pair hneF]
  _ ≤ _:=Finset.card_le_card hsub
theorem q3T {α : Type} {l : List α} {p : α → Bool} {i j k : Nat}
 (hi : i < l.length) (hj : j < l.length) (hk : k < l.length)
 (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
 (h1 : p l[i]=true) (h2 : p l[j]=true) (h3 : p l[k]=true) : 3 ≤ l.countP p:=by
 rw [kL]
 let fi : Fin l.length:=⟨i,hi⟩
 let fj : Fin l.length:=⟨j,hj⟩
 let fk : Fin l.length:=⟨k,hk⟩
 have hsub : ({fi,fj,fk} : Finset (Fin l.length)) ⊆ Finset.univ.filter (fun x : Fin l.length=>p l[x]=true):=by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx1
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1⟩
  · rcases Finset.mem_insert.mp hx1 with rfl | hx2
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2⟩
    · rw [Finset.mem_singleton.mp hx2];exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3⟩
 have hni : fi ∉ ({fj,fk} : Finset (Fin l.length)):=by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨fun h=>hij (congrArg Fin.val h),fun h=>hik (congrArg Fin.val h)⟩
 have hnj : fj ≠ fk:=fun h=>hjk (congrArg Fin.val h)
 have hcard : ({fi,fj,fk} : Finset (Fin l.length)).card=3:=by
  rw [Finset.card_insert_of_notMem hni,Finset.card_pair hnj]
 calc 3=({fi,fj,fk} : Finset (Fin l.length)).card:=hcard.symm
  _ ≤ _:=Finset.card_le_card hsub
theorem zo {tags : List qU} {i : Nat} (hi : i < tags.length) :
  qn tags i=tags[i]:=by
 induction tags generalizing i with
 | nil=>simp at hi
 | cons a bs ih =>
  cases i with
  | zero=>rfl
  | succ k=>exact ih (Nat.lt_of_succ_lt_succ hi)
def uH (start qQ : Nat) (yV : Nat → Bool) : Bool :=
 (Nat.rec (motive:=fun _=>Nat → Bool) (fun _=>true)
  (fun _ next i=>qS (yV i) (next (Nat.add i 1))) qQ) start
theorem w9 (start qQ : Nat) (yV : Nat → Bool) :
  uH start qQ yV=qE start qQ yV:=by
 induction qQ generalizing start with
 | zero=>rfl
 | succ c ih =>
  change qS (yV start) (uH (Nat.add start 1) c yV)=(yV start&&qE (start+1) c yV)
  rw [qR,ih]
noncomputable def q3c (qx : Nat → Option qy) (z8 : zt)
  (lnk : jo) (state : qc) : Bool :=
 @Option.rec qy (fun _=>Bool) false
  (fun saved =>
   qS (Nat.beq saved.1 state.1)
    (qS (Nat.beq saved.2.1 state.2.1)
     (@Bool.rec (fun _=>Bool)
      (@Option.rec z0 (fun _=>Bool) false
       (fun m=>uW saved.2.2 (vz m state.2.2.1))
       (z8 lnk.2))
      (uW saved.2.2 state.2.2.1)
      (Nat.beq lnk.2 0))))
  (qx lnk.1)
noncomputable def wM (maxK : Nat) (is24 : Bool) (mask goal : Word)
  (chart : Option qw) (cut : k6)
  (qQ : Nat) (q3 : zj) (qx : Nat → Option qy) (z8 : zt)
  (qz : Nat) (bucket : yq)
  (cf zJ : Nat) (ws : List Word) (history : List (Word × Word × Word))
  (x y out qp cout rest tok : Word) (kp0 kp1 : Bool) : Bool :=
 @Bool.rec (fun _=>Bool)
  true
  (@Option.rec jo (fun _=>Bool)
   (ye (yh out (zw kp1 y (zw kp0 x ws))) fun cws =>
    jq maxK is24 mask goal chart cut (cf,zJ,cws,(out,x,y) :: history))
   (fun lnk =>
    @Bool.rec (fun _=>Bool)
     (ye (yh out (zw kp1 y (zw kp0 x ws))) fun cws =>
      let child : qc:=(cf,zJ,cws,(out,x,y) :: history)
      zn (qS (Nat.blt lnk.1 qQ) (q3c qx z8 lnk child))
       (jq maxK is24 mask goal chart cut child))
     true
     (qS (Nat.blt lnk.1 qQ)
      (qS (Nat.beq lnk.2 0)
       (let pt:=q3 lnk.1
        qS (Nat.beq pt.1 qz) (Nat.beq pt.2 tok)))))
   (bucket tok))
  (Nat.beq (Nat.lor rest cout) qp)
noncomputable def q0N :
  {f : Nat → Bool → Word → Word → Option qw → k6 →
   Nat → zj → (Nat → Option qy) → zt → Nat → yq →
   Nat → Nat → List Word → List (Word × Word × Word) →
   Word → Word → Word → Word → Word → Word → Word → Bool → Bool → Bool // f=wM}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta wM q3c uW zw yh q32
   jq vn zz qZ qS zn kq
  beta_reduce
  exact rfl
noncomputable def zd:=q0N.1
noncomputable def zL (maxK : Nat) (is24 : Bool) (mask goal : Word)
  (chart : Option qw) (cut : k6)
  (qQ : Nat) (q3 : zj) (qx : Nat → Option qy) (z8 : zt)
  (qz : Nat) (bucket : yq)
  (state : qc) (sampleLen : Nat) (tags : List qU) : Bool :=
 let (q8,nots,ws,history):=state
 q7 (zz ws) fun n =>
 qS (Nat.ble n 64)
 (qS (kq (qS (Nat.beq nots 0) (qZ goal ws)))
 (uQ tags fun tags =>
 q7 (Nat.sub (Nat.shiftLeft 1 sampleLen) 1) fun qp =>
 q7 (Nat.sub q8 1) fun cf =>
 let dirSame:=Nat.beq nots 0
 vS dirSame qp tags fun countsSame =>
 let cS1:=countsSame.1
 let cS2:=countsSame.2.1
 let cS3:=countsSame.2.2
 let canK0Same:=Nat.ble (Nat.add (Nat.sub n 1) nots) q8
 let canK1Same:=Nat.ble (Nat.add n nots) q8
 let canK2Same:=Nat.ble (Nat.add (Nat.add n 1) nots) q8
 let nots1:=Nat.sub nots 1
 let dirNot:=Nat.beq nots1 0
 let canK0Not:=Nat.ble (Nat.add n nots1) q8
 let canK1Not:=Nat.ble (Nat.add (Nat.add n 1) nots1) q8
 let runLoop:=fun (countsNot : wS) =>
  uH 0 n fun a =>
   q7 (vR ws a) fun x =>
   @Prod.rec Word Word (fun _=>Bool) (fun xs1 xs2 =>
    let doUnary :=
     @Bool.rec (fun _=>Bool)
      (q7 (Nat.xor mask x) fun out =>
       @Bool.rec (fun _=>Bool)
        (q7 (q6 dirNot qp (xs1,xs2)) fun cxN =>
         q7 (q6 dirNot qp (Nat.xor qp xs1,Nat.xor qp xs2)) fun coutN =>
         q7 (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) a) 3) 2) 4) fun baseTok =>
         let r0:=Nat.lor countsNot.2.1 (Nat.xor countsNot.1 (Nat.land countsNot.1 cxN))
         let r1:=countsNot.1
         qS
           (@Bool.rec (fun _=>Bool) true
             (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket
              cf nots1 ws history x x out qp coutN r0 baseTok false true)
             canK0Not)
           (@Bool.rec (fun _=>Bool) true
             (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket
              cf nots1 ws history x x out qp coutN r1 (Nat.add baseTok 1) true true)
             canK1Not))
        true
        (zn (Nat.beq out 0) (zn (Nat.beq out mask) (qZ out ws))))
      true
      dirSame
    q7 (q6 dirSame qp (xs1,xs2)) fun cxS =>
    q7 (Nat.lor cS2 (Nat.xor cS1 (Nat.land cS1 cxS))) fun r2 =>
    qS doUnary
     (uH (Nat.add a 1) (Nat.sub n (Nat.add a 1)) fun b =>
      q7 (vR ws b) fun y =>
      @Prod.rec Word Word (fun _=>Bool) (fun ys1 ys2 =>
       q7 (q6 dirSame qp (ys1,ys2)) fun cyS =>
       q7 (Nat.mul (Nat.add (Nat.mul a 64) b) 3) fun baseAB =>
       q7 (Nat.lor cS3 (Nat.lor (Nat.xor cS2 (Nat.land (Nat.land cS2 cxS) cyS)) (Nat.xor cS1 (Nat.land cS1 (Nat.lor cxS cyS))))) fun r0 =>
       let doBin:=fun op out up dn =>
        q7 out fun out =>
          @Bool.rec (fun _=>Bool)
            (q7 (q6 dirSame qp (up,dn)) fun coutS =>
             q7 (Nat.mul (Nat.add baseAB op) 4) fun baseTok =>
             qS
              (@Bool.rec (fun _=>Bool) true
               (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket
                 cf nots ws history x y out qp coutS r0 baseTok false false)
               canK0Same)
              (@Bool.rec (fun _=>Bool) true
               (q7 (Nat.lor cS2 (Nat.xor cS1 (Nat.land cS1 cyS))) fun r1 =>
                qS
                  (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket
                   cf nots ws history x y out qp coutS r1 (Nat.add baseTok 1) true false)
                  (qS
                   (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket
                    cf nots ws history x y out qp coutS r2 (Nat.add baseTok 2) false true)
                   (@Bool.rec (fun _=>Bool) true
                    (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket
                     cf nots ws history x y out qp coutS cS1 (Nat.add baseTok 3) true true)
                    canK2Same)))
               canK1Same))
            true
            (zn (Nat.beq out 0) (zn (Nat.beq out mask) (qZ out ws)))
       qS (doBin 0 (Nat.land x y) (Nat.land xs1 ys1) (Nat.land xs2 ys2))
        (doBin 1 (Nat.lor x y) (Nat.lor xs1 ys1) (Nat.lor xs2 ys2)))
      (qn tags b)))
   (qn tags a)
 @Bool.rec (fun _=>Bool) (vS dirNot qp tags runLoop) (runLoop countsSame) dirSame))
theorem y3 {maxK : Nat} {is24 : Bool} {mask goal : Word}
 {chart : Option qw} {cut : k6}
 {qQ : Nat} {q3 : zj} {qx : Nat → Option qy} {z8 : zt}
 {qz : Nat} {bucket : yq}
 {sample : qH} {a b op keep : Nat} {state child : qc}
 {cout rest : Word} {kp0 kp1 : Bool}
 (jA : j3 mask goal sample)
 (hcoutHi : ∀ k ≥ sample.2,cout.testBit k=false)
 (hrestHi : ∀ k ≥ sample.2,rest.testBit k=false)
 (hcoutOk : ∀ q < sample.2,
  let code:=z3 sample.1 18 q
  let p:=Nat.land code 511
  let n:=Nat.shiftRight code 9
  let out:=zg mask op (state.2.2.1.getD a 0) (state.2.2.1.getD b 0)
  cout.testBit q=if Nat.beq (if op==2 then Nat.sub state.2.1 1 else state.2.1) 0
   then (out.testBit p && !out.testBit n) else Bool.xor (out.testBit p) (out.testBit n))
 (hrestOk : ∀ q < sample.2,rest.testBit q=false →
  ∀ i < state.2.2.1.length,(kp0=true ∨ i ≠ a) → (kp1=true ∨ i ≠ b) →
  let code:=z3 sample.1 18 q
  let p:=Nat.land code 511
  let n:=Nat.shiftRight code 9
  let w:=state.2.2.1.getD i 0
  (if Nat.beq (if op==2 then Nat.sub state.2.1 1 else state.2.1) 0
   then (w.testBit p && !w.testBit n) else Bool.xor (w.testBit p) (w.testBit n))=false)
 (hkp0 : kp0=keep.testBit 0)
 (hkp1 : kp1=((op==2)||keep.testBit 1))
 (hb : b < 64) (hop : op < 3) (hk : keep < 4)
 (eval : qL mask (zl a b op keep) state=some child)
 (zM : qm mask goal) (j6 : zZ mask goal child) (nd : state.2.2.1.Nodup)
 (openChild : jq maxK is24 mask goal chart cut child=false)
 (hcheck : zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket
  (Nat.sub state.1 1) (if op==2 then Nat.sub state.2.1 1 else state.2.1)
  state.2.2.1 state.2.2.2 (state.2.2.1.getD a 0) (state.2.2.1.getD b 0)
  (zg mask op (state.2.2.1.getD a 0) (state.2.2.1.getD b 0))
  (Nat.sub (Nat.shiftLeft 1 sample.2) 1) cout rest
  (zl a b op keep) kp0 kp1=true) :
 jR qQ q3 qx z8 qz bucket (zl a b op keep) child=true:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 have direct:=(jC (mask:=mask) (state:=(q8,nots,ws,history)) hb hop hk).trans eval
 let x:=ws.getD a 0;let y:=ws.getD b 0;let out:=zg mask op x y
 let zJ:=if op==2 then Nat.sub nots 1 else nots
 have hce : child=(Nat.sub q8 1,zJ,
  yh out (zw kp1 y (zw kp0 x ws)),(out,x,y) :: history):=by
  let bad : Bool:=q8==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
  let stale : Bool:=out==0||out==mask||ws.contains out
  change (if bad then none else if stale then none else
   some (q8 - 1,if op==2 then nots - 1 else nots,qB out (yg ws op keep x y),(out,x,y) :: history))=some child at direct
  by_cases h1 : bad=true;simp [h1] at direct
  by_cases h2 : stale=true;simp [h1,h2] at direct
  have heq : (q8 - 1,if op==2 then nots - 1 else nots,qB out (yg ws op keep x y),(out,x,y) :: history)=child:=by
   simpa [h1,h2] using direct
  rw [← heq,uL,ja,ja,hkp0,hkp1];rfl
 rw [show zd=wM from q0N.2] at hcheck
 unfold wM at hcheck
 let qp:=Nat.sub (Nat.shiftLeft 1 sample.2) 1
 cases hcov : Nat.beq (Nat.lor rest cout) qp
 · exfalso
   have hne : Nat.lor rest cout ≠ qp:=fun heq=>by rw [heq,Nat.beq_refl] at hcov;exact Bool.noConfusion hcov
   have hex : ∃ q,(Nat.lor rest cout).testBit q ≠ qp.testBit q:=by
    by_contra hall
    push_neg at hall
    exact hne (Nat.eq_of_testBit_eq hall)
   obtain ⟨q,hqne⟩:=hex
   have hfullBit : ∀ j,qp.testBit j=decide (j < sample.2):=by
    intro j;change ((1<<<sample.2) - 1).testBit j=_;rw [Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow_sub_one]
   have hqlt : q < sample.2:=by
    by_contra hge
    have hk : q ≥ sample.2:=Nat.le_of_not_lt hge
    have h1 : (Nat.lor rest cout).testBit q=false:=by rw [q0.qX,hrestHi q hk,hcoutHi q hk];rfl
    have h2 : qp.testBit q=false:=by rw [hfullBit];simp [hge]
    exact hqne (h1.trans h2.symm)
   have hfq : qp.testBit q=true:=by rw [hfullBit];simp [hqlt]
   have hlor0 : (Nat.lor rest cout).testBit q=false:=by
    cases hb' : (Nat.lor rest cout).testBit q
    · rfl
    · exfalso;exact hqne (hb'.trans hfq.symm)
   rw [q0.qX,Bool.or_eq_false_iff] at hlor0
   obtain ⟨hr0,hc0⟩:=hlor0
   obtain ⟨hp,mn,hneg⟩:=jA q hqlt
   let p:=Nat.land (z3 sample.1 18 q) 511
   let n:=Nat.shiftRight (z3 sample.1 18 q) 9
   obtain ⟨_,k,_,y1⟩:=j6
   rw [hce] at y1
   change qf mask goal k zJ (yh out (zw kp1 y (zw kp0 x ws))).toFinset at y1
   have hsame : (out :: yg ws op keep x y).toFinset=(yh out (zw kp1 y (zw kp0 x ws))).toFinset:=by
    rw [uL,ja,ja,hkp0,hkp1]
    ext w;simp only [List.mem_toFinset,List.mem_cons,vF];rfl
   have y1' : qf mask goal k zJ (out :: yg ws op keep x y).toFinset:=by rwa [hsame]
   have hsepFalse : ∀ w ∈ out :: yg ws op keep x y,
    (if Nat.beq zJ 0 then (w.testBit p && !w.testBit n) else Bool.xor (w.testBit p) (w.testBit n))=false:=by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | later
    · have hco:=hcoutOk q hqlt
      exact hco.symm.trans hc0
    · have rightMem:=q3e (wg nd (keep.testBit 0) x) later
      have leftMem:=q3e nd rightMem.1
      obtain ⟨i,inside,eq⟩:=List.mem_iff_getElem.mp leftMem.1
      have atIndex : ws.getD i 0=w:=by
       simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside] using eq
      have hia : kp0=true ∨ i ≠ a:=by
       rw [hkp0];rcases leftMem.2 with h | h;exact Or.inl h;exact Or.inr (fun he=>h (he ▸ atIndex).symm)
      have hib : kp1=true ∨ i ≠ b:=by
       rw [hkp1];rcases rightMem.2 with h | h;exact Or.inl h;exact Or.inr (fun he=>h (he ▸ atIndex).symm)
      simpa only [atIndex] using hrestOk q hqlt hr0 i inside hia hib
   cases hdir : Nat.beq zJ 0
   · have h:=q1D y1' ((kU zM hp).trans mn.symm) (fun w hw=>by
      have hb':=hsepFalse w (List.mem_toFinset.mp hw)
      simp only [hdir,Bool.false_eq_true, ↓reduceIte] at hb'
      unfold jV
      cases h1 : w.testBit p <;> cases h2 : w.testBit n <;> simp_all)
     change goal.testBit p=goal.testBit n at h
     rw [hp,hneg] at h
     exact Bool.noConfusion h
   · have ht0 : zJ=0:=Nat.beq_eq.mp hdir
     rw [ht0] at y1'
     obtain ⟨w,hw,on,off⟩:=q2f y1' hp hneg
     have hb':=hsepFalse w (List.mem_toFinset.mp hw)
     dsimp only [p,n] at on off hb'
     simp only [hdir, ↓reduceIte,on,off] at hb'
     exact Bool.noConfusion hb'
 · rw [hcov] at hcheck;dsimp only at hcheck
   rw [show jR=kP from u6.2]
   unfold kP
   cases hbk : bucket (zl a b op keep) with
   | none =>
    rw [hbk] at hcheck;dsimp only at hcheck
    rw [zV, ← hce,openChild] at hcheck
    exact Bool.noConfusion hcheck
   | some lnk =>
    rw [hbk] at hcheck;dsimp only at hcheck ⊢
    rw [qR,zQ,Bool.and_eq_true,Bool.or_eq_true]
    cases htr : qS (Nat.blt lnk.1 qQ) (qS (Nat.beq lnk.2 0)
     (qS (Nat.beq (q3 lnk.1).1 qz) (Nat.beq (q3 lnk.1).2 (zl a b op keep))))
    · rw [htr] at hcheck;dsimp only at hcheck
      rw [zV,zQ,qR, ← hce,openChild,Bool.or_false,Bool.and_eq_true] at hcheck
      exact ⟨hcheck.1,Or.inr hcheck.2⟩
    · simp only [qR,Bool.and_eq_true] at htr
      refine ⟨htr.1,Or.inl ?_⟩
      simp only [qR,Bool.and_eq_true]
      exact htr.2
theorem q7P {maxK : Nat} {is24 : Bool} {mask goal : Word} {chart : Option qw}
 {cut : k6} {qQ : Nat} {q3 : zj} {qx : Nat → Option qy}
 {z8 : zt} {qz : Nat} {bucket : yq}
 {state child : qc} {sample : qH} {tags : List qU} {a b op keep : Nat}
 (jA : j3 mask goal sample)
 (htagsLen : tags.length=state.2.2.1.length)
 (htagsVal : ∀ j < state.2.2.1.length,zr sample (state.2.2.1.getD j 0) (qn tags j))
 (checked : zL maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket state sample.2 tags=true)
 (ha : a < state.2.2.1.length)
 (legal : (a=b ∧ op=2 ∧ keep < 2 ∧ state.2.1 ≠ 0) ∨
  (a < b ∧ b < state.2.2.1.length ∧ op < 2 ∧ keep < 4))
 (eval : qL mask (zl a b op keep) state=some child)
 (zM : qm mask goal) (j6 : zZ mask goal child) (nd : state.2.2.1.Nodup)
 (openChild : jq maxK is24 mask goal chart cut child=false) :
 jR qQ q3 qx z8 qz bucket (zl a b op keep) child=true:=by
 obtain ⟨q8,nots,ws,history⟩:=state
 change a < ws.length at ha
 change tags.length=ws.length at htagsLen
 change ∀ j < ws.length,zr sample (ws.getD j 0) (qn tags j) at htagsVal
 have htagsHi : ∀ t ∈ tags, ∀ k ≥ sample.2,t.1.testBit k=false ∧ t.2.testBit k=false:=by
  intro t ht k hk
  obtain ⟨j,hj,rfl⟩:=List.mem_iff_getElem.mp ht
  have hval:=htagsVal j (htagsLen ▸ hj)
  rw [zo hj] at hval
  exact hval.1 k hk
 unfold zL at checked
 simp only [ql,q35,q4Z,qR,uP,
  yd,za,w9,Bool.and_eq_true] at checked
 obtain ⟨hwidthB,_,hbody⟩:=checked
 have qV : ws.length ≤ 64:=Nat.ble_eq.mp hwidthB
 have hchildFit : ∀ (hop : op < 3) (hb : b < 64) (hk : keep < 4),
  zE ws.length op keep+(if op==2 then nots - 1 else nots) ≤ q8:=by
  intro hop hb hk
  have hdir:=(jC (mask:=mask) (state:=(q8,nots,ws,history)) hb hop hk).trans eval
  let x:=ws.getD a 0;let y:=ws.getD b 0;let out:=zg mask op x y
  let bad : Bool:=q8==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
  let stale : Bool:=out==0||out==mask||ws.contains out
  change (if bad then none else if stale then none else
   some (q8 - 1,if op==2 then nots - 1 else nots,qB out (yg ws op keep x y),(out,x,y) :: history))=some child at hdir
  by_cases h1 : bad=true;simp [h1] at hdir
  by_cases h2 : stale=true;simp [h1,h2] at hdir
  have heq : (q8 - 1,if op==2 then nots - 1 else nots,qB out (yg ws op keep x y),(out,x,y) :: history)=child:=by
   simpa [h1,h2] using hdir
  have hpos : 0 < q8:=(vA eval).1
  have hins : (qB out (yg ws op keep x y)).length=(yg ws op keep x y).length+1:=by
   generalize yg ws op keep x y=l
   induction l with | nil=>rfl | cons u us ih=>change (if out ≤ u then out :: u :: us else u :: qB out us).length=_;split <;> simp [ih]
  have hkl : ∀ (kp : Bool) (u : Word) (l : List Word),l.length - (if kp then 0 else 1) ≤ (zu kp u l).length:=by
   intro kp u l;cases kp;exact List.le_length_erase;simp [zu]
  have h1l:=hkl (keep.testBit 0) x ws
  have h2l:=hkl (op==2||keep.testBit 1) y (zu (keep.testBit 0) x ws)
  rw [← heq] at openChild
  unfold jq at openChild
  simp only [zQ,yd,Bool.or_eq_false_iff] at openChild
  have hnf : ¬ (q8 - 1+1 < (qB out (yg ws op keep x y)).length+(if op==2 then nots - 1 else nots)):=by
   intro hlt
   have hb' : Nat.blt (Nat.add (q8 - 1) 1) (Nat.add (qB out (yg ws op keep x y)).length (if op==2 then nots - 1 else nots))=true :=
    Nat.blt_eq.mpr hlt
   rw [hb'] at openChild;exact Bool.noConfusion openChild.1
  unfold zE
  dsimp only [yg] at hins hnf
  omega
 let qp:=Nat.sub (Nat.shiftLeft 1 sample.2) 1
 have hsigEq : ∀ (dir : Bool) (j : Nat) (hj : j < ws.length) (q : Nat) (hq : q < sample.2),
  (q6 dir qp (qn tags j)).testBit q =
  (let code:=z3 sample.1 18 q
   let p:=Nat.land code 511
   let n:=Nat.shiftRight code 9
   let w:=ws.getD j 0
   if dir then (w.testBit p && !w.testBit n) else Bool.xor (w.testBit p) (w.testBit n)):=by
  intro dir j hj q hq
  rw [k8 hq]
  obtain ⟨h1,h2⟩:=(htagsVal j hj).2 q hq
  rw [h1,h2]
 have hr1Spec : ∀ (dir : Bool) (idx : Nat) (hidx : idx < ws.length),
  let cs:=tags.foldr (fun tag acc =>
   let c:=q6 dir qp tag
   (Nat.lor acc.1 c,Nat.lor acc.2.1 (Nat.land acc.1 c),Nat.lor acc.2.2 (Nat.land acc.2.1 c))) (0,0,0)
  let cIdx:=q6 dir qp (qn tags idx)
  let r:=Nat.lor cs.2.1 (Nat.xor cs.1 (Nat.land cs.1 cIdx))
  (∀ k ≥ sample.2,r.testBit k=false) ∧
  (∀ q < sample.2,r.testBit q=false → ∀ i < ws.length,i ≠ idx →
   (q6 dir qp (qn tags i)).testBit q=false):=by
  intro dir idx hidx
  dsimp only
  obtain ⟨hcsHi,hcsBit⟩:=k4 (dir:=dir) htagsHi
  refine ⟨fun k hk => ?_,fun q hq hr0 i hi hne => ?_⟩
  · obtain ⟨h1,h2,_⟩:=hcsHi k hk
    have hci:=y2 (dir:=dir) hk ((htagsVal idx hidx).1 k hk)
    rw [q0.qX,q0.j7,q0.qM,h1,h2,hci];rfl
  · obtain ⟨h1,h2,_⟩:=hcsBit q hq
    rw [q0.qX,q0.j7,q0.qM,h1,h2,Bool.or_eq_false_iff] at hr0
    by_contra htrue
    have hti : (q6 dir qp (qn tags i)).testBit q=true:=by
     cases h : (q6 dir qp (qn tags i)).testBit q;exact absurd h htrue;rfl
    have hltI : i < tags.length:=htagsLen.symm ▸ hi
    have hltIdx : idx < tags.length:=htagsLen.symm ▸ hidx
    rw [zo hltI] at hti
    have hge1 : 1 ≤ tags.countP (fun t=>(q6 dir qp t).testBit q):=vI (p:=fun t=>(q6 dir qp t).testBit q) hltI hti
    have hlt2 : ¬ (2 ≤ tags.countP (fun t=>(q6 dir qp t).testBit q)):=by
     intro h2';rw [decide_eq_true h2'] at hr0;exact Bool.noConfusion hr0.1
    cases hcIdx : (q6 dir qp (qn tags idx)).testBit q
    · rw [hcIdx,decide_eq_true hge1] at hr0;exact Bool.noConfusion hr0.2
    · rw [zo hltIdx] at hcIdx
      exact hlt2 (wc (p:=fun t=>(q6 dir qp t).testBit q) hltI hltIdx hne hti hcIdx)
 have hr0Spec : ∀ (dir : Bool) (ia ib : Nat) (hia : ia < ws.length) (hib : ib < ws.length) (hab : ia ≠ ib),
  let cs:=tags.foldr (fun tag acc =>
   let c:=q6 dir qp tag
   (Nat.lor acc.1 c,Nat.lor acc.2.1 (Nat.land acc.1 c),Nat.lor acc.2.2 (Nat.land acc.2.1 c))) (0,0,0)
  let ca:=q6 dir qp (qn tags ia)
  let cb:=q6 dir qp (qn tags ib)
  let r:=Nat.lor cs.2.2 (Nat.lor (Nat.xor cs.2.1 (Nat.land (Nat.land cs.2.1 ca) cb)) (Nat.xor cs.1 (Nat.land cs.1 (Nat.lor ca cb))))
  (∀ k ≥ sample.2,r.testBit k=false) ∧
  (∀ q < sample.2,r.testBit q=false → ∀ i < ws.length,i ≠ ia → i ≠ ib →
   (q6 dir qp (qn tags i)).testBit q=false):=by
  intro dir ia ib hia hib hab
  dsimp only
  obtain ⟨hcsHi,hcsBit⟩:=k4 (dir:=dir) htagsHi
  refine ⟨fun k hk => ?_,fun q hq hr0 i hi hna hnb => ?_⟩
  · obtain ⟨h1,h2,h3⟩:=hcsHi k hk
    have hca:=y2 (dir:=dir) hk ((htagsVal ia hia).1 k hk)
    have hcb:=y2 (dir:=dir) hk ((htagsVal ib hib).1 k hk)
    rw [q0.qX,q0.qX,q0.j7,q0.qM,q0.qM,
     q0.j7,q0.qM,q0.qX,h1,h2,h3,hca,hcb];rfl
  · obtain ⟨h1,h2,h3⟩:=hcsBit q hq
    rw [q0.qX,q0.qX,q0.j7,q0.qM,q0.qM,
     q0.j7,q0.qM,q0.qX,h1,h2,h3,
     Bool.or_eq_false_iff,Bool.or_eq_false_iff] at hr0
    obtain ⟨h3f,h2f,h1f⟩:=hr0
    by_contra htrue
    have hti : (q6 dir qp (qn tags i)).testBit q=true:=by
     cases h : (q6 dir qp (qn tags i)).testBit q;exact absurd h htrue;rfl
    have hltI : i < tags.length:=htagsLen.symm ▸ hi
    have hltA : ia < tags.length:=htagsLen.symm ▸ hia
    have hltB : ib < tags.length:=htagsLen.symm ▸ hib
    rw [zo hltI] at hti
    have hge1 : 1 ≤ tags.countP (fun t=>(q6 dir qp t).testBit q):=vI (p:=fun t=>(q6 dir qp t).testBit q) hltI hti
    have hlt3 : ¬ (3 ≤ tags.countP (fun t=>(q6 dir qp t).testBit q)):=by
     intro h3';rw [decide_eq_true h3'] at h3f;exact Bool.noConfusion h3f
    cases hca : (q6 dir qp (qn tags ia)).testBit q <;>
    cases hcb : (q6 dir qp (qn tags ib)).testBit q
    · rw [hca,hcb,decide_eq_true hge1] at h1f;exact Bool.noConfusion h1f
    · have hcb':=hcb;rw [zo hltB] at hcb'
      have hge2:=wc (p:=fun t=>(q6 dir qp t).testBit q) hltI hltB hnb hti hcb'
      rw [hca,hcb,decide_eq_true hge2] at h2f;exact Bool.noConfusion h2f
    · have hca':=hca;rw [zo hltA] at hca'
      have hge2:=wc (p:=fun t=>(q6 dir qp t).testBit q) hltI hltA hna hti hca'
      rw [hca,hcb,decide_eq_true hge2] at h2f;exact Bool.noConfusion h2f
    · rw [zo hltA] at hca;rw [zo hltB] at hcb
      exact hlt3 (q3T (p:=fun t=>(q6 dir qp t).testBit q) hltI hltA hltB hna hnb hab hti hca hcb)
 rcases legal with ⟨rfl,rfl,hk,hn⟩ | ⟨ab,hb,hop,hk⟩
 · have hnf : Nat.beq nots 0=false:=by cases nots;exact absurd rfl hn;rfl
   rw [hnf] at hbody;dsimp only at hbody
   have atA:=zN hbody (i:=a) (Nat.zero_le _) (by simpa using ha)
   simp only [ql,qR,uM,Bool.and_eq_true] at atA
   have unary:=atA.1
   have fields:=jC (mask:=mask) (state:=(q8,nots,ws,history)) (a:=a) (b:=a) (op:=2) (keep:=keep) (by omega) (by decide) (by omega)
   have direct:=fields.trans eval
   obtain ⟨_,hfresh⟩:=uc direct
   have hstF : zn (Nat.beq (Nat.xor mask (ws.getD a 0)) 0)
    (zn (Nat.beq (Nat.xor mask (ws.getD a 0)) mask) (ws.contains (Nat.xor mask (ws.getD a 0))))=false:=by
    simp only [zQ,qA];simpa [zg,Bool.or_assoc] using hfresh
   rw [hstF] at unary;dsimp only at unary
   simp only [ql,qR,Bool.and_eq_true] at unary
   obtain ⟨hu0,hu1⟩:=unary
   have hfit:=hchildFit (by decide) (by omega) (by omega)
   have hgt : zg mask 2 (ws.getD a 0) (ws.getD a 0)=Nat.xor mask (ws.getD a 0):=rfl
   have htok0 : Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) a) 3) 2) 4=zl a a 2 0:=rfl
   have htok1 : Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) a) 3) 2) 4) 1=zl a a 2 1:=rfl
   have heq2 : (if ((2 : Nat)==2)=true then Nat.sub nots 1 else nots)=Nat.sub nots 1:=rfl
   have htagOut : zr sample (Nat.xor mask (ws.getD a 0))
    (Nat.xor qp (qn tags a).1,Nat.xor qp (qn tags a).2):=by
    have h:=jW (op:=2) (x:=(ws.getD a 0,qn tags a)) (y:=(ws.getD a 0,qn tags a)) jA zM (htagsVal a ha) (htagsVal a ha)
    exact h
   have hcoutHi : ∀ k ≥ sample.2,(q6 (Nat.beq (Nat.sub nots 1) 0) qp (Nat.xor qp (qn tags a).1,Nat.xor qp (qn tags a).2)).testBit k=false :=
    fun k hk=>y2 hk (htagOut.1 k hk)
   have hcoutOk : ∀ q < sample.2,
    (q6 (Nat.beq (Nat.sub nots 1) 0) qp (Nat.xor qp (qn tags a).1,Nat.xor qp (qn tags a).2)).testBit q =
    (let code:=z3 sample.1 18 q;let p:=Nat.land code 511;let n:=Nat.shiftRight code 9
     let out:=zg mask 2 (ws.getD a 0) (ws.getD a 0)
     if Nat.beq (if ((2 : Nat)==2)=true then Nat.sub nots 1 else nots) 0
     then (out.testBit p && !out.testBit n) else Bool.xor (out.testBit p) (out.testBit n)):=by
    intro q hq
    rw [k8 hq]
    obtain ⟨h1,h2⟩:=htagOut.2 q hq
    rw [h1,h2];rfl
   have hka : keep=0 ∨ keep=1:=by omega
   rcases hka with rfl | rfl
   · have hc0 : Nat.ble (Nat.add ws.length (Nat.sub nots 1)) q8=true:=by
      apply Nat.ble_eq.mpr;have hdf : ws.length - 1 - 0+1+(nots - 1) ≤ q8:=hfit;change ws.length+(nots - 1) ≤ q8;omega
     rw [hc0] at hu0;dsimp only at hu0
     obtain ⟨hrHi,hrOk⟩:=hr1Spec (Nat.beq (Nat.sub nots 1) 0) a ha
     exact y3 (kp0:=false) (kp1:=true) jA hcoutHi hrHi hcoutOk
      (fun q hq hr0 i hi h1 _=>by
       have:=hrOk q hq hr0 i hi (h1.resolve_left Bool.noConfusion)
       rwa [hsigEq _ i hi q hq] at this)
      rfl rfl (by omega) (by decide) (by decide) eval zM j6 nd openChild
      (by simpa only [heq2,hgt,htok0] using hu0)
   · have hc1 : Nat.ble (Nat.add (Nat.add ws.length 1) (Nat.sub nots 1)) q8=true:=by
      apply Nat.ble_eq.mpr;have hdf : ws.length - 0 - 0+1+(nots - 1) ≤ q8:=hfit;change ws.length+1+(nots - 1) ≤ q8;omega
     rw [hc1] at hu1;dsimp only at hu1
     obtain ⟨hcsHi,hcsBit⟩:=k4 (dir:=Nat.beq (Nat.sub nots 1) 0) htagsHi
     exact y3 (kp0:=true) (kp1:=true) jA hcoutHi
      (fun k hk=>(hcsHi k hk).1) hcoutOk
      (fun q hq hr0 i hi _ _=>by
       have h1:=(hcsBit q hq).1;rw [h1] at hr0
       by_contra htrue
       have hti : (q6 (Nat.beq (Nat.sub nots 1) 0) qp (qn tags i)).testBit q=true:=by
        rw [hsigEq _ i hi q hq];cases h : (if Nat.beq (Nat.sub nots 1) 0=true then _ else _);exact absurd h htrue;rfl
       have hltI : i < tags.length:=htagsLen.symm ▸ hi
       rw [zo hltI] at hti
       have hge1:=vI (p:=fun t=>(q6 (Nat.beq (Nat.sub nots 1) 0) qp t).testBit q) hltI hti
       rw [decide_eq_true hge1] at hr0;exact Bool.noConfusion hr0)
      rfl rfl (by omega) (by decide) (by decide) eval zM j6 nd openChild
      (by simpa only [heq2,hgt,htok1] using hu1)
 · change b < ws.length at hb
   have binary : qE (Nat.add a 1) (Nat.sub ws.length (Nat.add a 1)) (fun b =>
    q7 (vR ws b) fun y =>
    @Prod.rec Word Word (fun _=>Bool) (fun ys1 ys2 =>
     let countsSame:=tags.foldr (fun tag acc=>let c:=q6 (Nat.beq nots 0) qp tag;(Nat.lor acc.1 c,Nat.lor acc.2.1 (Nat.land acc.1 c),Nat.lor acc.2.2 (Nat.land acc.2.1 c))) (0,0,0)
     let cxS:=q6 (Nat.beq nots 0) qp (qn tags a)
     let r2:=Nat.lor countsSame.2.1 (Nat.xor countsSame.1 (Nat.land countsSame.1 cxS))
     let cyS:=q6 (Nat.beq nots 0) qp (ys1,ys2)
     let baseAB:=Nat.mul (Nat.add (Nat.mul a 64) b) 3
     let r0:=Nat.lor countsSame.2.2 (Nat.lor (Nat.xor countsSame.2.1 (Nat.land (Nat.land countsSame.2.1 cxS) cyS)) (Nat.xor countsSame.1 (Nat.land countsSame.1 (Nat.lor cxS cyS))))
     let doBin:=fun op out up dn =>
      q7 out fun out =>
       @Bool.rec (fun _=>Bool)
        (q7 (q6 (Nat.beq nots 0) qp (up,dn)) fun coutS =>
         q7 (Nat.mul (Nat.add baseAB op) 4) fun baseTok =>
         qS (@Bool.rec (fun _=>Bool) true (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket (Nat.sub q8 1) nots ws history (ws.getD a 0) y out qp coutS r0 baseTok false false) (Nat.ble (Nat.add (Nat.sub ws.length 1) nots) q8))
          (@Bool.rec (fun _=>Bool) true
           (q7 (Nat.lor countsSame.2.1 (Nat.xor countsSame.1 (Nat.land countsSame.1 cyS))) fun r1 =>
            qS (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket (Nat.sub q8 1) nots ws history (ws.getD a 0) y out qp coutS r1 (Nat.add baseTok 1) true false)
             (qS (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket (Nat.sub q8 1) nots ws history (ws.getD a 0) y out qp coutS r2 (Nat.add baseTok 2) false true)
              (@Bool.rec (fun _=>Bool) true (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket (Nat.sub q8 1) nots ws history (ws.getD a 0) y out qp coutS countsSame.1 (Nat.add baseTok 3) true true) (Nat.ble (Nat.add (Nat.add ws.length 1) nots) q8))))
           (Nat.ble (Nat.add ws.length nots) q8)))
        true (zn (Nat.beq out 0) (zn (Nat.beq out mask) (qZ out ws)))
     qS (doBin 0 (Nat.land (ws.getD a 0) y) (Nat.land (qn tags a).1 ys1) (Nat.land (qn tags a).2 ys2))
      (doBin 1 (Nat.lor (ws.getD a 0) y) (Nat.lor (qn tags a).1 ys1) (Nat.lor (qn tags a).2 ys2)))
    (qn tags b))=true:=by
    cases hds : Nat.beq nots 0
    · simp only [hds] at hbody ⊢
      have atA:=zN hbody (i:=a) (Nat.zero_le _) (by simpa using ha)
      simp only [ql,qR,uM,w9,za,Bool.and_eq_true] at atA
      simpa only [ql,qR,uM,za,Prod.mk.eta] using atA.2
    · simp only [hds] at hbody ⊢
      have atA:=zN hbody (i:=a) (Nat.zero_le _) (by simpa using ha)
      simp only [ql,qR,uM,w9,za,Bool.and_eq_true] at atA
      simpa only [ql,qR,uM,za,Prod.mk.eta] using atA.2
   have hlo : Nat.add a 1 ≤ b:=by change a+1 ≤ b;omega
   have hhi : b < Nat.add a 1+Nat.sub ws.length (Nat.add a 1):=by change b < a+1+(ws.length - (a+1));omega
   have atB:=zN binary (i:=b) hlo hhi
   simp only [ql,uM,qR,za,Bool.and_eq_true] at atB
   obtain ⟨hAnd,hOr⟩:=atB
   have fields:=jC (mask:=mask) (state:=(q8,nots,ws,history)) (a:=a) (b:=b) (op:=op) (keep:=keep) (by omega) (by omega) hk
   have direct:=fields.trans eval
   obtain ⟨_,hfresh⟩:=uc direct
   have hfit:=hchildFit (by omega) (by omega) hk
   have handleOp : ∀ (opv : Nat) (hopEq : op=opv) (hopLt : opv < 2) (outW up dn : Word)
    (houtEq : zg mask opv (ws.getD a 0) (ws.getD b 0)=outW)
    (htagOut : zr sample outW (up,dn))
    (hbr : @Bool.rec (fun _=>Bool)
     (let countsSame:=tags.foldr (fun tag acc=>let c:=q6 (Nat.beq nots 0) qp tag;(Nat.lor acc.1 c,Nat.lor acc.2.1 (Nat.land acc.1 c),Nat.lor acc.2.2 (Nat.land acc.2.1 c))) (0,0,0)
      let cxS:=q6 (Nat.beq nots 0) qp (qn tags a)
      let cyS:=q6 (Nat.beq nots 0) qp (qn tags b)
      let r2:=Nat.lor countsSame.2.1 (Nat.xor countsSame.1 (Nat.land countsSame.1 cxS))
      let r0:=Nat.lor countsSame.2.2 (Nat.lor (Nat.xor countsSame.2.1 (Nat.land (Nat.land countsSame.2.1 cxS) cyS)) (Nat.xor countsSame.1 (Nat.land countsSame.1 (Nat.lor cxS cyS))))
      let r1:=Nat.lor countsSame.2.1 (Nat.xor countsSame.1 (Nat.land countsSame.1 cyS))
      let coutS:=q6 (Nat.beq nots 0) qp (up,dn)
      let baseTok:=Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4
      (@Bool.rec (fun _=>Bool) true (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket (Nat.sub q8 1) nots ws history (ws.getD a 0) (ws.getD b 0) outW qp coutS r0 baseTok false false) (Nat.ble (Nat.add (Nat.sub ws.length 1) nots) q8)) &&
      (@Bool.rec (fun _=>Bool) true
       ((zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket (Nat.sub q8 1) nots ws history (ws.getD a 0) (ws.getD b 0) outW qp coutS r1 (Nat.add baseTok 1) true false) &&
        ((zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket (Nat.sub q8 1) nots ws history (ws.getD a 0) (ws.getD b 0) outW qp coutS r2 (Nat.add baseTok 2) false true) &&
         (@Bool.rec (fun _=>Bool) true (zd maxK is24 mask goal chart cut qQ q3 qx z8 qz bucket (Nat.sub q8 1) nots ws history (ws.getD a 0) (ws.getD b 0) outW qp coutS countsSame.1 (Nat.add baseTok 3) true true) (Nat.ble (Nat.add (Nat.add ws.length 1) nots) q8))))
       (Nat.ble (Nat.add ws.length nots) q8)))
     true
     (zn (Nat.beq outW 0) (zn (Nat.beq outW mask) (ws.contains outW)))=true),
    jR qQ q3 qx z8 qz bucket (zl a b op keep) child=true:=by
    intro opv hopEq hopLt outW up dn houtEq htagOut hbr
    subst op
    subst outW
    have hstF : zn (Nat.beq (zg mask opv (ws.getD a 0) (ws.getD b 0)) 0)
     (zn (Nat.beq (zg mask opv (ws.getD a 0) (ws.getD b 0)) mask)
      (ws.contains (zg mask opv (ws.getD a 0) (ws.getD b 0))))=false:=by
     simp only [zQ,qA];simpa [Bool.or_assoc] using hfresh
    rw [hstF] at hbr;dsimp only at hbr
    rw [Bool.and_eq_true] at hbr
    obtain ⟨hk0,hk123⟩:=hbr
    have hne2 : (opv==2)=false:=by cases h : (opv==2);rfl;exfalso;have:=beq_iff_eq.mp h;omega
    have hne2i : (if (opv==2)=true then Nat.sub nots 1 else nots)=nots:=by rw [hne2];rfl
    have hne2i' : (if (opv==2)=true then nots - 1 else nots)=nots:=by rw [hne2];rfl
    have htok0 : Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4=zl a b opv 0:=rfl
    have htok1 : Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 1=zl a b opv 1:=rfl
    have htok2 : Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 2=zl a b opv 2:=rfl
    have htok3 : Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 3=zl a b opv 3:=rfl
    have hcoutHi : ∀ k ≥ sample.2,(q6 (Nat.beq nots 0) qp (up,dn)).testBit k=false :=
     fun k hk=>y2 hk (htagOut.1 k hk)
    have hcoutOk : ∀ q < sample.2,
     (q6 (Nat.beq nots 0) qp (up,dn)).testBit q =
     (let code:=z3 sample.1 18 q;let p:=Nat.land code 511;let n:=Nat.shiftRight code 9
      let out:=zg mask opv (ws.getD a 0) (ws.getD b 0)
      if Nat.beq (if (opv==2)=true then Nat.sub nots 1 else nots) 0
      then (out.testBit p && !out.testBit n) else Bool.xor (out.testBit p) (out.testBit n)):=by
     intro q hq;rw [k8 hq,hne2i];obtain ⟨h1,h2⟩:=htagOut.2 q hq;rw [h1,h2]
    have hcases : keep=0 ∨ keep=1 ∨ keep=2 ∨ keep=3:=by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · have hc : Nat.ble (Nat.add (Nat.sub ws.length 1) nots) q8=true:=by
       apply Nat.ble_eq.mpr
       have hfl : zE ws.length opv 0=ws.length - 1 - 1+1:=by unfold zE;rw [hne2];rfl
       rw [hfl,hne2i'] at hfit;change ws.length - 1+nots ≤ q8;omega
      rw [hc] at hk0;dsimp only at hk0
      obtain ⟨hrHi,hrOk⟩:=hr0Spec (Nat.beq nots 0) a b ha hb (Nat.ne_of_lt ab)
      exact y3 (kp0:=false) (kp1:=false) jA hcoutHi hrHi hcoutOk
       (fun q hq hr0 i hi h1 h2=>by
        have:=hrOk q hq hr0 i hi (h1.resolve_left Bool.noConfusion) (h2.resolve_left Bool.noConfusion)
        rw [hsigEq _ i hi q hq] at this;rwa [hne2i])
       rfl (by rw [hne2];rfl) (by omega) (by omega) (by decide) eval zM j6 nd openChild
       (by simpa only [hne2i,htok0] using hk0)
    · have hc : Nat.ble (Nat.add ws.length nots) q8=true:=by
       apply Nat.ble_eq.mpr
       have hfl : zE ws.length opv 1=ws.length - 0 - 1+1:=by unfold zE;rw [hne2];rfl
       rw [hfl,hne2i'] at hfit;change ws.length+nots ≤ q8;omega
      rw [hc] at hk123;dsimp only at hk123
      rw [Bool.and_eq_true] at hk123
      obtain ⟨hrHi,hrOk⟩:=hr1Spec (Nat.beq nots 0) b hb
      exact y3 (kp0:=true) (kp1:=false) jA hcoutHi hrHi hcoutOk
       (fun q hq hr0 i hi _ h2=>by
        have:=hrOk q hq hr0 i hi (h2.resolve_left Bool.noConfusion)
        rw [hsigEq _ i hi q hq] at this;rwa [hne2i])
       rfl (by rw [hne2];rfl) (by omega) (by omega) (by decide) eval zM j6 nd openChild
       (by simpa only [hne2i,htok1] using hk123.1)
    · have hc : Nat.ble (Nat.add ws.length nots) q8=true:=by
       apply Nat.ble_eq.mpr
       have hfl : zE ws.length opv 2=ws.length - 1 - 0+1:=by unfold zE;rw [hne2];rfl
       rw [hfl,hne2i'] at hfit;change ws.length+nots ≤ q8;omega
      rw [hc] at hk123;dsimp only at hk123
      simp only [Bool.and_eq_true] at hk123
      obtain ⟨hrHi,hrOk⟩:=hr1Spec (Nat.beq nots 0) a ha
      exact y3 (kp0:=false) (kp1:=true) jA hcoutHi hrHi hcoutOk
       (fun q hq hr0 i hi h1 _=>by
        have:=hrOk q hq hr0 i hi (h1.resolve_left Bool.noConfusion)
        rw [hsigEq _ i hi q hq] at this;rwa [hne2i])
       rfl (by rw [hne2];rfl) (by omega) (by omega) (by decide) eval zM j6 nd openChild
       (by simpa only [hne2i,htok2] using hk123.2.1)
    · have hc1 : Nat.ble (Nat.add ws.length nots) q8=true:=by
       apply Nat.ble_eq.mpr
       have hfl : zE ws.length opv 3=ws.length - 0 - 0+1:=by unfold zE;rw [hne2];rfl
       rw [hfl,hne2i'] at hfit;change ws.length+nots ≤ q8;omega
      have hc3 : Nat.ble (Nat.add (Nat.add ws.length 1) nots) q8=true:=by
       apply Nat.ble_eq.mpr
       have hfl : zE ws.length opv 3=ws.length - 0 - 0+1:=by unfold zE;rw [hne2];rfl
       rw [hfl,hne2i'] at hfit;change ws.length+1+nots ≤ q8;omega
      rw [hc1] at hk123;dsimp only at hk123
      simp only [Bool.and_eq_true] at hk123
      have hk3:=hk123.2.2
      rw [hc3] at hk3;dsimp only at hk3
      obtain ⟨hcsHi,hcsBit⟩:=k4 (dir:=Nat.beq nots 0) htagsHi
      exact y3 (kp0:=true) (kp1:=true) jA hcoutHi
       (fun k hk=>(hcsHi k hk).1) hcoutOk
       (fun q hq hr0 i hi _ _=>by
        have h1:=(hcsBit q hq).1;rw [h1] at hr0
        by_contra htrue
        have hti : (q6 (Nat.beq nots 0) qp (qn tags i)).testBit q=true:=by
         rw [hsigEq _ i hi q hq];rw [hne2i] at htrue
         cases h : (if Nat.beq nots 0=true then _ else _);exact absurd h htrue;rfl
        have hltI : i < tags.length:=htagsLen.symm ▸ hi
        rw [zo hltI] at hti
        have hge1:=vI (p:=fun t=>(q6 (Nat.beq nots 0) qp t).testBit q) hltI hti
        rw [decide_eq_true hge1] at hr0;exact Bool.noConfusion hr0)
       rfl (by rw [hne2];rfl) (by omega) (by omega) (by decide) eval zM j6 nd openChild
       (by simpa only [hne2i,htok3] using hk3)
   have hopc : op=0 ∨ op=1:=by omega
   rcases hopc with h0 | h1
   · have htag0 : zr sample (Nat.land (ws.getD a 0) (ws.getD b 0))
      (Nat.land (qn tags a).1 (qn tags b).1,Nat.land (qn tags a).2 (qn tags b).2) :=
      jW (op:=0) (x:=(ws.getD a 0,qn tags a)) (y:=(ws.getD b 0,qn tags b)) jA zM (htagsVal a ha) (htagsVal b hb)
     exact handleOp 0 h0 (by decide) _ _ _ rfl htag0 hAnd
   · have htag1 : zr sample (Nat.lor (ws.getD a 0) (ws.getD b 0))
      (Nat.lor (qn tags a).1 (qn tags b).1,Nat.lor (qn tags a).2 (qn tags b).2) :=
      jW (op:=1) (x:=(ws.getD a 0,qn tags a)) (y:=(ws.getD b 0,qn tags b)) jA zM (htagsVal a ha) (htagsVal b hb)
     exact handleOp 1 h1 (by decide) _ _ _ rfl htag1 hOr
noncomputable def js :
  {f : Nat → Bool → Word → Word → Option qw → k6 →
   Nat → zj → (Nat → Option qy) → zt → Nat → yq →
   qc → Nat → List qU → Bool // f=zL}:=by
 refine ⟨?f, ?kf⟩
 case kf =>
  delta zL vS q6
   qZ vR qn zz uH qS zn kq
  beta_reduce
  exact rfl
noncomputable def yP:=js.1
noncomputable def qO (maxK : Nat) (is24 q4 : Bool) (mask goal : Word)
  (chart : Option qw) (bounds : List q2) (hints : Option (Nat → Nat))
  (qQ : Nat) (q3 : zj)
  (states : Nat → Option qc) (qx : Nat → Option qy)
  (z8 : zt) (zR : z2) (sampleLen : Nat)
  (tags : Nat → List qU) (i : Nat) : Bool :=
 @Option.rec qc (fun _=>Bool) false
  (fun st =>
   let (q8,nots,ws,history):=st
   ye ws fun forced =>
    qS (q1q mask forced)
     (zR (Nat.add i 1) fun bucket =>
      @Option.rec (Nat → Nat) (fun _=>Bool)
       (yP maxK is24 mask goal chart (qk q4 bounds)
        qQ q3 qx z8 (Nat.add i 1) bucket
        (q8,nots,forced,history) sampleLen (tags i))
       (fun hfn =>
        q7 (hfn i) fun code =>
         vl bounds 10 code fun vB =>
          yP maxK is24 mask goal chart (qk q4 vB)
           qQ q3 qx z8 (Nat.add i 1) bucket
           (q8,nots,forced,history) sampleLen (tags i))
       hints))
  (states i)
noncomputable def qT (maxK : Nat) (is24 : Bool) (mask goal : Word) (chart : Option qw)
  (cut : k6) (witnesses : List zW) (qQ : Nat) (q3 : zj)
  (qx : Nat → Option qy) (z8 : zt) (zR : z2)
  (stock : List Word) (q8 q9 : Nat) : Bool :=
 zR 0 fun bucket =>
  qE 0 (2 ^ stock.length) fun q5 =>
   let state:=zO stock q8 q9 q5
   !u9 witnesses state.2.2.1||jq maxK is24 mask goal chart cut state ||
    jR qQ q3 qx z8 0 bucket q5 state
theorem q76 {maxK : Nat} {is24 q4 : Bool} {mask goal : Word}
 {qV q8 q9 qQ : Nat} {stock : List Word} {chart : Option qw}
 {bounds : List q2} {hints : Option (Nat → Nat)} {q3 : zj} {z8 : zt} {zR : z2}
 {sample : qH} {root : List qb}
 (jA : j3 mask goal sample)
 (hroot : vK sample stock root)
 (uC : is24=true → mask=16777215 ∧ goal=4095)
 (kH : qm (qI qV) mask)
 (vh : qm mask goal)
 (w1 : ∀ c,chart=some c → jD goal c)
 (cutSound : ∀ vB : List q2,(∀ b ∈ vB,b ∈ bounds) →
  ∀ s,s.2.1 ≤ 1 → zZ mask goal s → qk q4 vB s=false)
 (q6k : qP mask goal qV z8)
 (q36 : z1 zR)
 (verified : qE 0 qQ (qO maxK is24 q4 mask goal chart bounds hints qQ q3
  (zx mask stock q8 q9 q3) (qr mask stock q8 q9 q3)
  z8 zR sample.2 (qG mask sample.2 root q8 q3))=true) :
 ∀ cap i saved,i < qQ → jr mask stock q8 q9 q3 i=some saved →
  saved.1=cap → saved.2.1 ≤ 1 → ∀ k,k ≤ cap → ¬ qf mask goal k saved.2.1 saved.2.2.1.toFinset:=by
 intro cap
 induction cap using Nat.strong_induction_on with
 | ind cap ih =>
  intro i s iBound stateEq sFuel sNots k kBound y1
  rcases s with ⟨yX,nots,words,history⟩
  let s : qc:=(yX,nots,words,history)
  have checked:=zN verified (Nat.zero_le i) (by simpa using iBound)
  change qO maxK is24 q4 mask goal chart bounds hints qQ q3
   (zx mask stock q8 q9 q3) (qr mask stock q8 q9 q3)
   z8 zR sample.2 (qG mask sample.2 root q8 q3) i=true at checked
  unfold qO at checked
  rw [q75,stateEq] at checked
  dsimp only at checked
  rw [zV,qR,Bool.and_eq_true] at checked
  obtain ⟨nd,zM⟩:=q1L checked.1
  obtain ⟨bucket,ok⟩:=q36 (Nat.add i 1) _ checked.2
  have hact : ∃ vB : List q2,(∀ x ∈ vB,x ∈ bounds) ∧
   zL maxK is24 mask goal chart (qk q4 vB)
    qQ q3 (qr mask stock q8 q9 q3) z8 (Nat.add i 1) bucket
    (yX,nots,words,history) sample.2 (qG mask sample.2 root q8 q3 i)=true:=by
   cases hints with
   | none =>
    rw [show yP=zL from js.2] at ok
    exact ⟨bounds,fun _ h=>h,ok⟩
   | some hfn =>
    dsimp only at ok
    rw [ql,q2p,show yP=zL from js.2] at ok
    exact ⟨j0 bounds 10 (hfn i),fun _ hx=>q1M hx,ok⟩
  obtain ⟨vB,hsubA,ok⟩:=hact
  have j6 : zZ mask goal s:=⟨nd,k,sFuel ▸ kBound,y1⟩
  have scanned:=ok
  unfold zL at scanned
  simp only [ql,qR,uP,yd,za,Bool.and_eq_true] at scanned
  have hwidth : words.length ≤ 64:=Nat.ble_eq.mp scanned.1
  have habsent : !(Nat.beq nots 0&&words.contains goal)=true:=scanned.2.1
  rcases q5b hwidth j6 with ⟨hn0,hit⟩ | ⟨child,possible,cv,cnle⟩
  · simp only [s] at hn0 hit
    have : (Nat.beq nots 0&&words.contains goal)=true:=by
     rw [hn0,Nat.beq_refl,List.contains_iff_mem.mpr hit];rfl
    rw [this] at habsent;exact Bool.noConfusion habsent
  obtain ⟨a,b,op,keep,ha,legal,eval⟩:=possible
  have cn1 : child.2.1 ≤ 1:=Nat.le_trans cnle sNots
  obtain ⟨htLen,htVal⟩:=q18 jA vh hroot stateEq
  have r:=q7P jA htLen htVal ok ha legal eval vh cv nd
   (q1s uC vh w1 cv (cutSound vB hsubA _ cn1 cv))
  have ⟨less,_,cm⟩:=q3U eval zM
  have below : child.1 < cap:=sFuel ▸ less
  obtain ⟨_,k',fits,clive⟩:=cv
  obtain ⟨j,dest,bound,restore,fuelEq,notsEq,tail⟩ :=
   q0K (fun d hf=>q1a stateEq eval hf) kH q6k cm r clive
  exact ih child.1 below j dest bound restore fuelEq (notsEq.symm ▸ cn1) k' fits tail
theorem q2x {maxK : Nat} {is24 q4 : Bool}
 {mask goal : Word} {qV q8 q9 qQ : Nat}
 {stock : List Word} {chart : Option qw}
 {q3 : zj} {z8 : zt} {zR : z2} {sample : qH}
 {root : List qb}
 {bounds : List q2} {hints : Option (Nat → Nat)} {witnesses : List zW}
 (jA : j3 mask goal sample)
 (hroot : vK sample stock root)
 (uC : is24=true → mask=16777215 ∧ goal=4095)
 (q4T : q9 ≤ 1)
 (kH : qm (qI qV) mask)
 (vh : qm mask goal)
 (w1 : ∀ c,chart=some c → jD goal c)
 (q6k : qP mask goal qV z8)
 (q36 : z1 zR)
 (q7m : ∀ w ∈ stock,qm mask w) (stockNd : stock.Nodup)
 (q9v : witnesses.all (wO mask goal stock)=true)
 (q63 : qu bounds)
 (q20 : ∀ b ∈ bounds,mask&&&b.1=b.1)
 (q41 : ∀ b ∈ bounds, ∀ w ∈ b.2.1,qm b.1 w)
 (boundsGoal : ∀ b ∈ bounds,(((goal&&&b.1)==b.2.2.2.2)&&(b.2.2.2.2 != 0)&&(b.2.2.2.2 != b.1))=true)
 (q2D : qT maxK is24 mask goal chart (qk q4 bounds) witnesses
  qQ q3 (qr mask stock q8 q9 q3) z8 zR stock q8 q9=true)
 (q2P : qE 0 qQ (qO maxK is24 q4 mask goal chart
  bounds hints qQ q3
  (zx mask stock q8 q9 q3) (qr mask stock q8 q9 q3)
  z8 zR sample.2 (qG mask sample.2 root q8 q3))=true) :
 qo mask stock goal q9 (q8+1):=by
 intro k S y1 hS
 by_contra! small
 have sub : ∀ w ∈ S,w ∈ stock:=by
  intro w hw;have hp:=jK y1 w hw
  exact ((hS w hw).resolve_left hp.1).resolve_left hp.2
 have included : S ⊆ stock.toFinset:=fun w hw=>List.mem_toFinset.mpr (sub w hw)
 obtain ⟨q5,tokenBound,eq⟩:=q9n stock S
 rw [Finset.inter_eq_right.mpr included] at eq
 let state:=zO stock q8 q9 q5
 have eq' : state.2.2.1.toFinset=S:=eq
 have v : zZ mask goal state:=by
  refine ⟨(wT stock q5).nodup stockNd,k, ?_, ?_⟩
  · change k ≤ q8;omega
  · rwa [eq']
 have cutOpen (vB : List q2) (hsub : ∀ b ∈ vB,b ∈ bounds)
  (s : qc) (hs : s.2.1 ≤ 1) (h : zZ mask goal s) :
  qk q4 vB s=false:=by
  cases hc : qk q4 vB s
  · rfl
  · exfalso
    have h1:=wl (fun b hb=>boundsGoal b (hsub b hb)) hc
    have h2:=q0h (q4:=q4)
     (fun b hb=>q63 b (hsub b hb)) (fun b hb=>q20 b (hsub b hb))
     (fun b hb=>q41 b (hsub b hb)) hs h
    rw [h1] at h2;exact Bool.noConfusion h2
 have openRoot:=q1s (maxK:=maxK) uC vh w1 v (cutOpen bounds (fun _ h=>h) _ q4T v)
 have allowed : u9 witnesses state.2.2.1=true:=by
  apply List.all_eq_true.mpr;intro kt mem
  apply List.contains_iff_mem.mpr;rw [← List.mem_toFinset,eq']
  exact q2y (List.all_eq_true.mp q9v kt mem) sub y1
 obtain ⟨bucket,rootB⟩:=q36 0 _ q2D
 have checked:=zN rootB (Nat.zero_le q5) (by simpa using tokenBound)
 change (!u9 witnesses state.2.2.1 ||
  jq maxK is24 mask goal chart (qk q4 bounds) state ||
  jR qQ q3 (qr mask stock q8 q9 q3) z8 0 bucket q5 state)=true at checked
 simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
 have finish:=q76 jA hroot uC kH vh w1 cutOpen q6k q36 q2P
 have fits : k ≤ q8:=by omega
 have still : qf mask goal k q9 state.2.2.1.toFinset:=by rwa [eq']
 have stateMask : ∀ w ∈ state.2.2.1,qm mask w:=fun w hw =>
  q7m _ ((wT stock q5).subset hw)
 obtain ⟨i,s,hi,restore,cap,notsEq,plan⟩ :=
  q0K (fun d hf=>q1P tokenBound hf) kH q6k stateMask checked still
 exact finish q8 i s hi restore cap (notsEq.symm ▸ q4T) k fits plan
theorem wb {rows m : Nat} (source : Fin m → Fin rows)
  {m1 m2 : Word} {s1 s2 : List Word} {g1 g2 min0 min1 : Nat}
  (yV : decide ((m1&&&qI rows=m1) ∧
   (∀ r : Fin rows,m1.testBit r.val=true → ∃ i : Fin m,source i=r) ∧
   y5 source m1=m2 ∧ y5 source g1=g2 ∧
   s1.all (fun w=>w&&&m1==w)=true ∧
   s1.all (fun w=>qC m2 s2 (y5 source w))=true)=true)
  (h0 : qo m2 s2 g2 0 min0) (h1 : qo m2 s2 g2 1 min1) :
  qo m1 s1 g1 0 min0 ∧ qo m1 s1 g1 1 min1 :=
 ⟨vU source yV h0,vU source yV h1⟩
def qe (nvars : Nat) (kV row : Nat) : Nat :=
 Nat.rec 0
  (fun i next=>(if row.testBit i then 1<<<((kV>>>(3*i))&&&7) else 0)|||next)
  nvars
def uY {qV : Nat} (mask goal : Word) (kt : q5a qV) : Bool :=
 let (move,zi,inverse):=kt
 Nat.beq (Nat.land mask (qI qV)) mask &&
 Nat.beq (Nat.land goal mask) goal &&
 Nat.beq (vQ move mask) mask &&
 Nat.beq (vQ move goal) goal &&
 qE 0 qV (fun i =>
  if h : i < qV then
   let fi : Fin qV:=⟨i,h⟩
   Nat.beq (inverse (zi fi)).val i &&
   Nat.beq (zi (inverse fi)).val i &&
   (!mask.testBit i||Nat.beq (vQ move (Nat.shiftLeft 1 i)) (Nat.shiftLeft 1 (inverse fi).val))
  else true)
theorem qs {qV : Nat} {mask goal : Word}
 {z8 : zt} {sel inv : Nat → Fin qV → Fin qV} {bound : Nat}
 (hhi : ∀ a,bound ≤ a → z8 a=none)
 (hok : qE 0 bound (fun a =>
  match z8 a with
  | none=>true
  | some m=>uY mask goal (m,sel a,inv a))=true) :
 qP mask goal qV z8:=by
 intro a m hm
 by_cases hlt : a < bound
 · have hc:=zN hok (Nat.zero_le a) (by simpa using hlt)
   rw [hm] at hc
   simp only [uY,Bool.and_eq_true,Nat.beq_eq] at hc
   obtain ⟨⟨⟨⟨bm,gm⟩,mm⟩,mg⟩,hloop⟩:=hc
   rw [q0J] at mm mg
   have left : ∀ i : Fin qV,inv a (sel a i)=i:=by
    intro i
    have hi:=zN hloop (Nat.zero_le i.val) (by simpa using i.isLt)
    simp only [i.isLt, ↓reduceDIte,Bool.and_eq_true,Nat.beq_eq] at hi
    exact Fin.ext hi.1.1
   have right : ∀ i : Fin qV,sel a (inv a i)=i:=by
    intro i
    have hi:=zN hloop (Nat.zero_le i.val) (by simpa using i.isLt)
    simp only [i.isLt, ↓reduceDIte,Bool.and_eq_true,Nat.beq_eq] at hi
    exact Fin.ext hi.1.2
   have basis : ∀ i : Fin qV,mask.testBit i.val=true → yG m (2 ^ i.val)=2 ^ (inv a i).val:=by
    intro i hbi
    have hi:=zN hloop (Nat.zero_le i.val) (by simpa using i.isLt)
    simp only [i.isLt, ↓reduceDIte,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',hbi,
     Bool.false_eq_true,false_or,Nat.beq_eq] at hi
    simpa [q0J,Nat.shiftLeft_eq] using hi.2
   exact ⟨sel a,q3S left right bm gm basis mm mg⟩
 · rw [hhi a (Nat.le_of_not_lt hlt)] at hm;cases hm
def qaj : qg:=([(0x99,0),(0x22,1)],[(0x44,1)])
def qai : qg:=([(0xa5,0),(0xa,3)],[(0x50,3)])
def q9A : qg:=([(0xc3,0),(0xc,2)],[(0x30,2)])
def q1C : qg:=([(0x9999,0),(0x2222,1)],[(0x4444,1)])
def q0p : qg:=([(0xa5a5,0),(0xa0a,3)],[(0x5050,3)])
def q1B : qg:=([(0xaa55,0),(0xaa,7)],[(0x5500,7)])
def wu : qg:=([(0xc3c3,0),(0xc0c,2)],[(0x3030,2)])
def w4 : qg:=([(0xcc33,0),(0xcc,6)],[(0x3300,6)])
def vY : qg:=([(0xf00f,0),(0xf0,4)],[(0xf00,4)])
def q9C : qg:=([(0x99999999,0),(0x22222222,1)],[(0x44444444,1)])
def kT : qg:=([(0xa5a5a5a5,0),(0xa0a0a0a,3)],[(0x50505050,3)])
def q8b : qg:=([(0xaa55aa55,0),(0xaa00aa,7)],[(0x55005500,7)])
def q9B : qg:=([(0xaaaa5555,0),(0xaaaa,15)],[(0x55550000,15)])
def q1A : qg:=([(0xc3c3c3c3,0),(0xc0c0c0c,2)],[(0x30303030,2)])
def w3 : qg:=([(0xcc33cc33,0),(0xcc00cc,6)],[(0x33003300,6)])
def un : qg:=([(0xcccc3333,0),(0xcccc,14)],[(0x33330000,14)])
def q8a : qg:=([(0xf00ff00f,0),(0xf000f0,4)],[(0xf000f00,4)])
def q89 : qg:=([(0xf0f00f0f,0),(0xf0f0,12)],[(0xf0f0000,12)])
def yQ : qg:=([(0xff0000ff,0),(0xff00,8)],[(0xff0000,8)])
def q6F : qg:=([(0x9999999999999999,0),(0x2222222222222222,1)],[(0x4444444444444444,1)])
def q6E : qg:=([(0xa5a5a5a5a5a5a5a5,0),(0xa0a0a0a0a0a0a0a,3)],[(0x5050505050505050,3)])
def q0o : qg:=([(0xaa55aa55aa55aa55,0),(0xaa00aa00aa00aa,7)],[(0x5500550055005500,7)])
def q6D : qg:=([(0xaaaa5555aaaa5555,0),(0xaaaa0000aaaa,15)],[(0x5555000055550000,15)])
def q0n : qg:=([(0xc3c3c3c3c3c3c3c3,0),(0xc0c0c0c0c0c0c0c,2)],[(0x3030303030303030,2)])
def q6C : qg:=([(0xcc33cc33cc33cc33,0),(0xcc00cc00cc00cc,6)],[(0x3300330033003300,6)])
def q2C : qg:=([(0xcccc3333cccc3333,0),(0xcccc0000cccc,14)],[(0x3333000033330000,14)])
def q2B : qg:=([(0xf00ff00ff00ff00f,0),(0xf000f000f000f0,4)],[(0xf000f000f000f00,4)])
def q2A : qg:=([(0xf0f00f0ff0f00f0f,0),(0xf0f00000f0f0,12)],[(0xf0f00000f0f0000,12)])
def w2 : qg:=([(0xff0000ffff0000ff,0),(0xff000000ff00,8)],[(0xff000000ff0000,8)])
def q6B : qg:=([(0xffff00000000ffff,0),(0xffff0000,16)],[(0xffff00000000,16)])
def q47 : qg:=([(0x99999999999999999999999999999999,0),(0x22222222222222222222222222222222,1)],[(0x44444444444444444444444444444444,1)])
def q46 : qg:=([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,0),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0x50505050505050505050505050505050,3)])
def q45 : qg:=([(0xaa55aa55aa55aa55aa55aa55aa55aa55,0),(0xaa00aa00aa00aa00aa00aa00aa00aa,7)],[(0x55005500550055005500550055005500,7)])
def q44 : qg:=([(0xaaaa5555aaaa5555aaaa5555aaaa5555,0),(0xaaaa0000aaaa0000aaaa0000aaaa,15)],[(0x55550000555500005555000055550000,15)])
def q43 : qg:=([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,0),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0x30303030303030303030303030303030,2)])
def q42 : qg:=([(0xcc33cc33cc33cc33cc33cc33cc33cc33,0),(0xcc00cc00cc00cc00cc00cc00cc00cc,6)],[(0x33003300330033003300330033003300,6)])
def q0V : qg:=([(0xcccc3333cccc3333cccc3333cccc3333,0),(0xcccc0000cccc0000cccc0000cccc,14)],[(0x33330000333300003333000033330000,14)])
def q0U : qg:=([(0xf00ff00ff00ff00ff00ff00ff00ff00f,0),(0xf000f000f000f000f000f000f000f0,4)],[(0xf000f000f000f000f000f000f000f00,4)])
def q0T : qg:=([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,0),(0xf0f00000f0f00000f0f00000f0f0,12)],[(0xf0f00000f0f00000f0f00000f0f0000,12)])
def vD : qg:=([(0xff0000ffff0000ffff0000ffff0000ff,0),(0xff000000ff000000ff000000ff00,8)],[(0xff000000ff000000ff000000ff0000,8)])
def vC : qg:=([(0xffffffff0000000000000000ffffffff,0),(0xffffffff00000000,32)],[(0xffffffff0000000000000000,32)])
def qa (w sub : Nat) [NeZero w] (ax : List Nat) (ones : Nat) (i : Fin sub) : Fin w:=Fin.ofNat w (ones|||q7p ax 0 i.val)
def EL (b : q2) (a c : Nat):=qo b.1 b.2.1 b.2.2.2.2 0 a ∧ qo b.1 b.2.1 b.2.2.2.2 1 c
theorem qh {rows m : Nat} (src : Fin m → Fin rows) {b : q2} {m2 g2 l0 l1 : Nat} {s2 : List Word} (h0 : qo m2 s2 g2 0 l0) (h1 : qo m2 s2 g2 1 l1) (hc : decide ((b.1&&&qI rows=b.1) ∧ (∀ r : Fin rows,b.1.testBit r.val=true → ∃ i : Fin m,src i=r) ∧ y5 src b.1=m2 ∧ y5 src b.2.2.2.2=g2 ∧ b.2.1.all (fun w=>w&&&b.1==w)=true ∧ b.2.1.all (fun w=>qC m2 s2 (y5 src w))=true)=true) : EL b l0 l1:=wb src hc h0 h1
theorem zm {maxK : Nat} {q4 : Bool} {mask goal : Word} {qV q8 q9 qQ : Nat} {stock : List Word} {root : List qb} {chart : Option qw} {q3 : zj} {z8 : zt} {zR : z2} {sample : qH} {bounds : List q2} {hints : Option (Nat → Nat)} {witnesses : List zW} (q6k : qP mask goal qV z8) (q36 : z1 zR) (q63 : qu bounds) (q2D : qT maxK false mask goal chart (qk q4 bounds) witnesses qQ q3 (qr mask stock q8 q9 q3) z8 zR stock q8 q9=true) (q2P : qE 0 qQ (qO maxK false q4 mask goal chart bounds hints qQ q3 (zx mask stock q8 q9 q3) (qr mask stock q8 q9 q3) z8 zR sample.2 (qG mask sample.2 root q8 q3))=true) (h0 : decide (q9 ≤ 1 ∧ (mask&&&qI qV=mask) ∧ (goal&&&mask=goal) ∧ stock.Nodup)=true) (jA : wd mask goal sample=true) (hroot : kG sample stock root=true) (hch : q54 goal chart=true) (hsm : stock.all (fun w=>w&&&mask==w)=true) (hess : witnesses.all (wO mask goal stock)=true) (hbnd : bounds.all (fun b=>((mask&&&b.1==b.1)&&b.2.1.all (fun w=>w&&&b.1==w))&&(((goal&&&b.1)==b.2.2.2.2)&&(b.2.2.2.2 != 0)&&(b.2.2.2.2 != b.1)))=true) : qo mask stock goal q9 (q8+1):=by
 obtain ⟨hin,hmb,hgm,hnd⟩:=of_decide_eq_true h0
 exact q2x (q1z jA) (q0q hroot) (fun h=>Bool.noConfusion h) hin hmb hgm (q7d hch) q6k q36 (um hsm) hnd hess q63 (fun b hb=>beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hbnd b hb)).1).1) (fun b hb=>um (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hbnd b hb)).1).2) (fun b hb=>(Bool.and_eq_true_iff.mp (List.all_eq_true.mp hbnd b hb)).2) q2D q2P
theorem zI : qo 0xff [0xaa,0xcc,0xf0] 0xe8 0 4:=zm (maxK:=2) (q4:=false) (qV:=8) (qQ:=0) (root:=([0xaa,0xcc,0xf0] : List Word).map (fun w=>(w,0,0))) (chart:=some ⟨[3,5,6,3,3,3,3,3,3,3,3,3,1,2,4,1,1,1,1,1,1,1,1,1],rfl⟩) (q3:=fun _=>(0,0)) (z8:=fun _=>none) (zR:=fun _ k=>k (fun _=>none)) (sample:=(0,0)) (bounds:=[]) (hints:=none) (witnesses:=[(0xaa,3,2),(0xcc,3,1),(0xf0,5,1)]) (fun _ _ h=>by cases h) (fun _ _ h=>⟨fun _=>none,h⟩) (fun _ h=>False.elim (List.not_mem_nil h)) (by decide +kernel) rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
def jN : Word:=0xff
def uU : Word:=0xe8
def ve : List Word:=[0xaa,0xcc,0xf0]
def q2l : Option qw:=some ⟨[3,5,6,3,3,3,3,3,3,3,3,3,1,2,4,1,1,1,1,1,1,1,1,1],rfl⟩
def q8m : List zW:=[(0xaa,3,2),(0xcc,3,1),(0xf0,5,1)]
def q5E : qH:=(0x201804060201402050100c0203,6)
def vM : zj:=fun i=>zf 1 4 0xe i
def uB : z2 :=
 qv 0x1 0x7 2 0x3 1 0x1 5 0x1f 3 0x7 0x1 4 1
theorem q15 : z1 uB :=
 qt 0x1 0x7 2 0x3 1 0x1 5 0x1f 3 0x7 0x1 4 1
def q39 : List qb:=zk ve 0x3cccf 0x28485 6
noncomputable def q7A:=qG jN 6 q39 4 vM
noncomputable def q5D:=zx jN ve 4 1 vM
noncomputable def q2k:=qr jN ve 4 1 vM
def vf (a : Nat) : Option z0 :=
 if Nat.blt a 6 then
  match a with
  |1=>some [q9A]
  |2=>some [qaj]
  |3=>some [qai,q9A]
  |4=>some [qaj,q9A]
  |5=>some [qai]
  | _=>none
 else none
theorem q6Z : qP jN uU 8 vf :=
 qs
  (sel:=fun a i=>Fin.ofNat 8 (qe 3 (z3 0x141121204a000 9 a) i.val))
  (inv:=fun a i=>Fin.ofNat 8 (qe 3 (z3 0x144208a04a000 9 a) i.val))
  (bound:=6)
  (by intro a ha;unfold vf;rw [show Nat.blt a 6=false from by cases h : Nat.blt a 6;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def q0F : List q2:=[]
theorem q6X : qu q0F:=show qu [] from fun _ h=>False.elim (List.not_mem_nil h)
noncomputable def q6Y:=qO 2 false true jN uU q2l q0F none 1 vM q5D q2k vf uB 6 q7A
theorem q6W : qT 2 false jN uU q2l (qk true q0F) q8m 1 vM q2k vf uB ve 4 1=true:=by decide +kernel
theorem q9q : qE 0 1 q6Y=true:=by decide +kernel
theorem zH : qo jN ve uU 1 5 :=
 zm (root:=q39) (sample:=q5E) (hints:=none) q6Z q15 q6X q6W q9q
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem km : qo 0xffff [0xaaaa,0xcccc,0xf0f0,0xff00] 0xfee8 0 6:=zm (maxK:=2) (q4:=false) (qV:=16) (qQ:=0) (root:=([0xaaaa,0xcccc,0xf0f0,0xff00] : List Word).map (fun w=>(w,0,0))) (chart:=some ⟨[3,5,6,9,10,12,3,3,3,3,3,3,1,2,4,8,1,1,1,1,1,1,1,1],rfl⟩) (q3:=fun _=>(0,0)) (z8:=fun _=>none) (zR:=fun _ k=>k (fun _=>none)) (sample:=(0,0)) (bounds:=[]) (hints:=none) (witnesses:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,5,1),(0xff00,9,1)]) (fun _ _ h=>by cases h) (fun _ _ h=>⟨fun _=>none,h⟩) (fun _ h=>False.elim (List.not_mem_nil h)) (by decide +kernel) rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
def j9 : Word:=0xffff
def ug : Word:=0xfee8
def kk : List Word:=[0xaaaa,0xcccc,0xf0f0,0xff00]
def q1m : Option qw:=some ⟨[3,5,6,9,10,12,3,3,3,3,3,3,1,2,4,8,1,1,1,1,1,1,1,1],rfl⟩
def q7z : List zW:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,5,1),(0xff00,9,1)]
def q4S : qH:=(0x100a0200c100c04024040a020180406020300403020140203008240205,13)
def vd : zj:=fun i=>zf 3 13 0x1098e20a102640f2078 i
def u4 : z2 :=
 qv 0x2451180b4c3801 0xd0500a07014080200c04638160d00c144162b81c4ed4cada593b131f61636340ac64138901f110360404c04078000f 9 0x1ff 4 0xf 19 0x7ffff 11 0x7ff 0x7 14 4
theorem q0E : z1 u4 :=
 qt 0x2451180b4c3801 0xd0500a07014080200c04638160d00c144162b81c4ed4cada593b131f61636340ac64138901f110360404c04078000f 9 0x1ff 4 0xf 19 0x7ffff 11 0x7ff 0x7 14 4
def q2j : List qb:=zk kk 0xb9113a73a8a1f 0xb0022a02a0007 13
noncomputable def q6V:=qG j9 13 q2j 6 vd
noncomputable def q4R:=zx j9 kk 6 1 vd
noncomputable def q1l:=qr j9 kk 6 1 vd
def kB (a : Nat) : Option z0 :=
 if Nat.blt a 24 then
  match a with
  |1=>some [vY]
  |2=>some [wu]
  |3=>some [w4,vY]
  |4=>some [wu,vY]
  |5=>some [w4]
  |6=>some [q1C]
  |7=>some [q1C,vY]
  |8=>some [q0p,wu]
  |9=>some [q1B,w4,vY]
  |10=>some [q0p,wu,vY]
  |11=>some [q1B,w4]
  |12=>some [q1C,wu]
  |13=>some [q1C,w4,vY]
  |14=>some [q0p]
  |15=>some [q1B,vY]
  |16=>some [q0p,w4]
  |17=>some [q1B,wu,vY]
  |18=>some [q1C,wu,vY]
  |19=>some [q1C,w4]
  |20=>some [q0p,vY]
  |21=>some [q1B]
  |22=>some [q0p,w4,vY]
  |23=>some [q1B,wu]
  | _=>none
 else none
theorem q5C : qP j9 ug 16 kB :=
 qs
  (sel:=fun a i=>Fin.ofNat 16 (qe 4 (z3 0x5305a08b0ca0990d121321a40b60a4196112832c24436424c16812982d04586504c8000 12 a) i.val))
  (inv:=fun a i=>Fin.ofNat 16 (qe 4 (z3 0x5321308b40b28344305a21a0ca60a2c26420994190d16114c16812984582d06504c8000 12 a) i.val))
  (bound:=24)
  (by intro a ha;unfold kB;rw [show Nat.blt a 24=false from by cases h : Nat.blt a 24;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def wI : List q2:=[]
theorem q5A : qu wI:=show qu [] from fun _ h=>False.elim (List.not_mem_nil h)
noncomputable def q5B:=qO 2 false true j9 ug q1m wI none 6 vd q4R q1l kB u4 13 q6V
theorem q5z : qT 2 false j9 ug q1m (qk true wI) q7z 6 vd q1l kB u4 kk 6 1=true:=by decide +kernel
theorem q8l : qE 0 6 q5B=true:=by decide +kernel
theorem kl : qo j9 kk ug 1 7 :=
 zm (root:=q2j) (sample:=q4S) (hints:=none) q5C q0E q5A q5z q8l
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem z7 : qo 0xffff [0xaaaa,0xcccc,0xf0f0,0xff00] 0xfec8 0 5:=zm (maxK:=2) (q4:=false) (qV:=16) (qQ:=0) (root:=([0xaaaa,0xcccc,0xf0f0,0xff00] : List Word).map (fun w=>(w,0,0))) (chart:=some ⟨[3,6,9,10,12,3,3,3,3,3,3,3,2,5,8,2,2,2,2,2,2,2,2,2],rfl⟩) (q3:=fun _=>(0,0)) (z8:=fun _=>none) (zR:=fun _ k=>k (fun _=>none)) (sample:=(0,0)) (bounds:=[]) (hints:=none) (witnesses:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,6,2),(0xff00,9,1)]) (fun _ _ h=>by cases h) (fun _ _ h=>⟨fun _=>none,h⟩) (fun _ h=>False.elim (List.not_mem_nil h)) (by decide +kernel) rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
def yC : Word:=0xffff
def v5 : Word:=0xfec8
def jk : List Word:=[0xaaaa,0xcccc,0xf0f0,0xff00]
def q04 : Option qw:=some ⟨[3,6,9,10,12,3,3,3,3,3,3,3,2,5,8,2,2,2,2,2,2,2,2,2],rfl⟩
def q5t : List zW:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,6,2),(0xff00,9,1)]
def q2O : qH:=(0x206020300a0302824100c02018100a040240406010280403008240203,13)
def jJ : zj:=fun i=>zf 1 6 0x3be5e i
def v6 : z2 :=
 qv 0xe1 0xaf174780f 5 0x1f 2 0x3 9 0x1ff 5 0x1f 0x3 7 2
theorem wD : z1 v6 :=
 qt 0xe1 0xaf174780f 5 0x1f 2 0x3 9 0x1ff 5 0x1f 0x3 7 2
def q0y : List qb:=zk jk 0x5b566429ba627 0xb03a00039603 13
noncomputable def q4L:=qG yC 13 q0y 5 jJ
noncomputable def q2N:=zx yC jk 5 1 jJ
noncomputable def q03:=qr yC jk 5 1 jJ
def jx (a : Nat) : Option z0 :=
 if Nat.blt a 4 then
  match a with
  |1=>some [w4]
  |2=>some [q0p]
  |3=>some [q0p,w4]
  | _=>none
 else none
theorem q3C : qP yC v5 16 jx :=
 qs
  (sel:=fun a i=>Fin.ofNat 16 (qe 4 (z3 0x21a60a298000 12 a) i.val))
  (inv:=fun a i=>Fin.ofNat 16 (qe 4 (z3 0x21a60a298000 12 a) i.val))
  (bound:=4)
  (by intro a ha;unfold jx;rw [show Nat.blt a 4=false from by cases h : Nat.blt a 4;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def uw : List q2:=[]
theorem q3A : qu uw:=show qu [] from fun _ h=>False.elim (List.not_mem_nil h)
noncomputable def q3B:=qO 2 false true yC v5 q04 uw none 3 jJ q2N q03 jx v6 13 q4L
theorem q3z : qT 2 false yC v5 q04 (qk true uw) q5t 3 jJ q03 jx v6 jk 5 1=true:=by decide +kernel
theorem q6Q : qE 0 3 q3B=true:=by decide +kernel
theorem z6 : qo yC jk v5 1 6 :=
 zm (root:=q0y) (sample:=q2O) (hints:=none) q3C wD q3A q3z q6Q
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem zT : qo 0xffff [0xaaaa,0xcccc,0xf0f0,0xff00] 0xfe88 0 5:=zm (maxK:=2) (q4:=false) (qV:=16) (qQ:=0) (root:=([0xaaaa,0xcccc,0xf0f0,0xff00] : List Word).map (fun w=>(w,0,0))) (chart:=some ⟨[3,9,10,12,3,3,3,3,3,3,3,3,5,6,8,5,5,5,5,5,5,5,5,5],rfl⟩) (q3:=fun _=>(0,0)) (z8:=fun _=>none) (zR:=fun _ k=>k (fun _=>none)) (sample:=(0,0)) (bounds:=[]) (hints:=none) (witnesses:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,12,8),(0xff00,9,1)]) (fun _ _ h=>by cases h) (fun _ _ h=>⟨fun _=>none,h⟩) (fun _ h=>False.elim (List.not_mem_nil h)) (by decide +kernel) rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
def yR : Word:=0xffff
def vE : Word:=0xfe88
def jE : List Word:=[0xaaaa,0xcccc,0xf0f0,0xff00]
def q0s : Option qw:=some ⟨[3,9,10,12,3,3,3,3,3,3,3,3,5,6,8,5,5,5,5,5,5,5,5,5],rfl⟩
def q6K : List zW:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,12,8),(0xff00,9,1)]
def q3i : qH:=(0xa0302824080c0281c0c030301c100a04024100c010280403008240203,13)
def kg : zj:=fun i=>zf 3 14 0xe4c4c40e9c424078 i
def vv : z2 :=
 qv 0x2a000301 0x18c7100e1e261c434c7480e800f 6 0x3f 3 0x7 15 0x7fff 11 0x7ff 0x7 14 3
theorem q0e : z1 vv :=
 qt 0x2a000301 0x18c7100e1e261c434c7480e800f 6 0x3f 3 0x7 15 0x7fff 11 0x7ff 0x7 14 3
def q1i : List qb:=zk jE 0x63d1a4279bba7 0x387e00319a03 13
noncomputable def q5k:=qG yR 13 q1i 5 kg
noncomputable def q3h:=zx yR jE 5 1 kg
noncomputable def q0r:=qr yR jE 5 1 kg
def jX (a : Nat) : Option z0 :=
 if Nat.blt a 2 then
  match a with
  |1=>some [q1C]
  | _=>none
 else none
theorem q4u : qP yR vE 16 jX :=
 qs
  (sel:=fun a i=>Fin.ofNat 16 (qe 4 (z3 0x681000 12 a) i.val))
  (inv:=fun a i=>Fin.ofNat 16 (qe 4 (z3 0x681000 12 a) i.val))
  (bound:=2)
  (by intro a ha;unfold jX;rw [show Nat.blt a 2=false from by cases h : Nat.blt a 2;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def w6 : List q2:=[]
theorem q4s : qu w6:=show qu [] from fun _ h=>False.elim (List.not_mem_nil h)
noncomputable def q4t:=qO 2 false true yR vE q0s w6 none 5 kg q3h q0r jX vv 13 q5k
theorem q4r : qT 2 false yR vE q0s (qk true w6) q6K 5 kg q0r jX vv jE 5 1=true:=by decide +kernel
theorem q7q : qE 0 5 q4t=true:=by decide +kernel
theorem zS : qo yR jE vE 1 6 :=
 zm (root:=q1i) (sample:=q3i) (hints:=none) q4u q0e q4s q4r q7q
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem kj : qo 0xffff [0xaaaa,0xcccc,0xf0f0,0xff00] 0xf8c8 0 4:=zm (maxK:=2) (q4:=false) (qV:=16) (qQ:=0) (root:=([0xaaaa,0xcccc,0xf0f0,0xff00] : List Word).map (fun w=>(w,0,0))) (chart:=some ⟨[3,6,12,3,3,3,3,3,3,3,3,3,5,9,10,5,5,5,5,5,5,5,5,5],rfl⟩) (q3:=fun _=>(0,0)) (z8:=fun _=>none) (zR:=fun _ k=>k (fun _=>none)) (sample:=(0,0)) (bounds:=[]) (hints:=none) (witnesses:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,6,2),(0xff00,12,4)]) (fun _ _ h=>by cases h) (fun _ _ h=>⟨fun _=>none,h⟩) (fun _ h=>False.elim (List.not_mem_nil h)) (by decide +kernel) rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
def j8 : Word:=0xffff
def uf : Word:=0xf8c8
def kh : List Word:=[0xaaaa,0xcccc,0xf0f0,0xff00]
def q1k : Option qw:=some ⟨[3,6,12,3,3,3,3,3,3,3,3,3,5,9,10,5,5,5,5,5,5,5,5,5],rfl⟩
def q7t : List zW:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,6,2),(0xff00,12,4)]
def q4D : qH:=(0x2018080c0280c12030483014030501804060100c0203,10)
def v0 : zj:=fun i=>zf 1 5 0x1e i
def u3 : z2 :=
 qv 0x1 0xf 2 0x3 1 0x1 6 0x3f 4 0xf 0x1 5 1
theorem q0v : z1 u3 :=
 qt 0x1 0xf 2 0x3 1 0x1 6 0x3f 4 0xf 0x1 5 1
def q28 : List qb:=zk kh 0x4832cb7cd3 0x1e380078e1 10
noncomputable def q6N:=qG j8 10 q28 4 v0
noncomputable def q4C:=zx j8 kh 4 1 v0
noncomputable def q1j:=qr j8 kh 4 1 v0
def kA (a : Nat) : Option z0 :=
 if Nat.blt a 2 then
  match a with
  |1=>some [q1B,wu]
  | _=>none
 else none
theorem q5q : qP j8 uf 16 kA :=
 qs
  (sel:=fun a i=>Fin.ofNat 16 (qe 4 (z3 0x53000 12 a) i.val))
  (inv:=fun a i=>Fin.ofNat 16 (qe 4 (z3 0x53000 12 a) i.val))
  (bound:=2)
  (by intro a ha;unfold kA;rw [show Nat.blt a 2=false from by cases h : Nat.blt a 2;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def wy : List q2:=[]
theorem q5o : qu wy:=show qu [] from fun _ h=>False.elim (List.not_mem_nil h)
noncomputable def q5p:=qO 2 false true j8 uf q1k wy none 1 v0 q4C q1j kA u3 10 q6N
theorem q5n : qT 2 false j8 uf q1k (qk true wy) q7t 1 v0 q1j kA u3 kh 4 1=true:=by decide +kernel
theorem q8h : qE 0 1 q5p=true:=by decide +kernel
theorem ki : qo j8 kh uf 1 5 :=
 zm (root:=q28) (sample:=q4D) (hints:=none) q5q q0v q5o q5n q8h
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem q5V : qo 0xffffffff [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 0xffeaf8c8 0 7:=zm (maxK:=2) (q4:=false) (qV:=32) (qQ:=0) (root:=([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List Word).map (fun w=>(w,0,0))) (chart:=some ⟨[3,6,12,17,24,3,3,3,3,3,3,3,5,9,10,18,20,5,5,5,5,5,5,5],rfl⟩) (q3:=fun _=>(0,0)) (z8:=fun _=>none) (zR:=fun _ k=>k (fun _=>none)) (sample:=(0,0)) (bounds:=[]) (hints:=none) (witnesses:=[(0xaaaaaaaa,3,2),(0xcccccccc,3,1),(0xf0f0f0f0,6,2),(0xff00ff00,12,4),(0xffff0000,17,1)]) (fun _ _ h=>by cases h) (fun _ _ h=>⟨fun _=>none,h⟩) (fun _ h=>False.elim (List.not_mem_nil h)) (by decide +kernel) rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
def jd : Word:=0xffffffff
def uj : Word:=0xffeaf8c8
def ku : List Word:=[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def q1x : Option qw:=some ⟨[3,6,12,17,24,3,3,3,3,3,3,3,5,9,10,18,20,5,5,5,5,5,5,5],rfl⟩
def q7V : List zW:=[(0xaaaaaaaa,3,2),(0xcccccccc,3,1),(0xf0f0f0f0,6,2),(0xff00ff00,12,4),(0xffff0000,17,1)]
def q56 : qH:=(0xa070482c12110502c141809058241a0a0542816028180a1505068281102844241802830240302834201108060120d04830140609018100c0500c28060a0300a03040601203020180403008440406020300203,37)
def vs : zj:=fun i=>zf 3 13 0x19260d1850c1f20d904c81e40920f8 i
def ub : z2 :=
 qv 0x3a100000d0c000e401 0x4192260400e068180a18e1cd3937a5267464b7ab1bf4633c6c578989e0b10a53374866794caf2193c331f8463684c54981b920332a0565009c280f8401b060260803c08048001f 10 0x3ff 5 0x1f 19 0x7ffff 12 0xfff 0xf 16 5
theorem q0R : z1 ub :=
 qt 0x3a100000d0c000e401 0x4192260400e068180a18e1cd3937a5267464b7ab1bf4633c6c578989e0b10a53374866794caf2193c331f8463684c54981b920332a0565009c280f8401b060260803c08048001f 10 0x3ff 5 0x1f 19 0x7ffff 12 0xfff 0xf 16 5
def q2z : List qb:=zk ku 0x5f7c600885a135c94142f0a7d89b5b420daebe259d0959 0xf156260078100ec6040f6a01c88784a0d029c0ca98149 37
noncomputable def q7f:=qG jd 37 q2z 7 vs
noncomputable def q55:=zx jd ku 7 1 vs
noncomputable def q1w:=qr jd ku 7 1 vs
def kF (a : Nat) : Option z0 :=
 if Nat.blt a 10 then
  match a with
  |1=>some [un,q8a]
  |2=>some [q9C,q89]
  |3=>some [q9B,un,q89,yQ]
  |4=>some [kT,yQ]
  |5=>some [q8b,un,q8a,yQ]
  |6=>some [q8b,q1A]
  |7=>some [kT,w3,q89,yQ]
  |8=>some [q9C,q1A,q8a,yQ]
  |9=>some [q9B,w3]
  | _=>none
 else none
theorem q5U : qP jd uj 32 kF :=
 qs
  (sel:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x14e08d12235014d111b80a68889c04a700000 15 a) i.val))
  (inv:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x14e34444447014c88d380a11a29c04a700000 15 a) i.val))
  (bound:=10)
  (by intro a ha;unfold kF;rw [show Nat.blt a 10=false from by cases h : Nat.blt a 10;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def wQ : List q2:=[]
theorem q5S : qu wQ:=show qu [] from fun _ h=>False.elim (List.not_mem_nil h)
noncomputable def q5T:=qO 2 false true jd uj q1x wQ none 9 vs q55 q1w kF ub 37 q7f
theorem q5Q : qT 2 false jd uj q1x (qk true wQ) q7V 9 vs q1w kF ub ku 7 1=true:=by decide +kernel
theorem q8t : qE 0 9 q5T=true:=by decide +kernel
theorem q5R : qo jd ku uj 1 8 :=
 zm (root:=q2z) (sample:=q56) (hints:=none) q5U q0R q5S q5Q q8t
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem yU : qo 0xffffffff [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 0xfffef8c8 0 7:=zm (maxK:=2) (q4:=false) (qV:=32) (qQ:=0) (root:=([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List Word).map (fun w=>(w,0,0))) (chart:=some ⟨[3,6,12,17,18,20,24,3,3,3,3,3,5,9,10,16,5,5,5,5,5,5,5,5],rfl⟩) (q3:=fun _=>(0,0)) (z8:=fun _=>none) (zR:=fun _ k=>k (fun _=>none)) (sample:=(0,0)) (bounds:=[]) (hints:=none) (witnesses:=[(0xaaaaaaaa,3,2),(0xcccccccc,3,1),(0xf0f0f0f0,6,2),(0xff00ff00,12,4),(0xffff0000,17,1)]) (fun _ _ h=>by cases h) (fun _ _ h=>⟨fun _=>none,h⟩) (fun _ h=>False.elim (List.not_mem_nil h)) (by decide +kernel) rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
def qa3 : q2:=(0x55555555,[0x44444444,0x50505050,0x55005500,0x55550000],5,6,0x55545040)
theorem qa2 : EL qa3 5 6:=qh (qa 32 16 [1,2,3,4] 0) z7 z6 (by decide +kernel)
def qa1 : q2:=(0x33333333,[0x22222222,0x30303030,0x33003300,0x33330000],5,6,0x33323000)
theorem qa0 : EL qa1 5 6:=qh (qa 32 16 [2,3,0,4] 0) zT zS (by decide +kernel)
def q9Z : q2:=(0xf0f0f0f,[0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000],5,6,0xf0e0808)
theorem q9Y : EL q9Z 5 6:=qh (qa 32 16 [0,1,3,4] 0) zT zS (by decide +kernel)
def q9X : q2:=(0xff00ff,[0xaa00aa,0xcc00cc,0xf000f0,0xff0000],5,6,0xfe00c8)
theorem q9W : EL q9X 5 6:=qh (qa 32 16 [0,1,2,4] 0) z7 z6 (by decide +kernel)
def jb : Word:=0xffffffff
def ui : Word:=0xfffef8c8
def kr : List Word:=[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def q1u : Option qw:=some ⟨[3,6,12,17,18,20,24,3,3,3,3,3,5,9,10,16,5,5,5,5,5,5,5,5],rfl⟩
def q7Q : List zW:=[(0xaaaaaaaa,3,2),(0xcccccccc,3,1),(0xf0f0f0f0,6,2),(0xff00ff00,12,4),(0xffff0000,17,1)]
def q52 : qH:=(0x8140280c0a0d0284410180480c120b04830120d04844140305018140b0804820140403020110806004120201802110203004060100c0203,25)
def vp : zj:=fun i=>zf 1 6 0x3e i
def u7 : z2 :=
 qv 0x1 0x1f 2 0x3 1 0x1 7 0x7f 5 0x1f 0x1 6 1
theorem q0O : z1 u7 :=
 qt 0x1 0x1f 2 0x3 1 0x1 7 0x7f 5 0x1f 0x1 6 1
def q2w : List qb:=zk kr 0x1308dd02b894450c98b118f0ceedd113 0xd800ff90078000a000e08cef8011 25
noncomputable def q79:=qG jb 25 q2w 7 vp
noncomputable def q51:=zx jb kr 7 1 vp
noncomputable def q1t:=qr jb kr 7 1 vp
def kD (a : Nat) : Option z0 :=
 if Nat.blt a 2 then
  match a with
  |1=>some [q8b,q1A]
  | _=>none
 else none
theorem q5O : qP jb ui 32 kD :=
 qs
  (sel:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x20298000 15 a) i.val))
  (inv:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x20298000 15 a) i.val))
  (bound:=2)
  (by intro a ha;unfold kD;rw [show Nat.blt a 2=false from by cases h : Nat.blt a 2;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def wN : List q2:=[qa3,qa1,q9Z,q9X]
theorem q5M : qu wN:=q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q9W.1 q9W.2) q9Y.1 q9Y.2) qa0.1 qa0.2) qa2.1 qa2.2
noncomputable def q5N:=qO 2 false true jb ui q1u wN none 1 vp q51 q1t kD u7 25 q79
theorem q5L : qT 2 false jb ui q1u (qk true wN) q7Q 1 vp q1t kD u7 kr 7 1=true:=by decide +kernel
theorem q8r : qE 0 1 q5N=true:=by decide +kernel
theorem yT : qo jb kr ui 1 8 :=
 zm (root:=q2w) (sample:=q52) (hints:=none) q5O q0O q5M q5L q8r
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q4H : q2:=(0x33333333,[0x22222222,0x30303030,0x33003300,0x33330000],5,6,0x33323200)
theorem q2c : EL q4H 5 6:=qh (qa 32 16 [0,3,2,4] 0) z7 z6 (by decide +kernel)
def q4I : q2:=(0x55555555,[0x44444444,0x50505050,0x55005500,0x55550000],6,7,0x55545440)
theorem q2d : EL q4I 6 7:=qh (qa 32 16 [1,2,3,4] 0) km kl (by decide +kernel)
def q4G : q2:=(0xf0f0f0f,[0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000],6,7,0xf0e0e08)
theorem q2b : EL q4G 6 7:=qh (qa 32 16 [0,1,3,4] 0) km kl (by decide +kernel)
def q4F : q2:=(0xff00ff,[0xaa00aa,0xcc00cc,0xf000f0,0xff0000],5,6,0xfe00c8)
theorem q2a : EL q4F 5 6:=qh (qa 32 16 [0,1,2,4] 0) z7 z6 (by decide +kernel)
def q4E : q2:=(0xffff,[0xaaaa,0xcccc,0xf0f0,0xff00],5,6,0xfec8)
theorem q29 : EL q4E 5 6:=qh (qa 32 16 [0,1,2,3] 0) z7 z6 (by decide +kernel)
def yB : Word:=0xffffffff
def v3 : Word:=0xfffefec8
def jj : List Word:=[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def q02 : Option qw:=some ⟨[3,6,9,10,12,17,18,20,24,3,3,3,2,5,8,16,2,2,2,2,2,2,2,2],rfl⟩
def q5s : List zW:=[(0xaaaaaaaa,3,2),(0xcccccccc,3,1),(0xf0f0f0f0,6,2),(0xff00ff00,9,1),(0xffff0000,17,1)]
def q2M : qH:=(0x1003020180a0302824200a080480a1108050201804030201104060100a008240406040240412010280203008440403,21)
def jI : zj:=fun i=>zf 4 15 0x6512071f1a3036565480a91a1181f20264cac40e081f0 i
def v4 : z2 :=
 qv 0xd9d1c9c1b294745b2e0c01 0x160202cca0500e0a01c12c6820041431b2631d1006c18048b99b0732a2c06c180a92ca10534208039118ad9995a331f280561007c1809c29372466e08cac080e0001f 8 0xff 3 0x7 19 0x7ffff 12 0xfff 0xf 16 3
theorem wC : z1 v4 :=
 qt 0xd9d1c9c1b294745b2e0c01 0x160202cca0500e0a01c12c6820041431b2631d1006c18048b99b0732a2c06c180a92ca10534208039118ad9995a331f280561007c1809c29372466e08cac080e0001f 8 0xff 3 0x7 19 0x7ffff 12 0xfff 0xf 16 3
def q0x : List qb:=zk jj 0xf61218dd420a103b02bb644a7 0x1b40080590390000000b264086 21
noncomputable def q4K:=qG yB 21 q0x 7 jI
noncomputable def q2L:=zx yB jj 7 0 jI
noncomputable def q01:=qr yB jj 7 0 jI
def jw (a : Nat) : Option z0 :=
 if Nat.blt a 12 then
  match a with
  |1=>some [yQ]
  |2=>some [w3]
  |3=>some [un,yQ]
  |4=>some [w3,yQ]
  |5=>some [un]
  |6=>some [kT]
  |7=>some [kT,yQ]
  |8=>some [kT,w3]
  |9=>some [kT,un,yQ]
  |10=>some [kT,w3,yQ]
  |11=>some [kT,un]
  | _=>none
 else none
theorem q3y : qP yB v3 32 jw :=
 qs
  (sel:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x2c446069911421a70151828b50189865410a61c440000 15 a) i.val))
  (inv:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x2c44c888c0d421a70151828b5032a031310a61c440000 15 a) i.val))
  (bound:=12)
  (by intro a ha;unfold jw;rw [show Nat.blt a 12=false from by cases h : Nat.blt a 12;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def uv : List q2:=[q4H,q4I,q4G,q4F,q4E]
theorem q3w : qu uv:=q1 (q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q29.1 q29.2) q2a.1 q2a.2) q2b.1 q2b.2) q2d.1 q2d.2) q2c.1 q2c.2
noncomputable def q3x:=qO 2 false false yB v3 q02 uv none 12 jI q2L q01 jw v4 21 q4K
theorem q3v : qT 2 false yB v3 q02 (qk false uv) q5s 12 jI q01 jw v4 jj 7 0=true:=by decide +kernel
theorem q6P : qE 0 12 q3x=true:=by decide +kernel
theorem yl : qo yB jj v3 0 8 :=
 zm (root:=q0x) (sample:=q2M) (hints:=none) q3y wC q3w q3v q6P
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q62 : q2:=(0x5050505,[0x4040404,0x5000500,0x5050000],4,5,0x5040400)
theorem q61 : EL q62 4 5:=qh (qa 32 8 [1,3,4] 0) zI zH (by decide +kernel)
def yA : Word:=0xffffffff
def v1 : Word:=0xfffefec8
def ji : List Word:=[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def q00 : Option qw:=some ⟨[3,6,9,10,12,17,18,20,24,3,3,3,2,5,8,16,2,2,2,2,2,2,2,2],rfl⟩
def q5r : List zW:=[(0xaaaaaaaa,3,2),(0xcccccccc,3,1),(0xf0f0f0f0,6,2),(0xff00ff00,9,1),(0xffff0000,17,1)]
def q2K : qH:=(0x80c0205010030280c0a0902844080608028201408060201204030201104060100a010181009010480209010280203008440403,23)
def jH : zj:=fun i=>zf 4 16 0x328e01cb63499368036862a732a702a7c424342401f301333153328232b101c1315101f0 i
def v2 : z2 :=
 qv 0x2910028100271986518c9d65d800001342688105c01 0x11010113281001c1001c0e01c0f6340d0100e9364d6360c3294a31d0d0360a0122c6360c62a2b3360b32a2a0360a02a09c4248942083420701c6492d8762b446216632b4631f053152702b0701f06013040090432861c39839374192d233370332b013150201c0001f 10 0x3ff 4 0xf 20 0xfffff 12 0xfff 0x1f 17 4
theorem wz : z1 v2 :=
 qt 0x2910028100271986518c9d65d800001342688105c01 0x11010113281001c1001c0e01c0f6340d0100e9364d6360c3294a31d0d0360a0122c6360c62a2b3360b32a2a0360a02a09c4248942083420701c6492d8762b446216632b4631f053152702b0701f06013040090432861c39839374192d233370332b013150201c0001f 10 0x3ff 4 0xf 20 0xfffff 12 0xfff 0x1f 17 4
def q0w : List qb:=zk ji 0x2276228956b1852200cc8d69e0457 0xf400201681bc0000000548e0016 23
noncomputable def q4J:=qG yA 23 q0w 8 jH
noncomputable def q2J:=zx yA ji 8 1 jH
noncomputable def wZ:=qr yA ji 8 1 jH
def jv (a : Nat) : Option z0 :=
 if Nat.blt a 12 then
  match a with
  |1=>some [yQ]
  |2=>some [w3]
  |3=>some [un,yQ]
  |4=>some [w3,yQ]
  |5=>some [un]
  |6=>some [kT]
  |7=>some [kT,yQ]
  |8=>some [kT,w3]
  |9=>some [kT,un,yQ]
  |10=>some [kT,w3,yQ]
  |11=>some [kT,un]
  | _=>none
 else none
theorem q3u : qP yA v1 32 jv :=
 qs
  (sel:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x2c446069911421a70151828b50189865410a61c440000 15 a) i.val))
  (inv:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x2c44c888c0d421a70151828b5032a031310a61c440000 15 a) i.val))
  (bound:=12)
  (by intro a ha;unfold jv;rw [show Nat.blt a 12=false from by cases h : Nat.blt a 12;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def uu : List q2:=[q4H,q4F,q4I,q4G,q4E,q62]
theorem q3s : qu uu:=q1 (q1 (q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q61.1 q61.2) q29.1 q29.2) q2b.1 q2b.2) q2d.1 q2d.2) q2a.1 q2a.2) q2c.1 q2c.2
noncomputable def q3t:=qO 2 false true yA v1 q00 uu none 18 jH q2J wZ jv v2 23 q4J
theorem q3r : qT 2 false yA v1 q00 (qk true uu) q5r 18 jH wZ jv v2 ji 8 1=true:=by decide +kernel
theorem q6O : qE 0 18 q3t=true:=by decide +kernel
theorem yk : qo yA ji v1 1 9 :=
 zm (root:=q0w) (sample:=q2K) (hints:=none) q3u wz q3s q3r q6O
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q4O : q2:=(0x55555555,[0x44444444,0x50505050,0x55005500,0x55550000],6,7,0x55545440)
theorem q2i : EL q4O 6 7:=qh (qa 32 16 [1,2,3,4] 0) km kl (by decide +kernel)
def q2R : q2:=(0x3030303,[0x2020202,0x3000300,0x3030000],4,5,0x3020200)
theorem q0X : EL q2R 4 5:=qh (qa 32 8 [0,3,4] 0) zI zH (by decide +kernel)
def q4M : q2:=(0xff00ff,[0xaa00aa,0xcc00cc,0xf000f0,0xff0000],5,6,0xfe00c0)
theorem q2g : EL q4M 5 6:=qh (qa 32 16 [1,2,0,4] 0) zT zS (by decide +kernel)
def q4N : q2:=(0x33333333,[0x22222222,0x30303030,0x33003300,0x33330000],5,6,0x33323200)
theorem q2h : EL q4N 5 6:=qh (qa 32 16 [0,3,2,4] 0) z7 z6 (by decide +kernel)
def yE : Word:=0xffffffff
def v9 : Word:=0xfffefec0
def jm : List Word:=[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def q08 : Option qw:=some ⟨[6,9,10,12,17,18,20,24,6,6,6,6,3,5,8,16,3,3,3,3,3,3,3,3],rfl⟩
def q5y : List zW:=[(0xaaaaaaaa,9,8),(0xcccccccc,6,4),(0xf0f0f0f0,6,2),(0xff00ff00,9,1),(0xffff0000,17,1)]
def q2V : qH:=(0x412020300814080280411028242012080600409010280a1101818061100824101808050080602818100a018240211040302011040240406,25)
def jM : zj:=fun i=>zf 3 15 0x31a79426684e4dd01529372656404880f8 i
def vc : z2 :=
 qv 0xa9a10000765b430f01 0x20cd08634dd8d676295ccd473299407850121e5086342100405937500d8402a0e4df2637898ad233708cae101e04048001f 8 0xff 3 0x7 18 0x3ffff 12 0xfff 0xf 16 3
theorem wH : z1 vc :=
 qt 0xa9a10000765b430f01 0x20cd08634dd8d676295ccd473299407850121e5086342100405937500d8402a0e4df2637898ad233708cae101e04048001f 8 0xff 3 0x7 18 0x3ffff 12 0xfff 0xf 16 3
def q0D : List qb:=zk jm 0x156561455c6353008e26494382195836 0x26020400022532106022360420878b0 25
noncomputable def q4Q:=qG yE 25 q0D 7 jM
noncomputable def q2U:=zx yE jm 7 0 jM
noncomputable def q07:=qr yE jm 7 0 jM
def jz (a : Nat) : Option z0 :=
 if Nat.blt a 4 then
  match a with
  |1=>some [yQ]
  |2=>some [q1A]
  |3=>some [q1A,yQ]
  | _=>none
 else none
theorem q3L : qP yE v9 32 jz :=
 qs
  (sel:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x70a11941c440000 15 a) i.val))
  (inv:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x70a11941c440000 15 a) i.val))
  (bound:=4)
  (by intro a ha;unfold jz;rw [show Nat.blt a 4=false from by cases h : Nat.blt a 4;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def uA : List q2:=[q4O,q2R,q4M,q4N]
theorem q3J : qu uA:=q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q2h.1 q2h.2) q2g.1 q2g.2) q0X.1 q0X.2) q2i.1 q2i.2
noncomputable def q3K:=qO 2 false false yE v9 q08 uA none 9 jM q2U q07 jz vc 25 q4Q
theorem q3I : qT 2 false yE v9 q08 (qk false uA) q5y 9 jM q07 jz vc jm 7 0=true:=by decide +kernel
theorem q6U : qE 0 9 q3K=true:=by decide +kernel
theorem yo : qo yE jm v9 0 8 :=
 zm (root:=q0D) (sample:=q2V) (hints:=none) q3L wH q3J q3I q6U
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q7y : q2:=(0xf0f0f0f,[0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000],5,6,0xf0e0e00)
theorem q7x : EL q7y 5 6:=qh (qa 32 16 [0,3,1,4] 0) z7 z6 (by decide +kernel)
def q65 : q2:=(0x11111111,[0x10101010,0x11001100,0x11110000],4,5,0x11101000)
theorem q64 : EL q65 4 5:=qh (qa 32 8 [2,3,4] 0) zI zH (by decide +kernel)
def q7w : q2:=(0xffff,[0xaaaa,0xcccc,0xf0f0,0xff00],5,6,0xfec0)
theorem q7v : EL q7w 5 6:=qh (qa 32 16 [1,2,0,3] 0) zT zS (by decide +kernel)
def yD : Word:=0xffffffff
def v7 : Word:=0xfffefec0
def jl : List Word:=[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def q06 : Option qw:=some ⟨[6,9,10,12,17,18,20,24,6,6,6,6,3,5,8,16,3,3,3,3,3,3,3,3],rfl⟩
def q5x : List zW:=[(0xaaaaaaaa,9,8),(0xcccccccc,6,4),(0xf0f0f0f0,6,2),(0xff00ff00,9,1),(0xffff0000,17,1)]
def q2T : qH:=(0x182c0a070181c200a01044080c02050201202824061102844060608060040901048060908050040a040600209020180a06040282011040300211040240406,28)
def jL : zj:=fun i=>zf 4 16 0x634a93686368c42594253425937402a431e3937132b1012192d1315101f0 i
def v8 : z2 :=
 qv 0x27194a4184df2001784d0e53080006c01 0x34040e33430040e63434101c034300a0d936318dab641e98d6a6292cd05a33528ca6801e20048bc422a50893421c0416c39224dc692d5c0d8702a98ca8631e4b0e459370a4b74637918ae162150cdc432b04c56301e0c048001f 10 0x3ff 4 0xf 18 0x3ffff 12 0xfff 0xf 16 4
theorem wG : z1 v8 :=
 qt 0x27194a4184df2001784d0e53080006c01 0x34040e33430040e63434101c034300a0d936318dab641e98d6a6292cd05a33528ca6801e20048bc422a50893421c0416c39224dc692d5c0d8702a98ca8631e4b0e459370a4b74637918ae162150cdc432b04c56301e0c048001f 10 0x3ff 4 0xf 18 0x3ffff 12 0xfff 0xf 16 4
def q0C : List qb:=zk jl 0xb6aa14948d72a66108c9f1124e1e8e5116 0x1108810000022a46a00c0a857401e0f1144 28
noncomputable def q4P:=qG yD 28 q0C 8 jL
noncomputable def q2S:=zx yD jl 8 1 jL
noncomputable def q05:=qr yD jl 8 1 jL
def jy (a : Nat) : Option z0 :=
 if Nat.blt a 4 then
  match a with
  |1=>some [yQ]
  |2=>some [q1A]
  |3=>some [q1A,yQ]
  | _=>none
 else none
theorem q3H : qP yD v7 32 jy :=
 qs
  (sel:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x70a11941c440000 15 a) i.val))
  (inv:=fun a i=>Fin.ofNat 32 (qe 5 (z3 0x70a11941c440000 15 a) i.val))
  (bound:=4)
  (by intro a ha;unfold jy;rw [show Nat.blt a 4=false from by cases h : Nat.blt a 4;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def uz : List q2:=[q4O,q4N,q2R,q7y,q4M,q65,q7w]
theorem q3F : qu uz:=q1 (q1 (q1 (q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q7v.1 q7v.2) q64.1 q64.2) q2g.1 q2g.2) q7x.1 q7x.2) q0X.1 q0X.2) q2h.1 q2h.2) q2i.1 q2i.2
noncomputable def q3G:=qO 2 false true yD v7 q06 uz none 15 jL q2S q05 jy v8 28 q4P
theorem q3E : qT 2 false yD v7 q06 (qk true uz) q5x 15 jL q05 jy v8 jl 8 1=true:=by decide +kernel
theorem q6T : qE 0 15 q3G=true:=by decide +kernel
theorem yn : qo yD jl v7 1 9 :=
 zm (root:=q0C) (sample:=q2T) (hints:=none) q3H wG q3F q3E q6T
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q86 : q2:=(0x5555555555555555,[0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000],7,8,0x5555555455405040)
theorem q6r : EL q86 7 8:=qh (qa 64 32 [1,2,3,4,5] 0) yU yT (by decide +kernel)
def q85 : q2:=(0x3333333333333333,[0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000],7,8,0x3333333233223000)
theorem q6q : EL q85 7 8:=qh (qa 64 32 [0,4,3,2,5] 0) yU yT (by decide +kernel)
def q81 : q2:=(0xffffffff,[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],7,8,0xffeaf8c8)
theorem q6m : EL q81 7 8:=qh (qa 64 32 [0,1,2,3,4] 0) q5V q5R (by decide +kernel)
def q84 : q2:=(0xf0f0f0f0f0f0f0f,[0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000],7,8,0xf0f0f0e0f0a0808)
theorem q6p : EL q84 7 8:=qh (qa 64 32 [1,0,4,3,5] 0) yU yT (by decide +kernel)
def q4c : q2:=(0x101010101010101,[0x100010001000100,0x101000001010000,0x101010100000000],4,5,0x101010001000000)
theorem q1X : EL q4c 4 5:=qh (qa 64 8 [3,4,5] 0) zI zH (by decide +kernel)
def q4b : q2:=(0x111100001111,[0x101000001010,0x110000001100,0x111100000000],4,5,0x111000001000)
theorem q1W : EL q4b 4 5:=qh (qa 64 8 [2,3,5] 0) zI zH (by decide +kernel)
def q6u : q2:=(0x505050505050505,[0x404040404040404,0x500050005000500,0x505000005050000,0x505050500000000],5,6,0x505050405000000)
theorem q3Y : EL q6u 5 6:=qh (qa 64 16 [3,4,1,5] 0) zT zS (by decide +kernel)
def q6v : q2:=(0x1111111111111111,[0x1010101010101010,0x1100110011001100,0x1111000011110000,0x1111111100000000],5,6,0x1111111011001000)
theorem q3Z : EL q6v 5 6:=qh (qa 64 16 [2,3,4,5] 0) z7 z6 (by decide +kernel)
def q49 : q2:=(0x3000300030003,[0x2000200020002,0x3000000030000,0x3000300000000],4,5,0x3000200020000)
theorem q1U : EL q49 4 5:=qh (qa 64 8 [0,4,5] 0) zI zH (by decide +kernel)
def q6t : q2:=(0x55005500550055,[0x44004400440044,0x50005000500050,0x55000000550000,0x55005500000000],5,6,0x55005400400040)
theorem q3X : EL q6t 5 6:=qh (qa 64 16 [1,2,4,5] 0) zT zS (by decide +kernel)
def q83 : q2:=(0xff00ff00ff00ff,[0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000],7,8,0xff00fe00ea00c8)
theorem q6o : EL q83 7 8:=qh (qa 64 32 [2,1,0,4,5] 0) yU yT (by decide +kernel)
def q4a : q2:=(0x5500000055,[0x4400000044,0x5000000050,0x5500000000],4,5,0x5400000040)
theorem q1V : EL q4a 4 5:=qh (qa 64 8 [1,2,5] 0) zI zH (by decide +kernel)
def q82 : q2:=(0xffff0000ffff,[0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000],7,8,0xfffe0000f8c8)
theorem q6n : EL q82 7 8:=qh (qa 64 32 [0,1,2,3,5] 0) yU yT (by decide +kernel)
def q6s : q2:=(0x555500005555,[0x444400004444,0x505000005050,0x550000005500,0x555500000000],5,6,0x555400005040)
theorem q3W : EL q6s 5 6:=qh (qa 64 16 [1,2,3,5] 0) z7 z6 (by decide +kernel)
def q48 : q2:=(0xf0000000f,[0xa0000000a,0xc0000000c,0xf00000000],4,5,0xe00000008)
theorem q1T : EL q48 4 5:=qh (qa 64 8 [0,1,5] 0) zI zH (by decide +kernel)
def j5 : Word:=0xffffffffffffffff
def ue : Word:=0xfffffffeffeaf8c8
def kd : List Word:=[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def q1g : Option qw:=some ⟨[3,6,12,17,24,33,34,36,40,48,3,3,5,9,10,18,20,32,5,5,5,5,5,5],rfl⟩
def q7k : List zW:=[(0xaaaaaaaaaaaaaaaa,3,2),(0xcccccccccccccccc,3,1),(0xf0f0f0f0f0f0f0f0,6,2),(0xff00ff00ff00ff00,12,4),(0xffff0000ffff0000,17,1),(0xffffffff00000000,33,1)]
def q4i : qH:=(0x14110a0c010060a0841011040a02818050a010031000c12280a09028030289024110508808240281824030403024220506040240484414060906040300a01840280a03020181008424061008814030488420110108810180284428110480c0a210280c0a0c020180403048300221010180203020300211,53)
def kS : zj:=fun i=>zf 7 19 0xd3981a6f635b808560d0a71a74d3349a0553407249aa3834068668d0ca1a4a0b301066c6ec18ad8195aec4c59268b18d1619a2c03459886971052ca1a53424a056941692021a302947268718d0e01a1c95a34c865590097a79164e22c8444cd88821119411ac82358dc68150d94318c86318dc66270b94e172862990c531b8a94e13284259384b2109c43112862190c431b8864f0ec961d90c39a78734b0e6861cd043815060280c03c18070362785c4b0b29e165382c9b8534f0a66e1413c2827050370a06c1713c23278404e0806c10078262783c4b0729e0e50c1c9b8364f06c9c0d8dc1b1b0362a0609e0c0dc181503c4f0529e0a50c10270204c0406c080d010150202804086040fc080f8101b020260403c081f80 i
def vW : z2 :=
 qv 0x998732040004c41980200000000000000000025c1000000000000000000000000000000000096820002580ca829482000246347850000000000000008e040002360c6818c05160a242000000000002220800000000000000000000000000000000000000000000000000000000000440100010b14000420382090209fc23ec37c84f60de22bb050000000000000007114e105b43b602688e000000000000000000000033056486c41400000000000000182180000000c005762ad85588aab19444a7844e04981128224043648612c8ae0f8715a61f3002f0001 0x7a19a4740400ea0681d00d03a00f0740346e6650bcc0a1399a00733404e726a1cd8d5380082f194c1dcc809c4d30791a006e0340e4050bc710878b213723420e40851bc040b89a007101c2e00801c00d83899506f0340e26841b8108b862707034e0de6681b80a83680e06c3541d1882da2505ee31b0dc02a0b60381acd003519a0693280d1283178ca86f0150670108ba6543740a9f14a13559367bec84f518d83331b86562b6c0656d898d9b099b3e36376acc56190cad2f32725d64c6b466a940c742e027063c4c0c52681858d03019a05f0345a5e9cd6b168694a734d9344b0c9c560d392618e05a05a09a08015c0d02c81b05ec430bb88217250d69c9b85b3420b405693c045a8ca005905a59d2843359086b9a105804309a06a15c0a527008956c4c0ad2681558d0aa19a0540340a7284540d0827814153f5a0a72b41498d8a71a004e0280a4c86534d082680f0516400a1e9e13d9382732104d3360980841101602582613a0400860680e80a01f82c04a04c2760801040d01e81404905a08a0b00f81309e0200400340780504ff134a562084494d0972820fd934253208496372906541200a8a362184794308cc861158dc2262704394e28388610a50c20b2184063707f29c0fa5081eb2703c6420778860ea50c1cb2183863716989e25b13459e258b2c431638822de53c54ca68b694b16b286a6a4dd4749983764f052c9a0d992c1ab21bac637742c66c718ad87b1383434f02c69a0ccd2c191a183134124e66e480ccd96195b2132743463e838c6c4901b8a502b14805409407c1200f012013757286e6e4dd95b1b8ae04215a0802c00d85781a03002a05e0500b80781680e22cf4f457e960b313c15e25a99c4351b87e0aa53c14ca72289431292840a24dd8a49b22564f448c9c88d90d1132139163704e69e698d0c1319b81332942063a09413c1202709104304606e0880d808009221f4f04389e08193c0f82721e04203c06c0740788d7a781cc4f03789646310c0d4a781994303126e05d93c0b32711364202ac6e0518d809b1511234f220684444cdc0902781103702005443bd3c07e2780e94f01b2860301380582610804220e0800280d80481a00802a00e05061b10cc2e1fa8694350b27ea0a4dd40c99a0664340ac7ee118ddc1b19b0262b602c4e418d0c8299f904337206666c10cad81993a0231f40263601810c0281f8820371020662100ac4181380401f00603600804c0080780003f 15 0x7fff 6 0x3f 23 0x7fffff 12 0xfff 0x7f 19 6
theorem q0l : z1 vW :=
 qt 0x998732040004c41980200000000000000000025c1000000000000000000000000000000000096820002580ca829482000246347850000000000000008e040002360c6818c05160a242000000000002220800000000000000000000000000000000000000000000000000000000000440100010b14000420382090209fc23ec37c84f60de22bb050000000000000007114e105b43b602688e000000000000000000000033056486c41400000000000000182180000000c005762ad85588aab19444a7844e04981128224043648612c8ae0f8715a61f3002f0001 0x7a19a4740400ea0681d00d03a00f0740346e6650bcc0a1399a00733404e726a1cd8d5380082f194c1dcc809c4d30791a006e0340e4050bc710878b213723420e40851bc040b89a007101c2e00801c00d83899506f0340e26841b8108b862707034e0de6681b80a83680e06c3541d1882da2505ee31b0dc02a0b60381acd003519a0693280d1283178ca86f0150670108ba6543740a9f14a13559367bec84f518d83331b86562b6c0656d898d9b099b3e36376acc56190cad2f32725d64c6b466a940c742e027063c4c0c52681858d03019a05f0345a5e9cd6b168694a734d9344b0c9c560d392618e05a05a09a08015c0d02c81b05ec430bb88217250d69c9b85b3420b405693c045a8ca005905a59d2843359086b9a105804309a06a15c0a527008956c4c0ad2681558d0aa19a0540340a7284540d0827814153f5a0a72b41498d8a71a004e0280a4c86534d082680f0516400a1e9e13d9382732104d3360980841101602582613a0400860680e80a01f82c04a04c2760801040d01e81404905a08a0b00f81309e0200400340780504ff134a562084494d0972820fd934253208496372906541200a8a362184794308cc861158dc2262704394e28388610a50c20b2184063707f29c0fa5081eb2703c6420778860ea50c1cb2183863716989e25b13459e258b2c431638822de53c54ca68b694b16b286a6a4dd4749983764f052c9a0d992c1ab21bac637742c66c718ad87b1383434f02c69a0ccd2c191a183134124e66e480ccd96195b2132743463e838c6c4901b8a502b14805409407c1200f012013757286e6e4dd95b1b8ae04215a0802c00d85781a03002a05e0500b80781680e22cf4f457e960b313c15e25a99c4351b87e0aa53c14ca72289431292840a24dd8a49b22564f448c9c88d90d1132139163704e69e698d0c1319b81332942063a09413c1202709104304606e0880d808009221f4f04389e08193c0f82721e04203c06c0740788d7a781cc4f03789646310c0d4a781994303126e05d93c0b32711364202ac6e0518d809b1511234f220684444cdc0902781103702005443bd3c07e2780e94f01b2860301380582610804220e0800280d80481a00802a00e05061b10cc2e1fa8694350b27ea0a4dd40c99a0664340ac7ee118ddc1b19b0262b602c4e418d0c8299f904337206666c10cad81993a0231f40263601810c0281f8820371020662100ac4181380401f00603600804c0080780003f 15 0x7fff 6 0x3f 23 0x7fffff 12 0xfff 0x7f 19 6
def q1Z : List qb:=zk kd 0x154d628a55082194040ac4170010720144e02091100a694a4006a88325a243915993194420273e55 0x10008a500000a43450ad11000ada1158032410290e600a00de0a040cb302900900048820022f35 53
noncomputable def q6A:=qG j5 53 q1Z 10 kS
noncomputable def q4h:=zx j5 kd 10 0 kS
noncomputable def q1f:=qr j5 kd 10 0 kS
def ky (a : Nat) : Option z0 :=
 if Nat.blt a 10 then
  match a with
  |1=>some [q2C,q2B]
  |2=>some [q6F,q2A]
  |3=>some [q6D,q2C,q2A,w2]
  |4=>some [q6E,w2]
  |5=>some [q0o,q2C,q2B,w2]
  |6=>some [q0o,q0n]
  |7=>some [q6E,q6C,q2A,w2]
  |8=>some [q6F,q0n,q2B,w2]
  |9=>some [q6D,q6C]
  | _=>none
 else none
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5i : qP j5 ue 64 ky :=
 qs
  (sel:=fun a i=>Fin.ofNat 64 (qe 6 (z3 0xa0a7288d1a446ac053a888eb80aad112a701a53800000 18 a) i.val))
  (inv:=fun a i=>Fin.ofNat 64 (qe 6 (z3 0xa0a72b444a888ec053a446ab80aa2346a701a53800000 18 a) i.val))
  (bound:=10)
  (by intro a ha;unfold ky;rw [show Nat.blt a 10=false from by cases h : Nat.blt a 10;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def wr : List q2:=[q86,q85,q81,q84,q4c,q4b,q6u,q6v,q49,q6t,q83,q4a,q82,q6s,q48]
theorem q5g : qu wr:=q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q1T.1 q1T.2) q3W.1 q3W.2) q6n.1 q6n.2) q1V.1 q1V.2) q6o.1 q6o.2) q3X.1 q3X.2) q1U.1 q1U.2) q3Z.1 q3Z.2) q3Y.1 q3Y.2) q1W.1 q1W.2) q1X.1 q1X.2) q6p.1 q6p.2) q6m.1 q6m.2) q6q.1 q6q.2) q6r.1 q6r.2
def q4j : Nat → Nat:=fun i =>
 match Nat.shiftRight i 6 with
 | 0=>y9 0xc00000000000000000003080000004000008200000230000c118000030c000304600000000000000000000140000004000000000000028000001400000060000083000000200000510000000000000000000001800000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000400000000000000000000000000041003122080000104000008200000290031220eac8218418628c20d58c450311e90eac8331400c12420000000 29 (Nat.land i 63)
 | _=>0
noncomputable def q5h:=qO 2 false false j5 ue q1g wr (some q4j) 118 kS q4h q1f ky vW 53 q6A
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5f : qT 2 false j5 ue q1g (qk false wr) q7k 118 kS q1f ky vW kd 10 0=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q88 : qE 0 118 q5h=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1e : qo j5 kd ue 0 11 :=
 zm (root:=q1Z) (sample:=q4i) (hints:=(some q4j)) q5i q0l q5g q5f q88
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q8O : q2:=(0x33003300330033,[0x22002200220022,0x30003000300030,0x33000000330000,0x33003300000000],5,6,0x33003200220000)
theorem q8N : EL q8O 5 6:=qh (qa 64 16 [0,4,2,5] 0) zT zS (by decide +kernel)
def q8S : q2:=(0x55555555,[0x44444444,0x50505050,0x55005500,0x55550000],4,5,0x55405040)
theorem q8R : EL q8S 4 5:=qh (qa 64 16 [1,2,3,4] 0) kj ki (by decide +kernel)
def q8I : q2:=(0xf000f000f000f,[0xa000a000a000a,0xc000c000c000c,0xf0000000f0000,0xf000f00000000],5,6,0xf000e000a0008)
theorem q8H : EL q8I 5 6:=qh (qa 64 16 [1,0,4,5] 0) z7 z6 (by decide +kernel)
def q8Q : q2:=(0x303030303030303,[0x202020202020202,0x300030003000300,0x303000003030000,0x303030300000000],5,6,0x303030203020000)
theorem q8P : EL q8Q 5 6:=qh (qa 64 16 [0,4,3,5] 0) z7 z6 (by decide +kernel)
def q8G : q2:=(0xf0f00000f0f,[0xa0a00000a0a,0xc0c00000c0c,0xf0000000f00,0xf0f00000000],5,6,0xf0e00000808)
theorem q8F : EL q8G 5 6:=qh (qa 64 16 [0,1,3,5] 0) zT zS (by decide +kernel)
def q8M : q2:=(0x333300003333,[0x222200002222,0x303000003030,0x330000003300,0x333300000000],5,6,0x333200003000)
theorem q8L : EL q8M 5 6:=qh (qa 64 16 [2,3,0,5] 0) zT zS (by decide +kernel)
def q8E : q2:=(0xf0f0f0f,[0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000],4,5,0xf0a0808)
theorem q8D : EL q8E 4 5:=qh (qa 64 16 [1,0,4,3] 0) kj ki (by decide +kernel)
def q8K : q2:=(0x33333333,[0x22222222,0x30303030,0x33003300,0x33330000],4,5,0x33223000)
theorem q8J : EL q8K 4 5:=qh (qa 64 16 [0,4,3,2] 0) kj ki (by decide +kernel)
def q8A : q2:=(0xff00ff,[0xaa00aa,0xcc00cc,0xf000f0,0xff0000],4,5,0xea00c8)
theorem q8z : EL q8A 4 5:=qh (qa 64 16 [2,1,0,4] 0) kj ki (by decide +kernel)
def q8C : q2:=(0xff000000ff,[0xaa000000aa,0xcc000000cc,0xf0000000f0,0xff00000000],5,6,0xfe000000c8)
theorem q8B : EL q8C 5 6:=qh (qa 64 16 [0,1,2,5] 0) z7 z6 (by decide +kernel)
def q8y : q2:=(0xffff,[0xaaaa,0xcccc,0xf0f0,0xff00],4,5,0xf8c8)
theorem q8x : EL q8y 4 5:=qh (qa 64 16 [0,1,2,3] 0) kj ki (by decide +kernel)
def j4 : Word:=0xffffffffffffffff
def ud : Word:=0xfffffffeffeaf8c8
def kc : List Word:=[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def q1d : Option qw:=some ⟨[3,6,12,17,24,33,34,36,40,48,3,3,5,9,10,18,20,32,5,5,5,5,5,5],rfl⟩
def q7j : List zW:=[(0xaaaaaaaaaaaaaaaa,3,2),(0xcccccccccccccccc,3,1),(0xf0f0f0f0f0f0f0f0,6,2),(0xff00ff00ff00ff00,12,4),(0xffff0000ffff0000,17,1),(0xffffffff00000000,33,1)]
def q4e : qH:=(0x222008c004180089004210409010300503820060808840071002c14210a070400c05034401800088102204018400604860200302084282110044000602060121904044020c090c02830020441021090c828030503028340a06002060400c142a048a02413080c01229050a00a250904428160281c0a241000c10280a090241605088120b02818241a0502c141a028542815020901211050602418090880a0c0284424030a03014060a0182811100a04024100c020180804412210403024060500c120c028840a0d0480c0a0310088402101088120d0406008060088404060100c080c008440203,103)
def kR : zj:=fun i =>
 match Nat.shiftRight i 8 with
 | 0=>zf 6 19 0xfc86368c06d180aa34a7c493788c9f118de21954402a8803d13136102d42056840ab0815214a74094c812850250203144032881eb4fa569f0213e03d7c078fa569e4ac3c62878650f2535d02d3a056740aae8151d3263864270c80e18d1c18e3925a6ccb4d8121b32d34f5a658b4ca4d5932d3264e64084c80f5901e3265a618b4bb13976212e6425c060b9969632c2c64c58c84b1901618e2c93754c9aa98dd562d28c42512b4a253941ad28342512b49a509332d2635a4cc86918ad21a1a432b492b2880d910152293741266819350321a063f40c6e818cd0315a06274065680c7d00152001e4002483d3cf6279e9303cc9e7990cf31b9e34f3c66e7b168e6271c356380b470138e0261c04239e9e6b13cd4a71a94234c9e6990cd3149a34f3468668cdcd0271a04234080680d8d00f1a01235e9e6313cc4a7989433126e60d3cc19b9895a2c6ac58168b02116f4f2989e5310ca4a79494328c9c51908a1a7943372809c50108a01b1402a280245193c9325926432469e48d2c91a192341264a24c9409015100282003c40070800410c4f1d8963a53c74a70e9371c69e38cdc70278e04e1c06e380d874968e92c1d89e3193c60270c0361803c3002066278ac4b1529e2a50c549b8a64f14c9c298dc531b0a62a1409e28138501b8a02a14c422988056278894f1128620cd840270804c1006c200d04015080281001020d3c3195863270c63e18c6c30090600f0c01c1a53c24a584937092661193c23258464308c7e118dc23198462b08c4e10d3c21958431f0809c1012c20250402a0804e10098200f0401b080341010c101f8201f040360804c100782f4504012080fc0 (Nat.land i 255)
 | 1=>zf 7 20 0x625cf621cf620cf4a7cf4a5cf4a1cf31bcf315cf1a7cf1a54f1a1cf1a14f027cf021cf020cf01bcf015cf928cf4ad4e32d4e02d4e327cd3274d1a7cd1a74d19bcd027cd021cd01bcd014cd62d4c6214c1ad4c1a14c02b4c01f4c627cb625cb327cb31bcb1a7cb19bcb0274b025cb01b4b019cb00f4b02d4aaae4a02d49aae494a7c84a1c84a0c81a7c81a1c81a0c8928c892848627474a74761c47327461a74631046627c5327c532d44aaec4aae4449a4331ac331a4301a4361c43626c232d4202d42aae4292d414ad413274192841aae3f4a7be4a5be4a1be327be321be31bbe315be928be9283e7ad3d62d3d32d3d7a23d627bc6273c625bc4a7bc4a73c327bc321bc31bbc61cbc61c3c627bb621bb4a73b49b3b4963b32c3a3273a31b3aaae3a627b9621b9620b94a7b94a5b94a1b949bb9327b9321b931bb9315b919b39195b91953918f39027b902539021b902139020b902039928b97ad3862d3832d38320381ad3802d387a2387a7b7627b7621b74a73732737321371a73719b3702737021377adb64ad364a1361ad3602b3601f36627b5625b54a7b54a1b549bb51a7b519bb502735025b501b35019b50153502d34aae3402d33aae3392d324ad3202732928324a731194314a7b04a1b04a0b0327b0321b0320b031bb001530928b0928304a1af321af31baf0152f7a2af6272e4a72e61c2e4a1ad321ad31bad496ad7a7ac4a72c4a12c3272c3212c4962c621ab4a1ab321ab31bab1952b0152b310ab627aa4a7aa4a1aa0242a0182a0122a326a962d281ad281a12801b28018a8018281ad271a127195274ad264a12649b2619b2601526012a6012261ad251ac251a1251a02519b2519a2549ba4499a4321a431fa431ba4319a4315a4313a4015a4 (Nat.land i 255)
 | 2=>zf 9 22 0x1955e587f7831bde0c67781a1de066f78195de063f7801bde003f7800f5e0025781a65dd89d734a75cc669710265c52836b7a75a989d6a49ada8c9d6a1a15a466d696275a129d683275a069d681a15a0c856732059c69d671a159c6816719b59c0556732759869d6619a59809d660155980c16562d58cc6d621a7588699627ad5806b56002d5800a95f00e555e994332650cc9d42321508c814200e509e9d3d3274f4c853c00e4f1e9d353274d5e9d3131b4c1e9d2f6274bcc9d2f7a74a989d2a3274a8c85293214a00392802549c0a92602a495287234a1c89887214a1c858b4f93273e0c84f74aa3d0084f10273980a8e5025390054d502a34989ccc327330c84cc021330090c90213180a8c5025310078bf01e2f4698b34ac2a8c50aa0142a8cb0a6327298cb0a332028c638a300e28d29ca21a1288c84a000ea812a89c621a6d2609a49825c6689302a24929c9002524189c8b7ad225280894a1221284871ad214c6c8419ba1008284015a11e9c8362720cc9c8319aa0c09e8301aa0d886824a1a08c84821a1a0866e82021a0806e82015a08c84800271fc06c7f32a1f4ca87c7ad1bcc6a6d62d1ad884684a71a069c681a11a0052684a119cc6c664a69946ac651aa196ab86562c9912b064321190c6c6431019189a624a69892926232698aab86262c984cb0611a018466c6119a1846506118a18528260320981e965f4a197d27e5f32797cc865f02797c0945f4ac9792aa5e32c978caa5e3269780545e01317803c5e00d17929e5d32797469e5d0159740545d01397403e5d00f1740365d496170c6e5b31596cc425b3101686565918a9640485800c161e9a574ad15ccac5702d15eaba57aae15d8985649a9592685631a1586685601a15987056aae15529e544a5951286541a7950694549289524a0547ad14d8b4534ad14d29c537a214d2b4524a71492985202d14aab8524ad145e9a504ac14129c50aae14189e4f (Nat.land i 255)
 | 3=>zf 10 23 0x7b5c3266aa334d4c021a9a5334449a686634d0c669a180d3434a067a634cb0039960d0324020648034c8cc518ba5030e320e0a01ec146698100d30100e5fb250be06557a8c7af50145e0640b946816f0d02dd0205bac42b686856d00a2d901a5b032ab4c699688132d06274e204e9b929b2e00725b32c4b094d9386992700aa4c4a6c9603c9280612500924a19448b55c9080692080aa4101448201c904ca92019323d31a47a0408e92b11199022318e4463488880511080322102443201c8618a90bb162164a6c2601e8446990400d2077ac400934800c69000cd20001a400c3e7f869cff3151fd3143f8c4c7e9882fb8cd9f731abeb55c7d0680f98d39f27a63e204c7c4098f80109ef01b3de0327bd298f6a529ea3253d404a7a8cb0f4a509e83253d06427a0c82f41901e83263cc34c79929cf19939e30273c604278c684ef0d69dd02d3ba01c7740a8df8151be62c35602a690c94cf3d619d31a33a93d66d298cd31399262132404e628650c4313186626306c415fd27abf99097f620afc6365f8c54bf0d097eaae2fa94d5f0654be00d17c31aaf43355e803cbd00497a (Nat.land i 255)
 | _=>(0,0)
def kx : z2:=fun qz k =>
 match Nat.shiftRight qz 7 with
 | 0=>qv 0xc6430000318838c010000000000000000000000000000000000c5e0e2d0b16020000c521e280713040000c46180003108586c6c340e1907022b7e4bbc0cdcf46e1996a5ab092d6b66a5435088a763d3616978f4a07a0d14fe227a15346398c5cad664e23234f8cd3c5d261fbd0d4a83eb4181e088effd27f623f711fa06f61c7a043bc51d620e7cd732337e6dbb8ed75a6a06b452d93bcc7c86246b0b1d7d22bbcb5c662d731688caed656252ac155210a6c95225289213e9899584bc3a4f3d22168d1045c32203904ae80c63e291eb18e932734538069be08d3ae694233a41961cc2a25eca2ea316e1cb214535728a413e1c972049c724621153873dc35d016330a530443a1d5309b4025a000c80001 0x1979284d2f24d926b32724d464209ac09c13500d826932a04d0654099d2821328cd426301a04c804c099deb4133190025f02604c402a0998c6a13080a826562d04bc0400980068132250425f32084c8c42098d29c1310d382611a104bc035098005212fa50825e31b04b555c08fe4a0f11b1646536268c9ec491915882ede256425d4a68cb29490960c90f1098d91b31ac84b8356096c6a81288d342421a0a36431d162006c2fe00a81f700f030801208faab83293d646447a684b2c5909612b012b990825631b04aa620161c0842fd80d81f6014246d55c480a4b4101496420392c046d25078518b22d4b134648620bb52959185129ad242505202326bbf46367618c548d38d641a71a6848e341460c63a101016458601b0bf402a07d403c8fa80741f400e03060120942ab811ec940a0a62c84a8c4d390d882d11a5642534a684a494946cccb2128993424e1a40482341281c66c2c580d860001503e601e05f002411e557024f62c849c6582900c98d1118d824d1a00498336092c6681250ca024918a0bfe03605ec03851ad57098e92d031d259063e4b011ac94011f7a21412c59369d89a523b105a144acac2894d09212828d39964209326848e641263869a4f90cda1fe195431431e06380b22c500d85fe01503e401e05e80244bd004417900814772510905e9e1233d2c23b7a29484c4f282189a521b10cce061c948a94f2911296122a50c24449fab6893753d125a121993c24232184106417890c6ecda18ad0e03108482343290067c4f88cda204195c3fa32a862463c45e8c54241027848004a162406c30200ac5fd01503e201e05e00244bc0044177008017a00918f5eb231e3d5463b7a68c7ec5918f98aa11fa56423e4aabc4094376ed26e11e996423c32a847664d6880c6e2bb0d085ee19b03dc32a05d863c31c010863701f0c7403618e406411d00a8239013047001e08dc03431abd3c636627ab62c43553d87e11b253de1f4a1bb9e93f76e926eea8a4cc235327940c6432734c7ed0f98dd9cf319a36262b453cc4e11a0d3c58c1a18c0233708046560c60c7c6300218c5e04218b807e31980dc63201b0c6203308cc05611900a8231013846001f08bc03c117006ccda7a2a9dec397871284cdba4d822d4963c3264276d8c6c8751880cd961ca9dc92d08b0c6e11598ac22a310b43432b236c62aa76b0e5a1c31b0452620686c66c46b8c50cd861ca9d892d7878c6ecdc98ad0eb310845032b089c62af0c250ddb549bb430637189407831300c0226012044a0180882aba10fd5715a67ac8448f4d5609884c5e30e42234ad041e95966752b010a25385994a1331a936083926acbf24d01db4963ae66590888cac8ff1939204326a3fa64c7794c84eb898d5a051acb3de33506506528b70c7422102d0bda05917a40b00fd01385e801b0bd8035179c0680b6804821e6260430c38087526a10e24d01da4960436634086866810c80d0217aae241ef59083d8b2906a50820d49b03c292c47dcc9c8f519081f702703d403608464a2108494011e7a2a42cc4f167589a90ab12d21462199a4c39085929eccea5342154a5842894356c126eaa724cd8d2496a40464347b4c6e8f498d9d75315a176621084c69e0c90d342121a5041234308206829028cdc205195a2d631d235862a101010c57501b83da02b07a40540b580480bb004841ef5a56b9e9c105bd1020e62d041a95a083129c0f024b11f932d3bc664e07e00b40f300d8206aae1c0af5968158b210525681924ac041294e08212986cca50999949b03b292c481ccb48b419611f232723e264c4794c844f80d0a1f019b13003284598638103816816802c03e404e07c40980f280d8166008340af5a5661e9ccec3d119ef62d040a95a166129c0c8a50196749a03b092c47c0cb48f2193a1f01ad13c834e45946380f7816816702003c40340806ab82b9bd642047a68bdac5908092b4101a5602024a70b1a942666d26c0eba4b11f532723d064215c00840f580d80b700403dd2510475e8a100313c1ff62583fcc4307f5882667b0e41fc4a78bd294d07ed2960fd250d5af49baa9a933634525a0fb993c1f732183f263715f8c6c0fc18add9a31503be62107dc69e0fb0d281f51a183e834247b066e8f38cd9d74195ba9432642e462a0f9813c16802683e404307c40820f800dc1ef01582fa01d45a802246a80245ed7ad0bacf4417b18b40f6a5699724a003ac92c07b0cb40f581680b600402392511795e9e6673d145ea6278bd2c4e17798722f4253c5e74a72ad294252e125a0f5193c1e93270bc6643159cc840f318dc1e631583bc62107a069e0f38d385e21a103cc337652464885c0c541e502783c8043078c06e0b380d41e2014a2d201123380120f0b1691e062703c0c42477d2b48ef25381df1ad03bc34207740ac8ee01281dc01f23b6f4f4769e960edb13c1da625ab5ac43552d87e8eba53d1d64a1bade9370764c9e8ec190c1d831b83ae34f15bc6860eb0cdc1d502703a804b474c0848e900fc1d301b03a4033074403c0e7d5701d002d0388058072c09c0e501301c301a037c0080736ab80e701681c102c039004e071c0980e000701bd004038d25107164a008c3d151cc627a388c4d472d8868e53104cca61c839894f071129a0e5a50c1ca4a0b19492d072469e0e08d341c81a1838e341234c62a08bc9441c46270384c38070d29c08b49441c1327037e620070069c8df3d3c1be627837a64f06eeaba0dd55715a57ac9368f4d5605884a5f30e59a54ac836894d660526a0de19681a232c833a65806a4c9c4ca190819b31b03426350668c680ca18a816431082bc62025d46b24c30d3896d1a112e833505d40b20c3013817401a82da02a26e58980dab0e01b949a037063506dcc680ae98809b619a036c03406c6ab80d83d659a562c8368c4d06bd284ec2a4d81b332d0324658069cc9c6ca190819931b22fa6280570c404c50d389891a612dc34206c80b40b5816018302702d402806c24b40d6c9409af7ad3b26c4d95b18820d7a569d6c49b034c65a06b8c9c6c8993019831b02b662026086b44b48d0018202d02d20286695eb4ec9bd3995a7a23302c5a76152b4eb625381a532d132664e0644c800ad18809851ad12d834e06040b40d655701a262c8340636058cc404be0d3817c0270349251068e4a008abd149a86279324c4d269d886664b0e41ab4a7833a94d06a92960d4a50c9a549ba9d292d06a0c9e0c919341a7321834c6370694c56864988498e1a192d033625cc65645a8c5418e02182e602b05a003c05a80241a27ad033ef4406858b40d0196816231012fe35a05fc0b408a49449997a79990f45067989e0ceb13819c625932ec4326458840cb30e419561c033694f066929ca5d24b41993278330643065cc6e0c898d50c8310931a34f25f869c4b38d088b418a831a04f05f809c0b380780b400482272514651e9e663bd141946278326c43631d8720c92538d914a1032293606412588be99389801a702fa04e0632ab80bab16418e32d031e6580638c9c0c698d815931012f434e25e06980b800d80b200402ed251062d89e0c5310c189620831094f061d2960c3250c18549ba9d092d0610c9e0b5993418332183046370604c560be0d3c17c1a1830033605fc6560bf0ca817d18f02c231505f009e0bd812817a02182f204205e00820bb810096601b12e202b22cc0120babd6816f7a202e8c5a05cccb40b9190015831002e235a05c00b4089494416e7a7998cf4505b589e0b6310d8d061c82d694e05a8c9c0b499081681a702ce336059809c0b281081647ad82c695a05892844b099681611ad02c0056057c07c4ae3d3c15e62782bac4b25698860ae253c15b4a182b49372564c9e4ac18dc1591a782b0337055c09c0ab012c95302102aa03605500660a980a8151aae129463405286680a9016813902c028e04e0518098495810013801a025602804940100a7d57014e7ac829a94205400b40988160144027028604c24c8084496010013501a025e02804900100a7496814b928129af5a05352b40a1016813c02c029804e04c0098497010013401a025c028048c0100a52538149194028204e04ec098494010012700e028125104fe4a00873d1410d7a2128ac4f24c589a4a2310c9436209988c39052129e09ca5341474a1828c941539125a0a2993c1313268288643050cc820a118dd0c4310928232a050405409d3d1493d6219986c3904f9286a71a4b413d3218278637430cc4249d8ca813b015021925104e589c09bb0e01384a729c292c042de8a49ab10ccc261c826c94304cd25a09a990c13431ba184621042a4a20993d3ccc17a2826294e04c1284096a4b012f327025c64242fcc40084bd1412c6219980c3904ad286c7124b412a32182526370498c420940ca81270151248f4f049589e092253c1234a18244048248007809080c01200120a2af59147de9a28f316411e4ac822a659047cc9a28e8cd811d19519f203e53ec06487d80988f900d023cc5a145189cc8a310911d4ad223894e044cc6a88918a411d1ad0238342044863c6820138cf8025320804263e007c08d80d811a0188232030440005487f00950f7012120c01e040002407f00340f7006023035a445c69c08b8d081161951a0604e640c08448280a81154ad122694e0451284089a4d89123270224336340809ca8401094fa01f22040360444054088009410f01211fe01e03fc0240870d6810d1ac121434e24246980860d0810b1a002143360424668680813990702122020361409886280b0fc5044a18a0693f042126e083a4cc106321820a63f0410c6e08198cc102315820262713fc08628000dc10001581fe01f13f8c8407f18d84fc02709fa04203f406c07e00a84f97a789f6c4f03ed29e27c250c0fa49b81f264f03e0c6e27b8cd80f7195013a04e13d408427b00d80f601501ea01e1349eb2074b1640f462689a294203a126c06499640e0326817635902e465207981680f202b01e205503c00a8058813847c02108e203e126c06c24600c80990150128025022c04803d807806f00d01de94e03b9298076a5080ec4a001d662803a8650074bd684c77a709d0c5a03a12b426825380c732081a063502f86b605d0d040b002d015405611e409c07381080e601e81ca03c125c06c04b80a807900f01c895a038d2b027125300e231401c232802a40ac06b3d640d262c8192959038129a06a99080cf31b016a35902f469a0598c740df02d01bc05603740aa06e01500af027015a04902a009023e810847201f0938036123406404b00a808901300f001e01d803203680600db32601b46420364c8006c18d00d718e01ad25a1355eb426431340c84a6899c9410354cb406718d80a702b01a804811b007824400c808801300d8018034ccb405301580d27ad0990f4e03458b4063a5040d049a819e65a0338c9c06318a80bc1ad816834112e066a05701680a502b08f404e11b809406681080cc01e819603c126006c24980c448a018012a02a01dc03c06519680a402b0192c5a032189c063b1080c6321014605611c009406280c0087012018865a030ccb006119300c1321018064002fc63805101584b57ac897af4d12ed8b205da5644bc4a1817c93702d4cb205e99340bc31b896434212dc66c05b8ca80b218f08d603e1218064043009806b00d0176c5a12d189c05d31080b94ad017094e02dc6b405b0d080a102b08d404a121007c05aa5680b44a1016665a02c86b4050015848501f095ec4312c5286058990c4ae31b816062b02bc6860570cac4ad92c815a95911d46942490cf809219900ea32612ac09c25601080ac01b015602a12a1e9a251b10c4a261f894a943129127e05524dc0a9499815064d029cc8605318fc0a531b8148633028cc56051189c4a01a1894233702846560500c7c49e021093e036027c05404f007809d0090138f4f026d89e04d24c00993278130643025cc6e04b0d3c09519b8128c5a024d89c0490d5809102d012004e023c098047010808d7a78118c4f022d29c04525080893278110643021cc520430d3c0851a18108337020c09c0410108081020010003601fc03c03f004807d7a780f8c4f01ed29e03d250c07949b80f034f01dc66e03b25680751ab00e805a01cc0840393d3c07162780e0c4301bd29e037250c06d32700d864201ac69e0350cdc06902700d0042019c06c03300a806500900bb25101724a00143d14461627887ac4d118189622fb10c45e6209838c39119129e229a5344634a588c4943510526ea1924cd42049680c864f014cc9a031992c062321b8ac6377124c66c2198ad833313a040621018469e01e8d340601a580be34301786824288cdc848199b0ac32b612464e8208c7d03218d903831510e406e21c00d844f015889c02a013c03e02700780390098070012005001260dbd1541f61cb8aa943710926e80fa4b585531b9036621116408422c010045b01b08b4034016c05402d00a005900f00b001c015c010013c9450567a7a0aaf4b3061e8a02b313c055625a880c4350c587ec0c30e40544a780a694e414928621da50805249bb076936012d25a02524b104f327a09c64e4134c868261909c3731bb860632404cc420288d3cc501a180a033700e865281b0c7481a18a809e04f013809c21b810c43001f009a037013006c01b0048013004804d2514125e9e60bbd14049627b02ec390120c9e40c9884047027208c042011806c0228078044004004b2512105e9e60b3d140436278084c4b20fd886a0f30e40414a7808094300fd26e80b24b403e327807a64e20e8c8401e18dc03b31b007462a00d4c4201a18808391a7907034e20d868441b8cdc81218a807204f00e009c01b80dc036015002400900924a24193d3cc157a28066c4f5075872019253c0314a1a02a92d20c0c6c0180cd802f027005c04c20ac084415010002d01b005803400ac05401500a00290041850f4f50a189ea12b10d42461fa05094f709d286e1324fd82549bb04893320a0c9e413990c82631fb04e6376098c6681298ad024313805034f10946862120cfc42719b884c333009c6560130c9c02518f804831b308c08461100fcc2101f28460365088066a1080c90230152044027408404c411807882200d904201a008c024011003c0210070838f4f106de96210313c41f625882cc43105587e010253c01f4a58830943105d27e00f24dc01d499803864f006cc9600d190c01931f8030637005cc6600b18ac015313802834f10486862098cdc013195802431f004409c008012c00f0250816042102807e20480f840e01b081a033103006400700a800d0138018026002c03c005006c00900d0004f453021886603b0fcc0161ca810943501d27ea0224dd403499a80292d4020c8680398fdc0631bb80a6336010c56c01989d0013109010343201c67e4030cdc805199b00c32b601464e8020c7d00318d9002315002008600380fc40401b88060331018056202809c00600f800a01b0010026001803c001004800003f 17 0x1ffff 6 0x3f 27 0x7ffffff 13 0x1fff 0x3ff 23 6 (Nat.land qz 127) k
 | 1=>qv 0x9620000009429229110000009010000008e20000000000000000000000000000008b38928818710000000000000000000000000000000000008618420000008220007e47a40000007460000007220000007116f26e10000006d16c16b16a16826710006616516416310000006216110000000000000005f20000005b45a15820005440000005044c40004a20004824714614334210000004110004010003d33c10003a20003643513232c62b12562411e61c21751250a8028011001 0x3574a10ab4ca055d8b46ac034156b2709ac138558c842ab954352ca10aa810853869e2a904ed2f0090aa01505320902a704a14c0251a0c098d4c06c2a602a15282a0a900c052c09066703e1518181a1009052a0ac66603c1510181a0809054989c2a364e1513210a6cd3c54208425e0121500240a0409053e08429e05414a0240a7412852609429204a14e01e0a68c7053607868003014382a19940f85200ac67f03214782b0a68d305346982870301440120a66560d3129829862814b8140a598d8d2b28229563614b32c0a55938d2066a68e03414a32c0a4d90052463829101c1484a70a3cd0851a05026b0101473210a34074cd605426b01e145c980a3255051788628a6431449a18a2a4c051326028604014419a0a1413050e0202870541434a70a1412850928028364113d02c09e41004e608027803613901a49ac04850989c28164114131a8a00d3c4fc09d26a0121388200a0fd6850329828294013e82d09b01304ee0802819421404a109fccd84f809827604213782009ac040cbc09827504013f9ad09ec1684da099a5e04013500809eb1344fcc6c27d33713e02089ec0ac4f5e9c279c4e13c32709b0d044ee66a27604f32f02089d40d44e988627394313932109c4d0c4e066e26f04313701b89b40af4bc06a26c642 12 0xfff 4 0xf 25 0x1ffffff 12 0xfff 0x3ff 22 4 (Nat.land qz 127) k
 | 2=>qv 0xe35ee9b6c5b03000672b289658b10d806bc35c1aa2540a984000a224f8e783325923c522188fe7774381db460006a1b310000be75e08000000000000000000000000000017040000000000000000572a9140000004e225112048c244100000008423c31c100000003611a08c465e200000000000000001688a8600026212088463e21c18000684302161098c4441e20e0858c2060e1060820808400000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 0x30e620861a93d1c2926c18619082e51a686123290c1409418081082ff02085ea0402b7006c185b10430a31b061262a0c2068418001082f4020060f55c0bdc080183253430519506080342b8929a58124d430331a85c43410c0866a17b80d4b00015060201e0c0002416980242ff19505ee0422bbc05454d0020af37a285eec430bf987e179b0e4afa4a195c29412bed26e57e990cafc31f85fa6370bf0c6657c18ac2fb1a185f43370b8466a17c8cac2f818f85ee0430bdc06e57a00a82f600f85ea01e0bd002416900242f31a605e46580bc4c6817931602f262705e294e2bc069c1780138af019a05de04c0bc066817781302ed32c05d86402b6c0b056d01002ee32605ce3580b9866817599002ea31b05ca32a0b8808417081002db01b05dac4d0bb92821748d082e419505be0420b7808016d00d82ed7a705d8c4e0bad26a17519382e81a705c632a0b7409c16c80d02e74a685d23420ba066c16c00d82e762705cc94e0b94c9c1720d382e31a105b804e0b5c08456db1342e232105c26400b8069c16f8d082de1a005ba3360b7005456dbd38ada62705b664e0b6869c16c8cd02d802705ae02a0b5528016b01802d101e05aac5a2b50cb416a0d682d431b05a634e0b4869816800c82d17ad15a065a0b406b4167816825e0140cea01c89d40201670150acd014059a01c0b000b01660130abe02005840340af805015e01602cb026057e0402af406816080a02c902105900402ae006815b80702c702105860402ad806815b0040aca19405940282b2465016480a0ac819405900280b3189a16598d82c07ac0598f4c2af18b0565b1302bc32c059664c0b28c9c16499082c8320058e01c2b1065016200a02c6626858a6360b19e9c562b1382c532705886420b0c03816131342c131b0584f4e2b0589c16099382c04ac157e9400af8cb015e99002c062685786360b01e9c55fb1382bf327057cc4d0afcc6c15f3d382bd627057864e0aecc9a15d18d42b8194056e0280aed89a15c98d82bb7a70574c4e0ae4c9c15c19082b600e056e6420ad803815a81282b402a155e03c0abc0481598150ab001e05620300ac80a8159250cab162185629430ac1886157a50daae019255a018 13 0x1fff 5 0x1f 27 0x7ffffff 13 0x1fff 0x3ff 23 5 (Nat.land qz 127) k
 | 3=>qv 0xf7273c3983ca1e21f084000000df10003555a81d0263a6fd1726b61da86cc560300052ae8c52ec00047a224c0007f50000000fc17d0bc91d0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000730b90400000000000000000000000001b880006d08001a86cc40000001904c61620b084000c015d1ae04000b420002c85602000570a8992cc9414149d98e060000000000d46681321161800056100014880004e22320da06442e2151090c4421e20a2840808c002 0x38098d132c1ac26763407ca86681a130f87274a0ce1e9351bfcc6c19f18d46f531a3e2a62a0d0469c19e8cf932919b3e623357ca066819b8134f3501a861601d4bb80221a0315033f3140e5b2586c30c5019d8d0033e626067ac410cf066c996253533b49a86586410cecc6a3860ca9f0c18f25d204d0ba408219c80d4308008867555c4ba46b019c8d0030000e25be0100cdd89a38718d9b15315067034e4c9866c19b00d833501505e801c4b7802019bbd30f3562606146403b70c689720d00f2319a05b00580cd8098173b1603254ac06126346b98c5019a81312da00806680420ccc06c19900c9af262c066294c7bc0c68396b16032d32c3de26341b9d89a198252832f3250e586425bb4c6c3928cd832e025064e0410b9405219200752ea0088e5294c0cb4cb0f92313432c4a1065664a0ca8c8419499043283202dd86361b9866c974013432602085c80296c8c03a173b161b244ac064e64c4ba06b01930d302dc01a06460284b74020b71a5306d732025c634c1c8868016b80d03220143648c4e5b8d884192a5383243270dc66426c8c69cd910d0832302706440428b6402019000c832102b264294e0c8468414680a128d008064035a0c7c0b4d2f00d031e00e3cc00100c740a818e0151af849a062a6344c2cc5017700a0b120201e286582bb468017680a1309320161e34c2bb06681750160b0732d060e35a0c6d29018db1602f292c05d201c3c51eb05740cd02e800e0628c582c6808418d00a82d531005e4c580c6189058a3134b19625062864d0c64c945738cd82e700f0630f582c5d89818b256031731a161a3580c340b01793160b15620862c93d5c2526c18a9905b0931496183422b9866c18601082e600f0628c580c5529898518d0b0e1a605ca0580b90038189b130ae31a005c601c0c512b0d84a4d130b326062694c3c5189a18a25343146270626c426c2529c985193a30a1a7061204e0bc929a1793160aff1a615f60402b800687800cd0ae202c16040402b7c06818824d430f31a9de83340c386541858c7831202715c204c2b7806818301202fd02006223280bf00981860ca03030200620c4c1c2868057c01302fa020061031c0c08080187b1302ea32c06143400be409856e80d030919a05f004c3c0128477a250070a31a86143352c0008457a01002d418a05ec04c 13 0x1fff 5 0x1f 27 0x7ffffff 13 0x1fff 0x3ff 23 5 (Nat.land qz 127) k
 | 4=>qv 0x9e10000000009d19c10009b10000000000000000000000000000000000000000000009830009539410009318f48e18d18c18b10000008838267f37877447136c56936636336216025d35b25925725255110000004f24e14d14944720000000000000000000000004610000000000000000000000000004513e73d13763523320000000000000000000003213112e32b32920002540002410002312210000000002021a61731611060d3094000000081008 0x1b58cd436b62706d402a0da809cd79496076962a06d23480d664a01b4a53474001506d001c0d9cc6c3afb13036732c0e220400cf003839f80d128702a16923340bca4b01af193433a195060e31e6d54cb0da918d03661a02e603340d8c6501830071b554a686ca3341d1c0541ac49403664a686ca34c2d68680daa0ca874301506080105cc12b05ae0d3074501a0e880285cc129a5ad8d0036401506af2500d8d29a5ae8d01b531950e8c02a0d880781b080c036001236763285cec050181804130218e067201c0c0802017f004234119405fa0100d7c65039e80d02fc008067001c0bec0211890c702fa00806bd55c0bdc0211a10ca835d01a06b802a0d6c0501ad007035932a06b064c0d5cc681798c7073301b3ea09421cc866c13e013035602036a23361cd006c5a41909f4f31badf2c403c39280d8724d1f2732c3e4c6401c9c09839300d035532406aa9586c152681aa190035318e06a40581cac0681a90d213411a006a20280d400181a7812034e00e069ac540d312901a58d2034c62c065e0340cc0050d79496072c0142696c4d0d2d29a99718d832e015069401e4cf8c98d7931612e218e05c40104c9cc6c59b8cda33719525c231c0c9c05417080403491a626703404b800201a400d031462c35ce9588cdc69896d8c702e501a06480283bfd280f9499006ef0200de4c4d6bc929a99698d832d015068ec480d1deb01a13d3034649a0e0a6400d14c689958d0034419a0686034 12 0xfff 4 0xf 27 0x7ffffff 13 0x1fff 0x3ff 23 4 (Nat.land qz 127) k
 | 5=>qv 0x31200005ced361accf2540000002431988c26020079001d20070b6594c1002c8000054a6914813c954924100000720015000340a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 0xdec0396ea94c3751a01bc80d0de00506f525036e0045ba2506de0c546e803537800e9bc8ca8de063c6ee0403770141bb0ca0dc80696e204c3750201b880a0dc00506ec3403740201bb1900dcc0806de0343751951ba0078dcc03d6e294c3751a01ba0d00dcc0806e23283724a61b9310adc52846e23423700211b78078dc00506de03436e1a61b70ca8db404c6da34c36c0265b60d30db00986d4040 9 0x1ff 3 0x7 25 0x1ffffff 13 0x1fff 0x3ff 23 3 (Nat.land qz 127) k
 | 6=>qv 0xc2efabc6e900000002dab46c9aeab1aa40000000002a1a127298800000000000000000000000025992a418e61c7f00000000001f17a5e1001d9001ca6b19a0000000191000000000000182000005914b4cd29469033ac0000000000000000000000000da328ba00000000b12a49a20c791c46916851124410e431088190440900400 0x6e3cd31b8e3280dfc041b8f6411e30078b900406e34ca037b0281e1c07037a31c8e2c07a38a0288e2407039001e8e2007838f6340e3d931b7e6280e381307850280e341307860280e38cd038d0100e300d038b9404e18ca038a9400e2650038c94c0e2250077e3284e140a038b9340e298d03893340e200d03873340e1e501b7d31c0df0040f746343e10cd03793343dccca13730343e0c0a03783286dd8c71b776280e198d038501c7e124d477632a6e1010437601d0dd00a038401c4dd4041b846400dcc0a038301c8dc80403840404dc40403843408dc01303830401dbccd236f0400e080d038164c2e00d30b819400e058a1b786280dd807037b0401de4cd0f783342dd41307799342dd0130b730340e0250037d0343de18d0f789400de41003780400df00d037a34c0dfc0d037e0340dfd90437e01e0df407037c0100df4cd037c034 10 0x3ff 3 0x7 26 0x3ffffff 12 0xfff 0x3ff 22 3 (Nat.land qz 127) k
 | _=>k (fun _=>none)
theorem q0k : z1 kx:=by
 intro qz k h
 unfold kx at h
 split at h <;> first | exact qt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h | exact ⟨fun _=>none,h⟩
def q1Y : List qb:=zk kc 0x379218606c8de2d01101c847103102422ee9863045dc84e000822117841a0533022e1a449283082b4e30440d01732384e435055207c1e88063a0d3f812c031d2c841c81e634256a12d0c432f52b 0xca210000001000001c0060000620140cd8630c4466c6400000709340c247302663020364300000803219601722386b0034110a424000450a5033872803010c6800020500494c18918011f123 103
noncomputable def q6w:=qG j4 103 q1Y 11 kR
noncomputable def q4d:=zx j4 kc 11 1 kR
noncomputable def q1c:=qr j4 kc 11 1 kR
def kv (a : Nat) : Option z0 :=
 if Nat.blt a 10 then
  match a with
  |1=>some [q2C,q2B]
  |2=>some [q6F,q2A]
  |3=>some [q6D,q2C,q2A,w2]
  |4=>some [q6E,w2]
  |5=>some [q0o,q2C,q2B,w2]
  |6=>some [q0o,q0n]
  |7=>some [q6E,q6C,q2A,w2]
  |8=>some [q6F,q0n,q2B,w2]
  |9=>some [q6D,q6C]
  | _=>none
 else none
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5e : qP j4 ud 64 kv :=
 qs
  (sel:=fun a i=>Fin.ofNat 64 (qe 6 (z3 0xa0a7288d1a446ac053a888eb80aad112a701a53800000 18 a) i.val))
  (inv:=fun a i=>Fin.ofNat 64 (qe 6 (z3 0xa0a72b444a888ec053a446ab80aa2346a701a53800000 18 a) i.val))
  (bound:=10)
  (by intro a ha;unfold kv;rw [show Nat.blt a 10=false from by cases h : Nat.blt a 10;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def wq : List q2:=[q86,q85,q81,q84,q4c,q83,q6u,q49,q6v,q6t,q4b,q82,q4a,q8O,q48,q6s,q8S,q8I,q8Q,q8G,q8M,q8E,q8K,q8A,q8C,q8y]
theorem q5d : qu wq:=q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q8x.1 q8x.2) q8B.1 q8B.2) q8z.1 q8z.2) q8J.1 q8J.2) q8D.1 q8D.2) q8L.1 q8L.2) q8F.1 q8F.2) q8P.1 q8P.2) q8H.1 q8H.2) q8R.1 q8R.2) q3W.1 q3W.2) q1T.1 q1T.2) q8N.1 q8N.2) q1V.1 q1V.2) q6n.1 q6n.2) q1W.1 q1W.2) q3X.1 q3X.2) q3Z.1 q3Z.2) q1U.1 q1U.2) q3Y.1 q3Y.2) q6o.1 q6o.2) q1X.1 q1X.2) q6p.1 q6p.2) q6m.1 q6m.2) q6q.1 q6q.2) q6r.1 q6r.2
def q4f : Nat → Nat:=fun i =>
 match Nat.shiftRight i 6 with
 | 0=>y9 0x20a00000065940000186b28000000d650001632b50000000b4140000182558000002c65000000015a00001624140000000b2e1883105650000000350000000b0a00000006b400000001a8000101134a00020226940000000d400008089a5000000585000020226970c41b4480801862082300018610ca0002c8340400c5988328000b10d010030c4104600001a508c00002da508000620c2b00000178ca0003c615a0000205a62800041882d00010158ca00000000ac0000082d28000b20c280000020b4a00000080940000202458000069461000000010a0000002597166209a50800000006100000000478b30c4d2840000002f28000043ca4c59883694200000082ac00002d05100186208610001ab28c20c310620940006ac880e18831056500000d1202000000000c0000000008000000000 39 (Nat.land i 63)
 | 1=>y9 0x1000000000000000000000000000000006000000000040000000000f00000000008000000000000000000000600000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000200000000002000000000000000000000000000088da500000000e2500122c3582500001130d650000030962b0bc566208230000001056500000000061000186208610000000346500000b0b46500000002c6500000d58465d618825946100030f40cad00000000da8000000001a50000001346500000002c65000000001a500000000105000000005a500000003065000000001a50000047a1a5000000000050030c4188250000000202f00000002d05000168091a5000000001a800000002d05d618625910100001868d6800000003468000000001a500000030d65 44 (Nat.land i 63)
 | 2=>y9 0x20a00000000000000000040002000020000400002000140000000080000000000000200008000000002000000000000000000000000000000000000000000000000000000000000000000000006000080000000000000deb30400018000f0000000000000400000000000000000000000f003ca0002000000000000008000100000000000000000000000000000000080003e085780001 19 (Nat.land i 63)
 | 3=>y9 0x400000001000640002010080402000000000002c4d46a01000000000000040201008040000000000000000000001000040000000000000200828201105 9 (Nat.land i 63)
 | 4=>y9 0x6a0161404428003500059400d4001a800000006a0161400d050000000014161400c2805850030a000058144d003500b0a00614001a800350005940061800830001e0208fcc20810410000000000000000000000000000000028000000000000000000000000000000000000000000000000000000b280000000000001400b28000000000000000000000000000000000000000004 19 (Nat.land i 63)
 | 5=>y9 0x28c00103000014000020000ac0000500208c00165823594000000000ac000a100001800d65000028000650000000000b000010000a4000014000c50062ac001650005940000500059400000000000000c500001400000000000000060000000000500003c000080000140000600031400000000000000000003140000000000000002000000000c500002c000000000000010d0006a000008000020001a80000140000500b0a0000110006a000000 22 (Nat.land i 63)
 | 6=>y9 0x5a000c300188000f0000000000d1a000000d1a034680000000040000000050000000c500194000000000000500594000000018000500014000f0002000000001401640028c00680000001650003c29050000e88230005800cf00014000000000000500014000d0006800050659400020208c00000002c000b0002c006b0000c001800008000500014000200008000b 18 (Nat.land i 63)
 | 7=>y9 0x30800c28f4d1b0a00006400000880002900060ca000065000002800009400000ac31023000002800001400000a000163000002000000400001000000a00003280003140001100001440598a2800001000000a0000ab000022800b1140000000000000000000000000000000000000000000000000000000a000000000000000000000000a000000000000000000000000a000000000000000000000000000000800000400080bc00000a000005001682800000000000000050f0010178000414005a0a002d05 25 (Nat.land i 63)
 | 8=>y9 0xb00346500346500000b00000d002c6500000db4102300082300000600018200000600030f000000000000003468000000003468003468003468003468000005000000000005000008000088000005002d0500000000000000000b00000500146800000d0000000000000000050000050000050000000000080000a10001a5000005000000000064 24 (Nat.land i 63)
 | 9=>y9 0x628005415600000f1800502de0520000800b0196000c002800558c20594b158148895712ac0000025000a00140158061000a00140008cab 15 (Nat.land i 63)
 | 10=>y9 0x18280a0b6281417a8d46a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 9 (Nat.land i 63)
 | 11=>y9 0x2000500ac0000004005000000000000a3a40c005000000f000c0030004004001800b0290002001000f003c0000020000033c002001400100000050000000002c001611400f0514000000000000140050000000000000000000c5002c000000010d06a00c5002c10d06a0008000c0c5 14 (Nat.land i 63)
 | 12=>y9 0x3000050000000000000a40000500005000050000100000000000000000000000000000400008000080000800008000cf000040000400004c594500002000000000b00008000050016500000000000000000000000000000000000000000000f000000000000000000160000b0000300001000030000000000000000000a00003000000000300003000030000000001000010000b00000000050000300003 20 (Nat.land i 63)
 | 13=>y9 0x1800300000000000000300000000000000000000018005800f028a00000000000000000000b200000000002c0020003001600000000000000200000558000015602ac0000000000000000010000000007980000000000000000d5800d0016000000280000000000c0018003000600034c68003 15 (Nat.land i 63)
 | 14=>y9 0x800f003c000000000000000000000000000000200021450000000 14 (Nat.land i 63)
 | _=>0
noncomputable def yu:=qO 2 false true j4 ud q1d wq (some q4f) 913 kR q4d q1c kv kx 103 q6w
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5c : qT 2 false j4 ud q1d (qk true wq) q7j 913 kR q1c kv kx kc 11 1=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q87 : qE 0 256 yu=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q6z : qE 256 256 yu=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q6y : qE 512 256 yu=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q6x : qE 768 145 yu=true:=by decide +kernel
theorem q4g : qE 0 913 yu=true:=(@vX 0 512 401 yu (@vX 0 256 256 yu q87 q6z) (@vX 512 256 145 yu q6y q6x))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1b : qo j4 kc ud 1 12 :=
 zm (root:=q1Y) (sample:=q4e) (hints:=(some q4f)) q5e q0k q5d q5c q4g
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q4y : q2:=(0x3333333333333333,[0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000],8,9,0x3333333233323000)
theorem q26 : EL q4y 8 9:=qh (qa 64 32 [0,2,3,4,5] 0) yo yn (by decide +kernel)
def q4x : q2:=(0xf0f0f0f0f0f0f0f,[0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000],8,9,0xf0f0f0e0f0e0808)
theorem q25 : EL q4x 8 9:=qh (qa 64 32 [3,0,1,4,5] 0) yo yn (by decide +kernel)
def q4z : q2:=(0x5555555555555555,[0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000],8,9,0x5555555455545040)
theorem q27 : EL q4z 8 9:=qh (qa 64 32 [1,2,3,4,5] 0) yl yk (by decide +kernel)
def q4w : q2:=(0xff00ff00ff00ff,[0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000],8,9,0xff00fe00fe00c8)
theorem q24 : EL q4w 8 9:=qh (qa 64 32 [0,1,2,4,5] 0) yl yk (by decide +kernel)
def q4v : q2:=(0xffff0000ffff,[0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000],7,8,0xfffe0000f8c8)
theorem q23 : EL q4v 7 8:=qh (qa 64 32 [0,1,2,3,5] 0) yU yT (by decide +kernel)
def yz : Word:=0xffffffffffffffff
def kY : Word:=0xfffffffefffef8c8
def jg : List Word:=[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def wY : Option qw:=some ⟨[3,6,12,17,18,20,24,33,34,36,40,48,5,9,10,16,32,5,5,5,5,5,5,5],rfl⟩
def q5m : List zW:=[(0xaaaaaaaaaaaaaaaa,3,2),(0xcccccccccccccccc,3,1),(0xf0f0f0f0f0f0f0f0,6,2),(0xff00ff00ff00ff00,12,4),(0xffff0000ffff0000,17,1),(0xffffffff00000000,33,1)]
def q2I : qH:=(0x28300a1102884100c048441221010480422100844022100904028020180a030480c120c0500c1406080482014100c00221080c002110804420180203004060100c0203,30)
def jG : zj:=fun i=>zf 1 13 0x310e07e i
def kZ : z2 :=
 qv 0x19 0x710c03f 3 0x7 1 0x1 14 0x3fff 12 0xfff 0x1 13 1
theorem wx : z1 kZ :=
 qt 0x19 0x710c03f 3 0x7 1 0x1 14 0x3fff 12 0xfff 0x1 13 1
def q0u : List qb:=zk jg 0x25f00e012800ef09011006240a540c034ee01db21a163 0xf008000000cb01c03c00380300080300c01bb01c141 30
noncomputable def q4B:=qG yz 30 q0u 9 jG
noncomputable def q2H:=zx yz jg 9 0 jG
noncomputable def wX:=qr yz jg 9 0 jG
def ju (a : Nat) : Option z0 :=
 if Nat.blt a 4 then
  match a with
  |1=>some [q6B]
  |2=>some [q0o,q0n]
  |3=>some [q0o,q0n,q6B]
  | _=>none
 else none
theorem q3q : qP yz kY 64 ju :=
 qs
  (sel:=fun a i=>Fin.ofNat 64 (qe 6 (z3 0x9414ec05395a200000 18 a) i.val))
  (inv:=fun a i=>Fin.ofNat 64 (qe 6 (z3 0x9414ec05395a200000 18 a) i.val))
  (bound:=4)
  (by intro a ha;unfold ju;rw [show Nat.blt a 4=false from by cases h : Nat.blt a 4;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def ut : List q2:=[q4y,q4x,q4z,q4w,q4v]
theorem q3o : qu ut:=q1 (q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q23.1 q23.2) q24.1 q24.2) q27.1 q27.2) q25.1 q25.2) q26.1 q26.2
noncomputable def q3p:=qO 2 false false yz kY wY ut none 2 jG q2H wX ju kZ 30 q4B
theorem q3n : qT 2 false yz kY wY (qk false ut) q5m 2 jG wX ju kZ jg 9 0=true:=by decide +kernel
theorem q6M : qE 0 2 q3p=true:=by decide +kernel
theorem jh : qo yz jg kY 0 10 :=
 zm (root:=q0u) (sample:=q2I) (hints:=none) q3q wx q3o q3n q6M
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q7s : q2:=(0xffffffff,[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],7,8,0xfffef8c8)
theorem q7r : EL q7s 7 8:=qh (qa 64 32 [0,1,2,3,4] 0) yU yT (by decide +kernel)
def yy : Word:=0xffffffffffffffff
def kW : Word:=0xfffffffefffef8c8
def je : List Word:=[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def wW : Option qw:=some ⟨[3,6,12,17,18,20,24,33,34,36,40,48,5,9,10,16,32,5,5,5,5,5,5,5],rfl⟩
def q5l : List zW:=[(0xaaaaaaaaaaaaaaaa,3,2),(0xcccccccccccccccc,3,1),(0xf0f0f0f0f0f0f0f0,6,2),(0xff00ff00ff00ff00,12,4),(0xffff0000ffff0000,17,1),(0xffffffff00000000,33,1)]
def q2G : qH:=(0x2050082404060102802834120b04834140b028300a1102884121104884100c1008440221009040280280c1203048301403050180412010880806100c020120805020300804420180088402110203004060100c0203,38)
def jF : zj:=fun i=>zf 2 15 0x49479286c43587280fc i
def kX : z2 :=
 qv 0x900e1 0x124a2725097a29310c5872003f 5 0x1f 2 0x3 17 0x1ffff 13 0x1fff 0x7 16 2
theorem ww : z1 kX :=
 qt 0x900e1 0x124a2725097a29310c5872003f 5 0x1f 2 0x3 17 0x1ffff 13 0x1fff 0x7 16 2
def q0t : List qb:=zk je 0x502bc0a482814004fd03f844801232a122920c050137d01c3de8d00b3 0x3c020000000007c0371c1e000323808100801000780183be0e0031 38
noncomputable def q4A:=qG yy 38 q0t 10 jF
noncomputable def q2F:=zx yy je 10 1 jF
noncomputable def wV:=qr yy je 10 1 jF
def jt (a : Nat) : Option z0 :=
 if Nat.blt a 4 then
  match a with
  |1=>some [q6B]
  |2=>some [q0o,q0n]
  |3=>some [q0o,q0n,q6B]
  | _=>none
 else none
theorem q3m : qP yy kW 64 jt :=
 qs
  (sel:=fun a i=>Fin.ofNat 64 (qe 6 (z3 0x9414ec05395a200000 18 a) i.val))
  (inv:=fun a i=>Fin.ofNat 64 (qe 6 (z3 0x9414ec05395a200000 18 a) i.val))
  (bound:=4)
  (by intro a ha;unfold jt;rw [show Nat.blt a 4=false from by cases h : Nat.blt a 4;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def ur : List q2:=[q4z,q4y,q4x,q4w,q4v,q7s]
theorem q3k : qu ur:=q1 (q1 (q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q7r.1 q7r.2) q23.1 q23.2) q24.1 q24.2) q25.1 q25.2) q26.1 q26.2) q27.1 q27.2
noncomputable def q3l:=qO 2 false true yy kW wW ur none 5 jF q2F wV jt kX 38 q4A
theorem q3j : qT 2 false yy kW wW (qk true ur) q5l 5 jF wV jt kX je 10 1=true:=by decide +kernel
theorem q6L : qE 0 5 q3l=true:=by decide +kernel
theorem jf : qo yy je kW 1 11 :=
 zm (root:=q0t) (sample:=q2G) (hints:=none) q3m ww q3k q3j q6L
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def q9U : q2:=(0x55555555555555555555555555555555,[0x44444444444444444444444444444444,0x50505050505050505050505050505050,0x55005500550055005500550055005500,0x55550000555500005555000055550000,0x55555555000000005555555500000000,0x55555555555555550000000000000000],10,11,0x55555555555555545555555454544400)
theorem q9T : EL q9U 10 11:=qh (qa 128 64 [2,4,1,3,5,6] 0) jh jf (by decide +kernel)
def q9K : q2:=(0xffffffff00000000ffffffff,[0xaaaaaaaa00000000aaaaaaaa,0xcccccccc00000000cccccccc,0xf0f0f0f000000000f0f0f0f0,0xff00ff0000000000ff00ff00,0xffff000000000000ffff0000,0xffffffff0000000000000000],11,12,0xfffffffe00000000fefceea0)
theorem q9J : EL q9K 11 12:=qh (qa 128 64 [0,2,4,1,3,6] 0) q1e q1b (by decide +kernel)
def q9I : q2:=(0xffffffffffffffff,[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],11,12,0xfffffffefefceea0)
theorem q9H : EL q9I 11 12:=qh (qa 128 64 [0,2,4,1,3,5] 0) q1e q1b (by decide +kernel)
def q9S : q2:=(0x33333333333333333333333333333333,[0x22222222222222222222222222222222,0x30303030303030303030303030303030,0x33003300330033003300330033003300,0x33330000333300003333000033330000,0x33333333000000003333333300000000,0x33333333333333330000000000000000],10,11,0x33333333333333323333333232302220)
theorem q9R : EL q9S 10 11:=qh (qa 128 64 [3,0,2,4,5,6] 0) jh jf (by decide +kernel)
def q9Q : q2:=(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,[0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0xf000f000f000f000f000f000f000f00,0xf0f00000f0f00000f0f00000f0f0000,0xf0f0f0f000000000f0f0f0f00000000,0xf0f0f0f0f0f0f0f0000000000000000],10,11,0xf0f0f0f0f0f0f0e0f0f0f0e0e0c0e00)
theorem q9P : EL q9Q 10 11:=qh (qa 128 64 [0,3,1,4,5,6] 0) jh jf (by decide +kernel)
def q9O : q2:=(0xff00ff00ff00ff00ff00ff00ff00ff,[0xaa00aa00aa00aa00aa00aa00aa00aa,0xcc00cc00cc00cc00cc00cc00cc00cc,0xf000f000f000f000f000f000f000f0,0xff000000ff000000ff000000ff0000,0xff00ff0000000000ff00ff00000000,0xff00ff00ff00ff0000000000000000],10,11,0xff00ff00ff00fe00ff00fe00fc00a0)
theorem q9N : EL q9O 10 11:=qh (qa 128 64 [0,2,4,1,5,6] 0) jh jf (by decide +kernel)
def q9M : q2:=(0xffff0000ffff0000ffff0000ffff,[0xaaaa0000aaaa0000aaaa0000aaaa,0xcccc0000cccc0000cccc0000cccc,0xf0f00000f0f00000f0f00000f0f0,0xff000000ff000000ff000000ff00,0xffff000000000000ffff00000000,0xffff0000ffff0000000000000000],10,11,0xffff0000fffe0000fffe0000eea0)
theorem q9L : EL q9M 10 11:=qh (qa 128 64 [1,3,0,2,5,6] 0) jh jf (by decide +kernel)
def q9i : q2:=(0x11111111111111111111111111111111,[0x10101010101010101010101010101010,0x11001100110011001100110011001100,0x11110000111100001111000011110000,0x11111111000000001111111100000000,0x11111111111111110000000000000000],8,9,0x11111111111111101111111010100000)
theorem q9h : EL q9i 8 9:=qh (qa 128 32 [3,2,4,5,6] 0) yo yn (by decide +kernel)
def q9a : q2:=(0x3030303030303030303030303030303,[0x2020202020202020202020202020202,0x3000300030003000300030003000300,0x3030000030300000303000003030000,0x3030303000000000303030300000000,0x3030303030303030000000000000000],8,9,0x3030303030303020303030202000200)
theorem q99 : EL q9a 8 9:=qh (qa 128 32 [4,0,3,5,6] 0) yo yn (by decide +kernel)
def q9c : q2:=(0x5555000055550000555500005555,[0x4444000044440000444400004444,0x5050000050500000505000005050,0x5500000055000000550000005500,0x5555000000000000555500000000,0x5555000055550000000000000000],8,9,0x5555000055540000555400004400)
theorem q9b : EL q9c 8 9:=qh (qa 128 32 [2,1,3,5,6] 0) yo yn (by decide +kernel)
def q94 : q2:=(0xf000f000f000f000f000f000f000f,[0xa000a000a000a000a000a000a000a,0xc000c000c000c000c000c000c000c,0xf0000000f0000000f0000000f0000,0xf000f00000000000f000f00000000,0xf000f000f000f0000000000000000],8,9,0xf000f000f000e000f000e000c0000)
theorem q93 : EL q94 8 9:=qh (qa 128 32 [0,1,4,5,6] 0) yo yn (by decide +kernel)
def q9e : q2:=(0x550055005500550055005500550055,[0x440044004400440044004400440044,0x500050005000500050005000500050,0x550000005500000055000000550000,0x550055000000000055005500000000,0x550055005500550000000000000000],8,9,0x550055005500540055005400540000)
theorem q9d : EL q9e 8 9:=qh (qa 128 32 [1,4,2,5,6] 0) yl yk (by decide +kernel)
def q9g : q2:=(0x5050505050505050505050505050505,[0x4040404040404040404040404040404,0x5000500050005000500050005000500,0x5050000050500000505000005050000,0x5050505000000000505050500000000,0x5050505050505050000000000000000],8,9,0x5050505050505040505050404040400)
theorem q9f : EL q9g 8 9:=qh (qa 128 32 [3,1,4,5,6] 0) yl yk (by decide +kernel)
def q92 : q2:=(0xf0f00000f0f00000f0f00000f0f,[0xa0a00000a0a00000a0a00000a0a,0xc0c00000c0c00000c0c00000c0c,0xf0000000f0000000f0000000f00,0xf0f0000000000000f0f00000000,0xf0f00000f0f0000000000000000],8,9,0xf0f00000f0e00000f0e00000e00)
theorem q91 : EL q92 8 9:=qh (qa 128 32 [0,3,1,5,6] 0) yl yk (by decide +kernel)
def q96 : q2:=(0x3333000033330000333300003333,[0x2222000022220000222200002222,0x3030000030300000303000003030,0x3300000033000000330000003300,0x3333000000000000333300000000,0x3333000033330000000000000000],8,9,0x3333000033320000333200002220)
theorem q95 : EL q96 8 9:=qh (qa 128 32 [2,0,3,5,6] 0) yl yk (by decide +kernel)
def q98 : q2:=(0x330033003300330033003300330033,[0x220022002200220022002200220022,0x300030003000300030003000300030,0x330000003300000033000000330000,0x330033000000000033003300000000,0x330033003300330000000000000000],8,9,0x330033003300320033003200300020)
theorem q97 : EL q98 8 9:=qh (qa 128 32 [0,2,4,5,6] 0) yl yk (by decide +kernel)
def q7I : q2:=(0x110011001100110011001100110011,[0x100010001000100010001000100010,0x110000001100000011000000110000,0x110011000000000011001100000000,0x110011001100110000000000000000],6,7,0x110011001100100011001000100000)
theorem q7H : EL q7I 6 7:=qh (qa 128 16 [2,4,5,6] 0) km kl (by decide +kernel)
def q90 : q2:=(0xff000000ff000000ff000000ff,[0xaa000000aa000000aa000000aa,0xcc000000cc000000cc000000cc,0xf0000000f0000000f0000000f0,0xff00000000000000ff00000000,0xff000000ff0000000000000000],8,9,0xff000000fe000000fe000000a0)
theorem q8Z : EL q90 8 9:=qh (qa 128 32 [1,0,2,5,6] 0) yo yn (by decide +kernel)
def q6d : q2:=(0x101000001010000010100000101,[0x100000001000000010000000100,0x101000000000000010100000000,0x101000001010000000000000000],4,5,0x101000001000000010000000000)
theorem q6c : EL q6d 4 5:=qh (qa 128 8 [3,5,6] 0) zI zH (by decide +kernel)
def q6f : q2:=(0x10001000100010001000100010001,[0x10000000100000001000000010000,0x10001000000000001000100000000,0x10001000100010000000000000000],4,5,0x10001000100000001000000000000)
theorem q6e : EL q6f 4 5:=qh (qa 128 8 [4,5,6] 0) zI zH (by decide +kernel)
def q69 : q2:=(0x5000000050000000500000005,[0x4000000040000000400000004,0x5000000000000000500000000,0x5000000050000000000000000],4,5,0x5000000040000000400000000)
theorem q68 : EL q69 4 5:=qh (qa 128 8 [1,5,6] 0) zI zH (by decide +kernel)
def q7K : q2:=(0x1010101010101010101010101010101,[0x1000100010001000100010001000100,0x1010000010100000101000001010000,0x1010101000000000101010100000000,0x1010101010101010000000000000000],5,6,0x1010101010101000101010000000000)
theorem q7J : EL q7K 5 6:=qh (qa 128 16 [3,5,4,6] 0) z7 z6 (by decide +kernel)
def q67 : q2:=(0x3000000030000000300000003,[0x2000000020000000200000002,0x3000000000000000300000000,0x3000000030000000000000000],4,5,0x3000000020000000200000000)
theorem q66 : EL q67 4 5:=qh (qa 128 8 [0,5,6] 0) zI zH (by decide +kernel)
def q7E : q2:=(0x303000003030000030300000303,[0x202000002020000020200000202,0x300000003000000030000000300,0x303000000000000030300000000,0x303000003030000000000000000],6,7,0x303000003020000030200000200)
theorem q7D : EL q7E 6 7:=qh (qa 128 16 [0,3,5,6] 0) km kl (by decide +kernel)
def q6b : q2:=(0x11000000110000001100000011,[0x10000000100000001000000010,0x11000000000000001100000000,0x11000000110000000000000000],4,5,0x11000000100000001000000000)
theorem q6a : EL q6b 4 5:=qh (qa 128 8 [2,5,6] 0) zI zH (by decide +kernel)
def q7G : q2:=(0x30003000300030003000300030003,[0x20002000200020002000200020002,0x30000000300000003000000030000,0x30003000000000003000300000000,0x30003000300030000000000000000],5,6,0x30003000300020003000200000000)
theorem q7F : EL q7G 5 6:=qh (qa 128 16 [0,5,4,6] 0) z7 z6 (by decide +kernel)
def ze : Word:=0xffffffffffffffffffffffffffffffff
def yM : Word:=0xfffffffffffffffefffffffefefceea0
def zP : List Word:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def uG : Option qw:=some ⟨[5,9,10,18,20,33,34,36,40,48,65,66,3,6,12,17,24,32,64,3,3,3,3,3],rfl⟩
def q2X : List zW:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,4),(0xcccccccccccccccccccccccccccccccc,10,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,1),(0xff00ff00ff00ff00ff00ff00ff00ff00,9,1),(0xffff0000ffff0000ffff0000ffff0000,18,2),(0xffffffff00000000ffffffff00000000,33,1),(0xffffffffffffffff0000000000000000,65,1)]
def q17 : qH:=(0x22140c06830280c1200c090305018120182c301206024060a03058060708854804220110180d10088402420120805020104181c080c0205008864301908048301c040a01048100c00c0e0603840281008480600184c182406110040a030880c420605030090184808240211022210890430140304820140c0280814101800609018840641088480c070884c042201108220508824180503028180a040240c05040280605008140412008240805009040221,79)
def yN : zj:=fun i=>zf 6 19 0x31a6e636c92815494274a1ccc42918712310e201b4432a824a0f2509d6213834270650e3d39a62734f4e54078abd39362726c4148c6c918dd09281e643358706b10cc49b1892d31258618acb00f16c4228c86518a4a00f149432526e4a4dc74a78cf4f1589c2b10854a70a94214c9c28cdc4496089430d26e198d83315060420c06c19880349b8464308c6e118ac200f8201304012081fc0 i
def jP : z2 :=
 qv 0xd03000cf1ce1000cc2000000000000000cb1ca1c91c72c43c13c01bb5b83000b53ae7a86a53a32a039c49b19929639519058f18c38b18838627e87b371a65c5f65694d94764433f53a536430624c16e10601f001 0xdf24d03e32007e6340f80381f0ca1bd61c87c6360f4c801e98d03d4a0578f4ead589c1e25093532106a3420f24a01d31303b61c076943ac24a01d2530384967666342cc080d73d143a621072c380e18871b81083701b366c40cbd8701a2530b64a016831c4cc0681b0070334a0a6c935aad25a9998a9b119a06c32a0d0c531618843300f06b2500c8038d53d14344a106201c6a5e8a19b108321a10623280c189a183d382f62705cf582a58981498a02e7ac05cc582b18801625602b4a005464c0b989a173d38ac62705a03c0b189a163d382b62705264e0a98821498d997928d4cf4eca1e894eb138a64a70469400a12584e813aa7621c506430a0c6e13c943a4626d30c3968cc981318d81a31023a33686c650cd81001d01b32d251e91e9d8cbd132062724864e08cc81cf18a01931023c34087c6501001381c01a32af4548d88412b0e026321846635854c42ca3d1424621e28c3968d28411a4d82249684292ce78c6c4f01081e4a093e935a4925acd98d420315c2462127863c8d80a81f00f322f450798840e990c1c314c2662106c03c8cb10c1a4a1832937251e9c49313818327828641048c524ab1349162082a94d06126e0898a8957a7126c4e05d29e0a2504167a782ac4e05188409a538124a102264e615e8b47310f0561c918942c3126c07a4b38931b32034304066e058ca50618a912042611e8a86b10e8761c81c94303526f0224b50b32101863602cc540418810919b21432a0280840480d88462190a94301d26e03190c0531b80862b6058734124de81496f06637c08c570098850319be0632b80863e808c548201b90602b00c03e01004c0100480007f 12 0xfff 4 0xf 23 0x7fffff 13 0x1fff 0x3f 19 4
theorem uR : z1 jP :=
 qt 0xd03000cf1ce1000cc2000000000000000cb1ca1c91c72c43c13c01bb5b83000b53ae7a86a53a32a039c49b19929639519058f18c38b18838627e87b371a65c5f65694d94764433f53a536430624c16e10601f001 0xdf24d03e32007e6340f80381f0ca1bd61c87c6360f4c801e98d03d4a0578f4ead589c1e25093532106a3420f24a01d31303b61c076943ac24a01d2530384967666342cc080d73d143a621072c380e18871b81083701b366c40cbd8701a2530b64a016831c4cc0681b0070334a0a6c935aad25a9998a9b119a06c32a0d0c531618843300f06b2500c8038d53d14344a106201c6a5e8a19b108321a10623280c189a183d382f62705cf582a58981498a02e7ac05cc582b18801625602b4a005464c0b989a173d38ac62705a03c0b189a163d382b62705264e0a98821498d997928d4cf4eca1e894eb138a64a70469400a12584e813aa7621c506430a0c6e13c943a4626d30c3968cc981318d81a31023a33686c650cd81001d01b32d251e91e9d8cbd132062724864e08cc81cf18a01931023c34087c6501001381c01a32af4548d88412b0e026321846635854c42ca3d1424621e28c3968d28411a4d82249684292ce78c6c4f01081e4a093e935a4925acd98d420315c2462127863c8d80a81f00f322f450798840e990c1c314c2662106c03c8cb10c1a4a1832937251e9c49313818327828641048c524ab1349162082a94d06126e0898a8957a7126c4e05d29e0a2504167a782ac4e05188409a538124a102264e615e8b47310f0561c918942c3126c07a4b38931b32034304066e058ca50618a912042611e8a86b10e8761c81c94303526f0224b50b32101863602cc540418810919b21432a0280840480d88462190a94301d26e03190c0531b80862b6058734124de81496f06637c08c570098850319be0632b80863e808c548201b90602b00c03e01004c0100480007f 12 0xfff 4 0xf 23 0x7fffff 13 0x1fff 0x3f 19 4
def uV : List qb:=zk zP 0x2006390412428242000880018414e90a0508000e34a05fc820a1d0a00107960926ee08804805d11083b44118626541145910ee900431390507c64804a642300a046076736f 0x6380010000000000000018004c0000400000784200fc0004760a600072c0822e431824002d001ca1040186e62410741034e00002139043ac4a8409600200202607a606b 79
noncomputable def q2n:=qG ze 79 uV 13 yN
noncomputable def q16:=zx ze zP 13 1 yN
noncomputable def uF:=qr ze zP 13 1 yN
def yL (a : Nat) : Option z0 :=
 if Nat.blt a 20 then
  match a with
  |1=>some [vC]
  |2=>some [q0V,q0U]
  |3=>some [q0V,q0U,vC]
  |4=>some [q47,q0T]
  |5=>some [q47,q0T,vC]
  |6=>some [q44,q0V,q0T,vD]
  |7=>some [q44,q0V,q0T,vD,vC]
  |8=>some [q46,vD]
  |9=>some [q46,vD,vC]
  |10=>some [q45,q0V,q0U,vD]
  |11=>some [q45,q0V,q0U,vD,vC]
  |12=>some [q45,q43]
  |13=>some [q45,q43,vC]
  |14=>some [q46,q42,q0T,vD]
  |15=>some [q46,q42,q0T,vD,vC]
  |16=>some [q47,q43,q0U,vD]
  |17=>some [q47,q43,q0U,vD,vC]
  |18=>some [q44,q42]
  |19=>some [q44,q42,vC]
  | _=>none
 else none
theorem q1I : qP ze yM 128 yL :=
 qs
  (sel:=fun a i=>Fin.ofNat 128 (qe 7 (z3 0xb814e6a0a72e11a3a88d1b888d6a446ae80a7ac053b9111ea888ee7015ab80ab9a226ad112e4e03aa701b8a706a5382e8d1000000 21 a) i.val))
  (inv:=fun a i=>Fin.ofNat 128 (qe 7 (z3 0xb814e6a0a72e6889ab444b9111ea888ee80a7ac053b888d6a446ae7015ab80ab8468ea2346e4e03aa701b8a706a5382e8d1000000 21 a) i.val))
  (bound:=20)
  (by intro a ha;unfold yL;rw [show Nat.blt a 20=false from by cases h : Nat.blt a 20;rfl;have:=Nat.blt_eq.mp h;omega];rfl)
  (by decide +kernel)
def vj : List q2:=[q9U,q9K,q9I,q9S,q9Q,q9O,q9M,q9i,q9a,q9c,q94,q9e,q9g,q92,q96,q98,q7I,q90,q6d,q6f,q69,q7K,q67,q7E,q6b,q7G]
theorem q1G : qu vj:=q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (q1 (show qu [] from fun _ h=>False.elim (List.not_mem_nil h)) q7F.1 q7F.2) q6a.1 q6a.2) q7D.1 q7D.2) q66.1 q66.2) q7J.1 q7J.2) q68.1 q68.2) q6e.1 q6e.2) q6c.1 q6c.2) q8Z.1 q8Z.2) q7H.1 q7H.2) q97.1 q97.2) q95.1 q95.2) q91.1 q91.2) q9f.1 q9f.2) q9d.1 q9d.2) q93.1 q93.2) q9b.1 q9b.2) q99.1 q99.2) q9h.1 q9h.2) q9L.1 q9L.2) q9N.1 q9N.2) q9P.1 q9P.2) q9R.1 q9R.2) q9H.1 q9H.2) q9J.1 q9J.2) q9T.1 q9T.2
def q0b : Nat → Nat:=fun i =>
 match Nat.shiftRight i 6 with
 | 0=>y9 0x1518a60002a314c000000f980000001100000001c0000001880000000a000000000000000006000263154000000000000a8c530001518a80001831540002062a00000000000000001c00000005c0000003b8000001e10000005e6000000c0400000170820d38c540022e18a600022314c00394628800090c530000018a800028314c075a0629800498c570000918a60000831640004462a800040c540000918a80720c21cc075a062a000003d6100000706e0000124a01830462980e408c54000cf10e67305231500f328439800068c5401cc4189a00010314c0002062a000028c51a48a818a60014625200002462880e628c4801c8310560314627a0e181462880e618928000c4189a0018a3120e629062080c520462 35 (Nat.land i 63)
 | _=>0
noncomputable def q1H:=qO 2 false true ze yM uG vj (some q0b) 64 yN q16 uF yL jP 79 q2n
theorem q1E : qT 2 false ze yM uG (qk true vj) q2X 64 yN uF yL jP zP 13 1=true:=by decide +kernel
theorem q3N : qE 0 64 q1H=true:=by decide +kernel
theorem q1F : qo ze zP yM 1 14 :=
 zm (root:=uV) (sample:=q17) (hints:=(some q0b)) q1I uR q1G q1E q3N
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def w5 : List (BitVec 128):=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def vi : BitVec 128:=0xfffffffffffffffefffffffefefceea0
def q37 : List Word:=w5.map BitVec.toNat
def j1 : PEqualNP.CircuitLowerBounds.Circuit:=⟨[⟨.or,[5,6]⟩,⟨.or,[3,7]⟩,⟨.or,[2,8]⟩,⟨.or,[2,1]⟩,⟨.or,[4,7]⟩,⟨.or,[4,3]⟩,⟨.or,[1,7]⟩,⟨.and,[0,9]⟩,⟨.and,[10,11]⟩,⟨.and,[12,13]⟩,⟨.or,[15,16]⟩,⟨.or,[14,17]⟩,⟨.and,[5,6]⟩,⟨.or,[18,19]⟩],20⟩
def vL : (Fin 7 → Bool) → Bool:=fun x : Fin 7 → Bool=>decide (∃ i < ([0,2,0,3,1,3,1,4,2,4,0,5,1,5,2,5,3,5,4,5,0,6,1,6,2,6,3,6,4,6,5,6] : List ℕ).length / 2,(List.ofFn x).getD (([0,2,0,3,1,3,1,4,2,4,0,5,1,5,2,5,3,5,4,5,0,6,1,6,2,6,3,6,4,6,5,6] : List ℕ).getD (2*i) 0) false=true ∧ (List.ofFn x).getD (([0,2,0,3,1,3,1,4,2,4,0,5,1,5,2,5,3,5,4,5,0,6,1,6,2,6,3,6,4,6,5,6] : List ℕ).getD (2*i+1) 0) false=true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q4q : yc (fun r=>(w5.map fun v=>v.getLsbD r)==List.ofFn fun j : Fin 7=>r.testBit j.val) 7 0=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q2W : yc (fun r=>vi.getLsbD r==vL (fun j : Fin 7=>r.testBit j.val)) 7 0=true:=by decide +kernel
theorem q2Y : qo (qI 128) q37 vi.toNat 1 14:=by
 intro k S hlive hS
 apply q1F k S (by simpa [ze,yM,qI,vi] using hlive)
 intro w hw
 have h1:=hS w hw
 rcases h1 with rfl | h1 | h1
 · exact Or.inl rfl
 · exact Or.inr (Or.inl (by simpa [ze,qI] using h1))
 · have hm : qC ze zP w=true :=
    List.all_eq_true.mp (by decide +kernel : q37.all (fun u=>qC ze zP u)=true) w h1
   exact jn.mp hm
end PEqualNP.Outside.L_meta_10460
open PEqualNP.Outside.L_meta_10460 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_10460 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates out legal oneNot computes
  have hfan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, out⟩ := by
    intro g hg; exact legal g hg
  have hev : (gates.foldl yK w5).getD out 0 = vi :=
    q7C w5 vi vL q4q q2W ⟨gates, out⟩ hfan computes
  have hhit : vi.toNat ∈ (gates.foldl yK w5).map BitVec.toNat := by
    rw [List.getD_eq_getElem?_getD] at hev
    cases h : (gates.foldl yK w5)[out]? with
    | none =>
      rw [h] at hev
      have hne : (0 : BitVec 128) ≠ vi := by decide +kernel
      exact False.elim (hne hev)
    | some v =>
      rw [h] at hev
      exact List.mem_map.mpr ⟨v, List.mem_of_getElem? h, congrArg BitVec.toNat hev⟩
  obtain ⟨k, t, S, hk, ht, hlive, hsub⟩ := q3M w5 gates vi.toNat legal (by unfold qi; decide +kernel) hhit
  have ht1 : t ≤ 1 := Nat.le_trans ht (q5u oneNot)
  by_cases ht0 : t = 0
  · subst ht0
    obtain ⟨gs', o', hleg', hlen', heval'⟩ := q0f w5 vi hlive hsub
    have hfan' : PEqualNP.MetaComplexity.FanInTwo ⟨gs', o'⟩ := by
      intro g hg
      have h := hleg' g hg
      exact ⟨by rcases h.1 with h1 | h1; exact Or.inl h1; exact Or.inr (Or.inl h1), h.2⟩
    refine ⟨gs', o', hleg', Nat.le_trans hlen' hk, ?_⟩
    exact q0G w5 vi ⟨gs', o'⟩ vL hfan' q4q q2W heval'
  · have ht1eq : t = 1 := by omega
    subst ht1eq
    have size : 14 ≤ gates.length := Nat.le_trans (q2Y k S hlive (fun w hw => Or.inr (Or.inr (hsub w hw)))) hk
    have monoEval : ∀ x, j1.eval (List.ofFn x) = vL x := by
      intro x
      have clean : PEqualNP.MetaComplexity.FanInTwo j1 := by
        intro gate member
        simp only [j1, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      exact q0G w5 vi j1 vL clean q4q q2W (by decide +kernel) x
    refine ⟨j1.gates, j1.output, ?_, ?_, monoEval⟩
    · intro gate member
      simp only [j1, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact Nat.le_trans (by decide +kernel : j1.gates.length ≤ 14) size
