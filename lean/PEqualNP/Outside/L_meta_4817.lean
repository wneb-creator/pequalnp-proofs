import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_4817.eg
open PEqualNP.CircuitLowerBounds
abbrev Sig:= BitVec 512
def zero:Sig:= 0
def one:Sig:= BitVec.allOnes 512
def neg (a:Sig):Sig:= ~~~a
def bin (d:Nat) (a b:Sig):Sig:=
 if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def bu (a:Sig):Prop:= a ≠ zero ∧ a ≠ one
def bK (u:Bool) (d:Nat):Prop:= d<2 ∨ (u=true ∧ d<4)
def i0 (d:Nat):= if d=2 then 3 else if d=3 then 2 else d
lemma cd {u d} (h:bK u d):d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3):= by
 rcases h with h | ⟨h,j⟩
 · omega
 · have:d=0 ∨ d=1 ∨ d=2 ∨ d=3:= by omega
   rcases this with h1 | h1 | h1 | h1
   · exact Or.inl h1
   · exact Or.inr (Or.inl h1)
   · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
   · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
lemma mT {u d} (h:bK u d) (a b:Sig):bin d a b = bin (i0 d) b a:= by
 rcases cd h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,i0,BitVec.and_comm,BitVec.or_comm]
lemma rc {u d} (h:bK u d):bK u (i0 d) ∧ i0 (i0 d)=d:= by
 rcases cd h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
 all_goals simp_all [i0,bK]
def Live (u:Bool) (target:Sig):Nat → Finset Sig → Prop
 | 0,S => S={target} ∧ bu target
 | k+1,S => ∃ (U:Finset Sig) (a b:Sig) (d:Nat),bK u d ∧ S=insert a (insert b U) ∧
     bu a ∧ bu b ∧ a ≠ b ∧
     bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
lemma Live.stop {u} {target:Sig} (hp:bu target):Live u target 0 {target}:= ⟨rfl,hp⟩
lemma Live.binary {u} {target:Sig} {k:Nat} {U:Finset Sig} {a b:Sig} {d:Nat} (hd:bK u d)
   (ha:bu a) (hb:bu b) (hab:a ≠ b)
   (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live u target k (insert (bin d a b) U)):
   Live u target (k+1) (insert a (insert b U)):=
 ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
lemma Live.ind {u} {target:Sig} {motive: ∀ (k:Nat) (S:Finset Sig),Live u target k S → Prop}
   (stop: ∀ (hp:bu target),motive 0 {target} (Live.stop hp))
   (binary: ∀ {k:Nat} {U:Finset Sig} {a b:Sig} {d:Nat} (hd:bK u d)
     (ha:bu a) (hb:bu b) (hab:a ≠ b)
     (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live u target k (insert (bin d a b) U)),
     motive k (insert (bin d a b) U) tail →
     motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
   {k:Nat} {S:Finset Sig} (h:Live u target k S):motive k S h:= by
 induction k generalizing S with
 | zero =>
   obtain ⟨rfl,hp⟩:= h
   exact stop hp
 | succ k ih =>
   obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩:= h
   exact binary hd ha hb hab hf tail (ih tail)
private lemma mf {u target k S} (h:Live u target k S): ∀ a ∈ S,bu a:= by
 induction h using Live.ind with
 | stop hp => simpa using hp
 | binary hd ha hb hab hf _ ih =>
   simp only [Finset.forall_mem_insert]
   exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma lP {u target k S} (h:Live u target k S):S.card ≤ k+1:= by
 induction h using Live.ind with
 | stop hp => simp
 | @binary k U a b d hd ha hb hab hf _ ih =>
   have hu:bin d a b ∉ U:= fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
   rw [Finset.card_insert_of_notMem hu] at ih
   have h1:= Finset.card_insert_le (a:= a) (s:= insert b U)
   have h2:= Finset.card_insert_le (a:= b) (s:= U)
   omega
def bit (i:Fin 512) (a:Sig):Bool:= a.getLsbD i.val
private lemma dg (i):bit i zero = false:= by simp [bit,zero]
private lemma eV (i):bit i one = true:= by unfold bit one;rw [BitVec.getLsbD_allOnes];simp
private lemma lp (i) (a:Sig):bit i (neg a) = !(bit i a):= by simp [bit,neg,i.isLt]
private lemma hU (i d) (a b:Sig):bit i (bin d a b) =
   (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
     if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b):= by
 unfold bin
 split_ifs <;> simp [bit]
lemma du {a b:Sig} (h: ∀ i,bit i a = bit i b):a=b:=
 BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩
def nrm (u:Bool) (a:Sig):Sig:= if u && bit 0 a then neg a else a
lemma rq (a:Sig):nrm false a = a:= rfl
lemma uu (a:Sig):bit 0 (nrm true a) = false:= by
 cases h:bit 0 a <;> simp [nrm,h,lp]
lemma ug {u} {a:Sig} (h:bit 0 a = false):nrm u a = a:= by simp [nrm,h]
lemma zzzz (a:Sig):neg (neg a) = a:= by simp [neg]
lemma vf (a:Sig):nrm true (neg a) = nrm true a:= by
 cases h:bit 0 a <;> simp [nrm,h,lp,zzzz]
lemma qo {a:Sig} (h:bu (neg a)):bu a:= by
 refine ⟨?_,?_⟩
 · rintro rfl
   exact h.2 (by simp [neg,zero,one])
 · rintro rfl
   exact h.1 (by simp [neg,zero,one])
lemma qn {u} {a:Sig} (h:bu (nrm u a)):bu a:= by
 unfold nrm at h
 split at h
 · exact qo h
 · exact h
def prime (d:Bool) (a b:Sig):= if d then a ||| b else a &&& b
lemma lI (i) (d:Bool) (a b:Sig):bit i (prime d a b) =
   (if d then bit i a || bit i b else bit i a && bit i b):= by cases d <;> simp [prime,bit]
lemma si (d:Bool) (a b:Sig):
   ∃ e,e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b):= by
 refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
   else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
 · split_ifs <;> omega
 · apply du
   intro i
   cases d <;> cases ha:bit 0 a <;> cases hb:bit 0 b <;>
     simp only [nrm,lI,ha,hb,hU,lp,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
       Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
     cases hx:bit i a <;> cases hy:bit i b <;> simp [hx,hy,lp,lI]
def cJ (w:List Sig) (v:Sig):Prop:= v ∈ w ∨ ¬bu v
def Repr (u:Bool) (w:List Sig) (v:Sig):Prop:= cJ w (nrm u v)
private lemma pt (a:Sig):
   bin 0 a one = a ∧ bin 1 a zero = a ∧
   bin 0 a zero = zero ∧ bin 1 a one = one ∧
   bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
   bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
   bin 0 one a = a ∧ bin 1 one a = one:= by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply du <;> intro i <;>
   simp [hU,dg,eV]
private lemma jn {w:List Sig} {a:Sig} (h:cJ w a):
   a = zero ∨ a = one ∨ a ∈ w ∧ bu a:= by
 by_cases hz:a = zero
 · exact Or.inl hz
 by_cases ho:a = one
 · exact Or.inr (Or.inl ho)
 exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def fy (u:Bool) (w:List Sig) (z:Sig):Prop:=
 ∃ d a b,bK u d ∧ a ∈ w ∧ b ∈ w ∧ bu a ∧ bu b ∧ a ≠ b ∧ z = bin d a b
private lemma qr {u w a b} (d:Nat) (hd:bK u d) (ha:cJ w a) (hb:cJ w b)
   (no:u=true → a ≠ one ∧ b ≠ one):
   cJ w (bin d a b) ∨ fy u w (bin d a b):= by
 have rz:cJ w zero:= Or.inr (fun h => h.1 rfl)
 have ro:cJ w one:= Or.inr (fun h => h.2 rfl)
 obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩:= pt a
 obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩:= pt b
 by_cases he:a=b
 · subst b
   left
   rcases cd hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
   · exact a5.symm ▸ ha
   · exact a6.symm ▸ ha
   · exact a7.symm ▸ rz
   · exact a8.symm ▸ rz
 rcases jn ha with rfl | rfl | ⟨ham,hap⟩
 · left
   rcases cd hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
   · exact b13.symm ▸ rz
   · exact b14.symm ▸ hb
   · exact b11.symm ▸ rz
   · exact b10.symm ▸ hb
 · left
   rcases cd hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
   · exact b15.symm ▸ hb
   · exact b16.symm ▸ ro
   · exact absurd rfl (no hu).1
   · exact absurd rfl (no hu).1
 rcases jn hb with rfl | rfl | ⟨hbm,hbp⟩
 · left
   rcases cd hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
   · exact a3.symm ▸ rz
   · exact a2.symm ▸ ha
   · exact a9.symm ▸ ha
   · exact a12.symm ▸ rz
 · left
   rcases cd hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
   · exact a1.symm ▸ ha
   · exact a4.symm ▸ ro
   · exact absurd rfl (no hu).2
   · exact absurd rfl (no hu).2
 exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
lemma mj (a:Sig):nrm true a ≠ one:= by
 intro h
 have:= uu a
 rw [h,eV] at this
 exact Bool.noConfusion this
lemma qz {u w a b} (d:Bool) (ha:Repr u w a) (hb:Repr u w b):
   Repr u w (prime d a b) ∨ fy u w (nrm u (prime d a b)):= by
 cases u
 · have e:prime d a b = bin (if d then 1 else 0) a b:= by cases d <;> rfl
   have h:= qr (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
   unfold Repr
   simp only [rq] at h ⊢
   rwa [e]
 · obtain ⟨e,he,eq⟩:= si d a b
   unfold Repr
   rw [eq]
   exact qr e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨mj a,mj b⟩)
lemma mJ {u w} {v:Sig} (h:v=zero ∨ v=one):Repr u w v:= by
 refine Or.inr fun hp => ?_
 have:= qn hp
 rcases h with rfl | rfl
 · exact this.1 rfl
 · exact this.2 rfl
private lemma rm {u target} {w:List Sig} {z:Sig} {k S c} (h:Live u target k S)
   (hz:cJ w z ∨ (c=1 ∧ fy u w z)) (sub: ∀ a ∈ S,a ∈ w++[z]):
   ∃ k' S',k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S',a ∈ w:= by
 by_cases hm:z ∈ S
 · by_cases hw:z ∈ w
   · refine ⟨k,S,by omega,h,?_⟩
     intro a ha
     have hu:a ∈ w ∨ a = z:= by simpa using sub a ha
     rcases hu with hu | rfl
     · exact hu
     · exact hw
   · have hp:= mf h z hm
     rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
     · exact False.elim ((hr.resolve_left hw) hp)
     · subst z
       let U:= S.erase (bin d a b)
       have ht:Live u target k (insert (bin d a b) U):= by simpa [U,Finset.insert_erase hm] using h
       have hu: ∀ v ∈ U,v ∈ w:= by
         intro v hv
         obtain ⟨hne,hm⟩:= Finset.mem_erase.mp hv
         simpa [hne] using sub v hm
       have hf:bin d a b ∉ insert a (insert b U):= by
         intro hh
         rcases Finset.mem_insert.mp hh with eq | u
         · exact hw (eq.symm ▸ ha)
         rcases Finset.mem_insert.mp u with eq | u
         · exact hw (eq.symm ▸ hb)
         · exact hw (hu _ u)
       exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
 · refine ⟨k,S,by omega,h,?_⟩
   intro a ha
   have hn:a ≠ z:= fun hh => hm (hh ▸ ha)
   simpa [hn] using sub a ha
abbrev Wire (R:Type):= R → Bool
def inv {R} (a:Wire R):Wire R:= fun r => !(a r)
def bH {R} (isOr:Bool) (a b:Wire R):Wire R:=
 if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d:Nat) (a b:Wire R):Wire R:=
 if d=0 then bH false a b else if d=1 then bH true a b else
   if d=2 then bH false a (inv b) else bH false (inv a) b
def aS {R} (a:Wire R):Prop:= ∃ b:Bool,a = fun _ => b
noncomputable def cost {R} (a:Wire R):Nat:= by
 classical exact if aS a then 1 else 0
noncomputable def mass {R} (xs:List (Wire R)):Nat:= (xs.map cost).sum
def ad {R} (u:Bool) (pool:List (Wire R)) (v:Wire R):Prop:=
 v ∈ pool ∨ aS v ∨ (u=true ∧ inv v ∈ pool)
def co {R} (u:Bool) (pool xs:List (Wire R)):= ∀ a ∈ xs,ad u pool a
def Reach {R} (u:Bool) (roots:List (Wire R)):Nat → List (Wire R) → Prop
 | 0,b => b=roots
 | p+1,c => ∃ (op:Bool) (bank:List (Wire R)) (a b:Wire R),Reach u roots p bank ∧ ad u bank a ∧
     ad u bank b ∧ c=bH op a b::bank
lemma Reach.start {R u} {roots:List (Wire R)}:Reach u roots 0 roots:= rfl
lemma Reach.two {R u} {roots:List (Wire R)} {p bank a b} (op:Bool) (h:Reach u roots p bank)
   (ha:ad u bank a) (hb:ad u bank b):Reach u roots (p+1) (bH op a b::bank):=
 ⟨op,bank,a,b,h,ha,hb,rfl⟩
lemma Reach.ind {R u} {roots:List (Wire R)} {motive: ∀ p bank,Reach u roots p bank → Prop}
   (start:motive 0 roots Reach.start)
   (two: ∀ {p bank a b} (op:Bool) (h:Reach u roots p bank) (ha:ad u bank a)
     (hb:ad u bank b),motive p bank h →
     motive (p+1) (bH op a b::bank) (Reach.two op h ha hb))
   {p bank} (h:Reach u roots p bank):motive p bank h:= by
 induction p generalizing bank with
 | zero =>
   obtain rfl:= h
   exact start
 | succ p ih =>
   obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩:= h
   exact two op h ha hb (ih h)
def kept {α:Type} (save:Bool) (x:α) (xs:List α):= if save then x::xs else xs
def Run {R} (u:Bool) (goal:Wire R):Nat → List (Wire R) → Prop
 | 0,zs => List.Perm [goal] zs
 | s+1,zs => ∃ (op:Nat) (ka kb:Bool) (a b:Wire R) (rest:List (Wire R)),bK u op ∧ (a::b::rest).Perm zs ∧
     Run u goal s (comb op a b::kept ka a (kept kb b rest))
lemma Run.stop {R u} {goal:Wire R}:Run u goal 0 [goal]:= List.Perm.refl _
lemma Run.perm {R u} {goal:Wire R} {s:Nat} {xs zs:List (Wire R)} (p:xs.Perm zs)
   (h:Run u goal s xs):Run u goal s zs:= by
 cases s with
 | zero => exact List.Perm.trans h p
 | succ s =>
   obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩:= h
   exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
lemma Run.two {R u} {goal:Wire R} {s:Nat} {a b:Wire R} {rest:List (Wire R)} (op:Nat) (hd:bK u op) (ka kb:Bool)
   (h:Run u goal s (comb op a b::kept ka a (kept kb b rest))):Run u goal (s+1) (a::b::rest):=
 ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
lemma Run.ind {R u} {goal:Wire R} {motive: ∀ s ws,Run u goal s ws → Prop}
   (stop:motive 0 [goal] Run.stop)
   (perm: ∀ {s xs zs} (p:List.Perm xs zs) (h:Run u goal s xs),motive s xs h → motive s zs (Run.perm p h))
   (two: ∀ {s a b rest} (op:Nat) (hd:bK u op) (ka kb:Bool) (h:Run u goal s (comb op a b::kept ka a (kept kb b rest))),
     motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
   {s ws} (h:Run u goal s ws):motive s ws h:= by
 induction s generalizing ws with
 | zero => exact perm h Run.stop stop
 | succ s ih =>
   obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩:= h
   exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
lemma gg {R} (a:Wire R) (xs):mass (a::xs)=cost a + mass xs:= by
 simp [mass]
lemma oj {R} (a:Wire R) (xs) (k:Bool):mass xs ≤ mass (kept k a xs):= by
 cases k <;> simp [kept,gg]
lemma gb {R} {a:Wire R} (h:aS a):aS (inv a):= by
 obtain ⟨v,rfl⟩:= h
 exact ⟨!v,rfl⟩
lemma pC {R} (a:Wire R):inv (inv a)=a:= by
 funext r
 simp [inv]
lemma pf {R} (a:Wire R):cost (inv a)=cost a:= by
 have:aS (inv a) ↔ aS a:= ⟨fun h => pC a ▸ gb h,gb⟩
 by_cases h:aS a
 · simp only [cost,if_pos h,if_pos (this.mpr h)]
 · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
lemma ik {R u} {bank:List (Wire R)} {a} (hu:u=true) (h:ad u bank a):ad u bank (inv a):= by
 rcases h with h | h | ⟨_,h⟩
 · exact Or.inr (Or.inr ⟨hu,(pC a).symm ▸ h⟩)
 · exact Or.inr (Or.inl (gb h))
 · exact Or.inl h
lemma nU {R} {a b:Wire R} (op) (h:aS a) (g:aS b):
   aS (bH op a b):= by
 obtain ⟨v,rfl⟩:= h
 obtain ⟨w,rfl⟩:= g
 cases op <;> exact ⟨_,rfl⟩
lemma da {R u} (op) {a b:Wire R} {bank}
   (h:aS a ∨ aS b) (ha:ad u bank a) (hb:ad u bank b):
   ad u bank (bH op a b):= by
 rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
 · cases op <;> cases v
   · exact Or.inr (Or.inl ⟨false,by funext x;simp [bH]⟩)
   · simpa [bH] using hb
   · simpa [bH] using hb
   · exact Or.inr (Or.inl ⟨true,by funext x;simp [bH]⟩)
 · cases op <;> cases v
   · exact Or.inr (Or.inl ⟨false,by funext x;simp [bH]⟩)
   · simpa [bH] using ha
   · simpa [bH] using ha
   · exact Or.inr (Or.inl ⟨true,by funext x;simp [bH]⟩)
lemma cC {R u} {bank v} (w:Wire R) (h:ad u bank v):
   ad u (w::bank) v:=
 h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
lemma p4 {R u} (roots:List (Wire R)) {p bank a b} (op) (hp:Reach u roots p bank)
   (ha:ad u bank a) (hb:ad u bank b):
   ∃ q next,Reach u roots q next ∧ ad u next (bH op a b) ∧
       (∀ v,ad u bank v → ad u next v) ∧
       q+cost a+cost b ≤ p+1+cost (bH op a b):= by
 classical
 by_cases c:aS a ∨ aS b
 · refine ⟨p,bank,hp,da op c ha hb,fun _ h => h,?_⟩
   by_cases ca:aS a <;> by_cases cb:aS b
   · simp [cost,ca,cb,nU op ca cb]
   · simp [cost,ca,cb]
   · simp [cost,ca,cb]
   · exact False.elim (c.elim ca cb)
 · have ca: ¬aS a:= fun h => c (Or.inl h)
   have cb: ¬aS b:= fun h => c (Or.inr h)
   exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => cC _ h,
     by simp [cost,ca,cb]⟩
lemma mM {R u} {bank:List (Wire R)} {d a b} (hd:bK u d) (ha:ad u bank a) (hb:ad u bank b):
   ∃ op x y,comb d a b=bH op x y ∧ ad u bank x ∧ ad u bank y ∧ cost x=cost a ∧ cost y=cost b:= by
 rcases cd hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
 · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
 · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
 · exact ⟨false,a,inv b,rfl,ha,ik hu hb,rfl,pf b⟩
 · exact ⟨false,inv a,b,rfl,ik hu ha,hb,pf a,rfl⟩
lemma pM {R u} (roots:List (Wire R)) {p bank a b} (d) (hd:bK u d) (hp:Reach u roots p bank)
   (ha:ad u bank a) (hb:ad u bank b):
   ∃ q next,Reach u roots q next ∧ ad u next (comb d a b) ∧
       (∀ v,ad u bank v → ad u next v) ∧
       q+cost a+cost b ≤ p+1+cost (comb d a b):= by
 obtain ⟨op,x,y,e,hx,hy,cx,cy⟩:= mM hd ha hb
 rw [e,←cx,←cy]
 exact p4 roots op hp hx hy
lemma pE {α:Type} {k:Bool} {x a:α} {xs} (h:x ∈ kept k a xs):
   x=a ∨ x∈xs:= by cases k <;> simp_all [kept]
lemma py {R u} {goal:Wire R} (nc: ¬aS goal) {s ws}
   (h:Run u goal s ws) (roots:List (Wire R)) {p bank}
   (hp:Reach u roots p bank) (hs:co u bank ws):
   ∃ q next,Reach u roots q next ∧ ad u next goal ∧ q+mass ws ≤ p+s:= by
 classical
 induction h using Run.ind generalizing p bank with
 | stop =>
   exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
 | perm eq _ ih =>
   have hsub:co u bank _:= fun v hv => hs v (eq.mem_iff.mp hv)
   obtain ⟨q,W,hW,hv,hl⟩:= ih hp hsub
   exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
 | @two s a b rest op hd ka kb _ ih =>
   obtain ⟨r,T,hT,hz,inc,le⟩:= pM roots op hd hp (hs a (by simp)) (hs b (by simp))
   have ht:co u T (comb op a b::kept ka a (kept kb b rest)):= by
     intro v h
     rcases List.mem_cons.mp h with rfl | hh
     · exact hz
     · apply inc v
       apply hs
       rcases pE hh with rfl | hh
       · simp
       · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (pE hh))
   obtain ⟨q,W,hW,hv,hl⟩:= ih hT ht
   have hlen:= oj a (kept kb b rest) ka
   have hlen':= oj b rest kb
   rw [gg] at hl
   refine ⟨q,W,hW,hv,?_⟩
   rw [gg,gg]
   omega
def aD {R S:Type} (rows:S → R) (a:Wire R):Wire S:=
 fun r => a (rows r)
lemma nQ {R S:Type} (rows:S → R) (k:Bool) (a:Wire R) (ws):
   (kept k a ws).map (aD rows) =
   kept k (aD rows a) (ws.map (aD rows)):= by
 cases k <;> simp [kept]
lemma ju {R S:Type} (rows:S → R) (d) (a b:Wire R):
   aD rows (comb d a b) = comb d (aD rows a) (aD rows b):= by
 unfold comb
 split_ifs <;> rfl
lemma oO {R S:Type} {u} (rows:S → R) {goal s ws} (h:Run u goal s ws):
   Run u (aD rows goal) s (ws.map (aD rows)):= by
 induction h using Run.ind with
 | stop => exact Run.stop
 | perm p _ ih => exact Run.perm (p.map _) ih
 | two op hd ka kb _ ih =>
   simp only [List.map_cons,nQ,ju] at ih ⊢
   exact Run.two op hd ka kb ih
lemma fg {R S:Type} {u} (rows:S → R) {goal s ws} (h:Run u goal s ws)
   (nc: ¬aS (aD rows goal)) {roots:List (Wire S)} {p bank L}
   (hp:Reach u roots p bank) (hs:co u bank (ws.map (aD rows)))
   (hl: ∀ q bs,Reach u roots q bs → ad u bs (aD rows goal) → L ≤ q):
   L + mass (ws.map (aD rows)) ≤ p+s:= by
 obtain ⟨q,bs,hq,ht,hle⟩:= py nc (oO rows h) roots hp hs
 have hqle:= hl q bs hq ht
 omega
abbrev Row:= Fin 512
def aF (a:Sig):Wire Row:= fun r => bit r a
def table (f:Wire Row):Sig:=
 (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
lemma ek (f:Wire Row) (r:Row):bit r (table f) = f r:= by
 simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn];simp [r.isLt]
lemma hZ (v:Sig):table (aF v) = v:= by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 exact ek (aF v) ⟨j,hj⟩
lemma nv (f:Wire Row):aF (table f) = f:= by
 funext r
 exact ek f r
lemma qq (a:Sig):aF (neg a) = inv (aF a):= by
 funext r
 exact lp _ _
lemma qw (d:Nat) (a b:Sig):
   aF (bin d a b) = comb d (aF a) (aF b):= by
 funext r
 simp only [aF,hU,comb]
 split_ifs <;> rfl
lemma ph {α β:Type} (f:α → β) (d:Bool) (a:α) (l:List α):
   (kept d a l).map f = kept d (f a) (l.map f):= by cases d <;> rfl
lemma mC {α:Type} (k:Bool) (a:α) (l:List α)
   (hn:l.Nodup) (ha:a ∉ l):(kept k a l).Nodup:= by cases k <;> simp [kept,hn,ha]
lemma lr (k:Bool) (a:Sig) (l:List Sig):
   (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset:= by
 cases k <;> simp [kept]
lemma m8 {u} {T:Sig} {k S} (h:Live u T k S) (v:List Sig)
   (hv:v.Nodup) (eqv:v.toFinset = S):Run u (aF T) k (v.map aF):= by
 classical
 induction h using Live.ind generalizing v with
 | stop hp =>
   have eq: [T].Perm v:= by
     apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
     simpa [eqv]
   exact Run.perm (eq.map _) Run.stop
 | @binary k U a b d hd ha hb hab fresh _ ih =>
   let rest:= ((U.erase a).erase b).toList
   let ka:= decide (a ∈ U)
   let kb:= decide (b ∈ U)
   let mid:= kept kb b rest
   let tail:= kept ka a mid
   have er:rest.toFinset = (U.erase a).erase b:= by simp [rest]
   have ar:a ∉ rest:= by simp [rest]
   have br:b ∉ rest:= by simp [rest]
   have hr:rest.Nodup:= Finset.nodup_toList _
   have bm:= mC kb b rest hr br
   have am:a ∉ mid:= by cases h:kb <;> simp [mid,kept,h,hab,ar]
   have nd:= mC ka a mid bm am
   have ht:tail.toFinset = U:= by
     change (kept ka a (kept kb b rest)).toFinset = U
     rw [lr,lr,er]
     ext j
     by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases aj:j=a <;>
       by_cases bj:j=b <;> simp_all [ka,kb]
   have hf:bin d a b ∉ tail:= by
     intro hz
     exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
   have progress:= ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
   change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map aF) at progress
   rw [List.map_cons,ph,ph,qw] at progress
   have perm:(a::b::rest).Perm v:= by
     apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
     ext j
     by_cases ja:j=a <;> by_cases jb:j=b <;> simp_all [er]
   exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
lemma so (f:Wire Row):table (inv f) = neg (table f):= by
 rw [←hZ (neg (table f)),qq,nv]
lemma pJ (d:Bool) (f g:Wire Row):
   table (bH d f g) = prime d (table f) (table g):= by
 apply du
 intro r
 rw [ek,lI,ek,ek]
 cases d <;> rfl
lemma h7 {u} {bank:List (Wire Row)} {a} (h:ad u bank a):
   Repr u ((bank.map table).map (nrm u)) (table a):= by
 rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
 · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
 · apply mJ
   cases b
   · exact Or.inl (du fun i => (ek _ i).trans (dg i).symm)
   · exact Or.inr (du fun i => (ek _ i).trans (eV i).symm)
 · have:= so a
   refine Or.inl ?_
   rw [←vf,←this]
   exact List.mem_map_of_mem (List.mem_map_of_mem hm)
lemma mP {u} {roots:List (Wire Row)} {p bank}
   (h:Reach u roots p bank) {T k S} (run:Live u T k S)
   (sub: ∀ a ∈ S,a ∈ (bank.map table).map (nrm u)):
   ∃ l V,l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V,a ∈ (roots.map table).map (nrm u):= by
 induction h using Reach.ind generalizing k S with
 | start => exact ⟨k,S,by omega,run,sub⟩
 | @two p bank a b d h ha hb ih =>
   rw [List.map_cons,List.map_cons,pJ] at sub
   have rep:= qz d (h7 ha) (h7 hb)
   obtain ⟨k',S',hk,run',sub'⟩:= rm (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
     (fun a hm => by simpa [or_comm] using sub a hm)
   obtain ⟨l,V,hl,hr,hs⟩:= ih run' sub'
   exact ⟨l,V,by omega,hr,hs⟩
def bJ (a:Sig):Bool:= !(bit 0 a)
lemma uo {u} {w:List Sig} (h:w.all bJ=true):w.map (nrm u)=w:= by
 have e:w.map (nrm u) = w.map id:= by
   apply List.map_congr_left
   intro a ha
   exact ug (by simpa [bJ] using List.all_eq_true.mp h a ha)
 rw [e,List.map_id]
lemma gv {u} {roots:List Sig} {p bank T} (hp:bu T) (nT:bJ T=true) (nR:roots.all bJ=true)
   (h:Reach u (roots.map aF) p bank) (hit:ad u bank (aF T)):
   ∃ k S,k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S,a ∈ roots:= by
 have hm:= h7 hit
 rw [hZ] at hm
 unfold Repr at hm
 rw [ug (by simpa [bJ] using nT)] at hm
 have mem:= hm.resolve_right (fun hn => hn hp)
 obtain ⟨l,V,hl,hr,hs⟩:= mP h (Live.stop hp) (by simpa using mem)
 refine ⟨l,V,by omega,hr,?_⟩
 have e:(roots.map aF).map table = roots:= by simp [List.map_map,Function.comp_def,hZ]
 rw [e,uo nR] at hs
 exact hs
lemma fn {u T k S} (h:Live u T k S) {r s:Row}
   (diff:bit r T ≠ bit s T): ∃ a ∈ S,bit r a ≠ bit s a:= by
 induction h using Live.ind with
 | stop hp => exact ⟨_,by simp,diff⟩
 | @binary k U a b d hd ha hb hab hf _ ih =>
   obtain ⟨v,hv,hd⟩:= ih
   rcases Finset.mem_insert.mp hv with rfl | hu
   · by_cases aeq:bit r a = bit s a
     · refine ⟨b,by simp,?_⟩
       intro beq
       exact hd (by rw [hU,hU,aeq,beq])
     · exact ⟨a,by simp,aeq⟩
   · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
lemma ex {u T k S} (h:Live u T k S) (roots:List Sig) (a:Sig)
   (sub: ∀ v ∈ S,v ∈ roots) (r s:Row) (diff:bit r T ≠ bit s T)
   (isolated: ∀ v ∈ roots,v ≠ a → bit r v = bit s v):a ∈ S:= by
 obtain ⟨v,hv,hd⟩:= fn h diff
 by_cases veq:v=a
 · simpa [veq] using hv
 · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs:List Sig:= [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph:Sig:= 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def cn (r:Row) (j:Fin 9):= bit r (inputs.getD j.val zero)
def edge (x:Fin 9 → Bool):Bool:=
 (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
 (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
 (x 6 && x 8) || (x 8 && x 5)
lemma mL: ∀ r:Row,bit r graph = edge (cn r):=by decide +kernel
lemma iA:bu graph:=by unfold bu;decide +kernel
lemma gt:List.ofFn (fun j:Fin 9 => inputs.getD j.val zero) = inputs:= rfl
def cF (f:Row → Row) (a:Sig):= table fun r => bit (f r) a
lemma de (f:Row → Row) (a:Sig) (r:Row):
   bit r (cF f a) = bit (f r) a:= ek _ _
lemma dh (f:Row → Row) (a:Sig):
   aF (cF f a) = aD f (aF a):= by funext r;exact de f a r
lemma mR (f:Row → Row) (d:Nat) (a b:Sig):
   cF f (bin d a b) = bin d (cF f a) (cF f b):= by
 apply du
 intro r
 simp only [de,hU]
lemma qd (f:Row → Row) (onto:Function.Surjective f):
   Function.Injective (cF f):= by
 intro a b h
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 obtain ⟨r,hr⟩:= onto ⟨j,hj⟩
 have he:= congrArg (bit r) h
 change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
 rw [de,de,hr] at he
 exact he
lemma iq (f:Row → Row):cF f zero = zero ∧ cF f one = one:= by
 constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
 · exact (de f zero ⟨j,hj⟩).trans ((dg _).trans (dg ⟨j,hj⟩).symm)
 · exact (de f one ⟨j,hj⟩).trans ((eV _).trans (eV ⟨j,hj⟩).symm)
lemma pz {u T k S} (h:Live u T k S) (f:Row → Row) (onto:Function.Surjective f):
   Live u (cF f T) k (S.image (cF f)):= by
 have inj:= qd f onto
 obtain ⟨fz,fo⟩:= iq f
 have pp (v) (p:bu v):bu (cF f v):=
   ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
 induction h using Live.ind with
 | stop hp => simpa using Live.stop (pp _ hp)
 | @binary k U a b d hd ha hb hab hf _ ih =>
   have fresh:cF f (bin d a b) ∉ (insert a (insert b U)).image (cF f):= by
     intro hm
     obtain ⟨v,hv,eq⟩:= Finset.mem_image.mp hm
     exact hf (inj eq ▸ hv)
   simp only [Finset.image_insert,mR] at fresh ih ⊢
   exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
lemma jj {u T k S} (h:Live u T k S) (none:u=false) {r s:Row}
   (pos:bit r T = true) (negRow:bit s T = false):
   ∃ a ∈ S,bit r a = true ∧ bit s a = false:= by
 induction h using Live.ind with
 | stop hp => exact ⟨_,by simp,pos,negRow⟩
 | @binary k U a b d hd ha hb hab hf _ ih =>
   obtain ⟨v,hv,hp,hn⟩:= ih
   rcases Finset.mem_insert.mp hv with rfl | hu
   · rw [hU] at hp hn
     subst none
     rcases cd hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
     · cases p:bit r a <;> cases q:bit s a <;> cases u:bit r b <;> cases z:bit s b <;> simp_all
     · cases p:bit r a <;> cases q:bit s a <;> cases u:bit r b <;> cases z:bit s b <;> simp_all
     · exact Bool.noConfusion h
     · exact Bool.noConfusion h
   · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (u:Bool) (roots:List Sig) (T:Sig) (L:Nat):Prop:=
 ∀ p bank,Reach u (roots.map aF) p bank → ad u bank (aF T) → L ≤ p
lemma sr {R u} {roots:List (Wire R)} {p bank} (h:Reach false roots p bank):Reach u roots p bank:= by
 have up {bank:List (Wire R)} {a} (h:ad false bank a):ad u bank a:=
   h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
 induction h using Reach.ind with
 | start => exact Reach.start
 | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
lemma pZ {u roots T L} (h:Lower true roots T L):Lower u roots T L:= by
 cases u
 · exact fun p bank hr ha => h p bank (sr hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
 · exact h
def az (u:Bool) (T:Sig) (cap:Nat) (S:Finset Sig):Prop:=
 ∀ k,k ≤ cap → ¬Live u T k S
def i5 (T:Sig) (roots:List Sig) (a:Sig):Prop:=
 ∃ r s:Row,bit r T ≠ bit s T ∧ ∀ v ∈ roots,v ≠ a → bit r v = bit s v
lemma eL {u roots T L} (hp:bu T) (nT:bJ T=true) (nR:roots.all bJ=true)
   (essential: ∀ a ∈ roots,i5 T roots a)
   (noRun:az u T L roots.toFinset):Lower u roots T (L+1):= by
 intro p bank h ha
 obtain ⟨k,S,hk,run,hs⟩:= gv hp nT nR h ha
 have he:roots.toFinset = S:= by
   ext a
   rw [List.mem_toFinset]
   refine ⟨fun hm => ?_,hs a⟩
   obtain ⟨r,s,hd,iso⟩:= essential _ hm
   exact ex run roots a hs r s hd iso
 by_contra! small
 exact noRun k (by omega) (he.symm ▸ run)
lemma gz {v:Sig} (hv:bu v): ¬aS (aF v):= by
 rintro ⟨b,h⟩
 have hr:Repr false [] v:= by
   apply mJ
   cases b
   · exact Or.inl (du fun i => (congrFun h i).trans (dg i).symm)
   · exact Or.inr (du fun i => (congrFun h i).trans (eV i).symm)
 have hr':cJ [] v:= hr
 exact (hr'.resolve_left (by simp)) hv
lemma pu {R} (a b:List (Wire R)):mass (a++b) = mass a + mass b:= by
 simp [mass]
lemma mG {R} (xs:List (Wire R)) (hc: ∀ x ∈ xs,aS x):
   mass xs = xs.length:= by
 induction xs with
 | nil => simp [mass]
 | cons a xs ih =>
   have ha:= hc a (by simp)
   simp only [gg,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
   omega
lemma l6 {u} {roots other:List Sig} {T G:Sig} (pT:bu T) (nT:bJ T=true) (nR:roots.all bJ=true) (pG:bu G)
   (r:Row → Row) (eq:cF r T = G)
   (dt: ∀ a ∈ roots,ad u (other.map aF) (aF (cF r a)))
   (singles:Finset Sig) (necessary: ∀ a ∈ singles,i5 T roots a)
   (constant: ∀ a ∈ singles,aS (aF (cF r a)))
   (L:Nat) (prior:Lower u other G L):Lower u roots T (L + singles.card):= by
 classical
 intro p bank hh ha
 obtain ⟨k,S,hk,run,sub⟩:= gv pT nT nR hh ha
 have subS:singles ⊆ S:= by
   intro a hs
   obtain ⟨i,j,hd,hiso⟩:= necessary a hs
   exact ex run roots a sub i j hd hiso
 let front:= singles.toList ++ (S \ singles).toList
 have nd:front.Nodup:= by
   simp only [front,List.nodup_append]
   refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
   intro a ha b hb he
   subst b
   exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
 have fe:front.toFinset=S:= by ext a;simp [front,Finset.union_sdiff_of_subset subS]
 have run':= m8 run front nd fe
 have gc:aD r (aF T) = aF G:= (dh _ _).symm.trans (congrArg aF eq)
 have supp:co u (other.map aF) ((front.map aF).map (aD r)):= by
   intro v hv
   obtain ⟨_,hm,rfl⟩:= List.mem_map.mp hv
   obtain ⟨a,hmem,rfl⟩:= List.mem_map.mp hm
   rw [←dh]
   exact dt a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
 have bound:= fg r run' (gc ▸ gz pG) Reach.start supp
   (L:=L) (gc ▸ prior)
 have massLo:singles.card ≤ mass ((front.map aF).map (aD r)):= by
   simp only [front,List.map_append,pu]
   let xs:= (singles.toList.map aF).map (aD r)
   have only: ∀ v ∈ xs,aS v:= by
     intro v hv
     obtain ⟨_,hm,rfl⟩:= List.mem_map.mp hv
     obtain ⟨a,hmem,rfl⟩:= List.mem_map.mp hm
     rw [←dh]
     exact constant _ (Finset.mem_toList.mp hmem)
   have sz:= mG xs only
   simp only [xs,List.length_map,Finset.length_toList] at sz
   change singles.card ≤ mass xs + _
   rw [sz]
   omega
 omega
def dd (ws:List Sig) (a b:Sig) (d:Nat) (ka kb:Bool):List Sig:=
 bin d a b::kept ka a (kept kb b ((ws.erase a).erase b))
lemma od {l:List Sig} (h:l.Nodup) (a:Sig):(l.erase a).toFinset = l.toFinset.erase a:= by
 ext x
 simp [h.mem_erase_iff]
lemma sl {u} {T:Sig} {cap:Nat} {ws:List Sig} (hn:ws.Nodup) (out:T ∉ ws)
   (twoStep: ∀ a ∈ ws,∀ b ∈ ws,∀ d,bK u d → ∀ ka kb,a ≠ b → bin d a b ∉ ws →
     bu (bin d a b) → (dd ws a b d ka kb).length ≤ cap →
     az u T (cap-1) (dd ws a b d ka kb).toFinset):
   az u T cap ws.toFinset:= by
 classical
 intro k hk h
 generalize he:ws.toFinset = S at h
 induction h using Live.ind with
 | stop hp =>
   have mem:T ∈ ws.toFinset:= he.symm ▸ Finset.mem_singleton_self _
   exact out (List.mem_toFinset.mp mem)
 | @binary k U a b d hd ha hb hab hf tail _ =>
   have am:a ∈ ws:= List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
   have bm:b ∈ ws:= List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
   have fresh:bin d a b ∉ ws:= fun h => hf (he ▸ List.mem_toFinset.mpr h)
   have hz:= mf tail _ (Finset.mem_insert_self _ _)
   let ka:= decide (a ∈ U)
   let kb:= decide (b ∈ U)
   let rest:= (ws.erase a).erase b
   have er:rest.toFinset = (ws.toFinset.erase a).erase b:= by
     rw [show rest=(ws.erase a).erase b by rfl,od (hn.erase _) b,
       od hn a]
   have ke:(kept ka a (kept kb b rest)).toFinset = U:= by
     rw [lr,lr,er,he]
     ext j
     by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases ja:j=a <;>
       by_cases jb:j=b <;> simp_all [ka,kb]
   have rn:rest.Nodup:= (hn.erase _).erase _
   have ar:a ∉ rest:= fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
   have br:b ∉ rest:= (hn.erase a).not_mem_erase
   have nk:= mC kb b rest rn br
   have ax:a ∉ kept kb b rest:= by cases kb <;> simp [kept,ar,hab]
   have nd:(dd ws a b d ka kb).Nodup:= by
     refine List.nodup_cons.mpr ⟨?_,mC ka a _ nk ax⟩
     intro h
     exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
   have eq:(dd ws a b d ka kb).toFinset = insert (bin d a b) U:= by
     change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
     simp [ke]
   have sc:= lP tail
   have len:(dd ws a b d ka kb).length ≤ cap:= by
     rw [←List.toFinset_card_of_nodup nd,eq]
     omega
   exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
def Sep (T:Sig) (width:Nat) (pos negRow:Fin width → Row)
   (asig:Sig → BitVec width × BitVec width):Prop:=
 (∀ i,bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
 ∀ w i,(asig w).1.getLsbD i.val = bit (pos i) w ∧
   (asig w).2.getLsbD i.val = bit (negRow i) w
def bc {n} (oriented:Bool) (s:BitVec n × BitVec n):BitVec n:=
 if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def dt {n} (oriented:Bool) (sig:Sig → BitVec n × BitVec n):List Sig → BitVec n
 | [] => 0
 | a::ws => bc oriented (sig a) ||| dt oriented sig ws
lemma pB {n:Nat} {oriented:Bool} {sig:Sig → BitVec n × BitVec n} {ws:List Sig} {i:Fin n}:
   (dt oriented sig ws).getLsbD i.val = true ↔
   ∃ a ∈ ws,(bc oriented (sig a)).getLsbD i.val = true:= by
 induction ws with
 | nil => simp [dt]
 | cons a ws ih =>
   simp only [dt,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
lemma o8 {u T k S} (h:Live u T k S) {ws:List Sig} (he:ws.toFinset=S)
   {width:Nat} {r s:Fin width → Row} {sig} (correct:Sep T width r s sig)
   (oriented:Bool) (zeroNot:oriented=true → u=false):
   dt oriented sig ws = BitVec.allOnes width:= by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 let i:Fin width:= ⟨j,hj⟩
 have yes:= (correct.1 i).1
 have no:= (correct.1 i).2
 rw [BitVec.getLsbD_allOnes];simp only [hj,decide_true]
 apply (pB (i:=i)).mpr
 cases oriented with
 | false =>
   obtain ⟨a,ha,hd⟩:= fn h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
   refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
   simp only [bc,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
   cases hx:bit (r i) a <;> cases hy:bit (s i) a <;> simp_all
 | true =>
   obtain ⟨a,ha,hp,hn⟩:= jj h (zeroNot rfl) yes no
   refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
   simp only [bc,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
     Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
lemma m2 {u T ws k} (h:Live u T k (List.toFinset ws)) {n:Nat} {r s:Fin n → Row} {sig}
   (correct:Sep T n r s sig):
   dt (!u) sig ws = BitVec.allOnes n:= by
 apply o8 h rfl correct
 simp
def Slice (u:Bool) (raw:List Sig) (T d:Sig) (L:Nat):Prop:=
 ∃ (f:Row → Row) (roots:List Sig),(∀ r,bit (f r) d = true) ∧
   (∀ a ∈ raw,ad u (roots.map aF) (aD f (aF a))) ∧
   ¬aS (aD f (aF T)) ∧
   ∀ p bank,Reach u (roots.map aF) p bank → ad u bank (aD f (aF T)) → L ≤ p
def bZ (d a:Sig):= a &&& d
def aY (u:Bool) (d:Sig) (pool:List Sig) (a:Sig):=
 let m:= bZ d a
 m == zero || m == d || (pool.map (bZ d)).any (fun v => v==m) ||
   (u && (let c:= bZ d (neg a);(pool.map (bZ d)).any (fun v => v==c)))
lemma nX {f:Row → Row} {d a b:Sig} (dom: ∀ r,bit (f r) d = true)
   (eq:bZ d a = bZ d b):
   aD f (aF a) = aD f (aF b):= by
 funext r
 have h:= congrArg (bit (f r)) eq
 change bit (f r) a = bit (f r) b
 simpa only [bit,bZ,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
   Bool.and_true] using h
lemma l7 {f:Row → Row} {d a:Sig} (dom: ∀ r,bit (f r) d = true)
   (eq:bZ d a = zero):aD f (aF a) = fun _ => false:= by
 funext r
 have he:= congrArg (bit (f r)) eq
 change bit (f r) a = false
 rw [dg] at he
 simpa only [bit,bZ,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
   Bool.and_true] using he
lemma mN {f:Row → Row} {d a:Sig} (dom: ∀ r,bit (f r) d = true)
   (eq:bZ d a = d):aD f (aF a) = fun _ => true:= by
 funext r
 have he:= congrArg (bit (f r)) eq
 change bit (f r) a = true
 rw [dom r] at he
 simpa only [bit,bZ,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
   Bool.and_true] using he
def ef (u:Bool) (f:Row → Row) (bank:List (Wire Row)) (pool:List Sig):=
 ∀ a ∈ pool,ad u bank (aD f (aF a))
lemma cv {u} {f:Row → Row} {d a:Sig} {bank pool}
   (dom: ∀ r,bit (f r) d = true) (supplyB:ef u f bank pool)
   (check:aY u d pool a = true):ad u bank (aD f (aF a)):= by
 simp only [aY,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
 rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
 · exact Or.inr (Or.inl ⟨false,l7 dom hz⟩)
 · exact Or.inr (Or.inl ⟨true,mN dom ho⟩)
 · exact nX dom he ▸ supplyB v hv
 · have h:= ik hu (nX dom he ▸ supplyB v hv)
   rw [qq] at h
   have e:inv (aD f (inv (aF a))) = aD f (aF a):= by
     funext r
     simp [inv,aD]
   rwa [e] at h
abbrev eR:= Nat × Sig × Sig
def bw (c:eR):= bin c.1 c.2.1 c.2.2
def is (u:Bool) (d:Nat):= decide (d<2) || (u && decide (d<4))
lemma pH {u d} (h:is u d=true):bK u d:= by
 simpa [is,bK] using h
def gn (u:Bool) (d:Sig) (pool:List Sig) (c:eR):=
 is u c.1 && (aY u d pool c.2.1 && aY u d pool c.2.2)
lemma m4 {u} {f:Row → Row} {d:Sig} {roots bank pool q}
   (dom: ∀ r,bit (f r) d = true) (hp:Reach u roots q bank) (hs:ef u f bank pool)
   (c:eR) (valid:gn u d pool c = true):
   ∃ next,Reach u roots (q+1) next ∧ ef u f next (bw c::pool):= by
 simp only [gn,Bool.and_eq_true] at valid
 obtain ⟨op,x,y,e,hx,hy,_,_⟩:= mM (pH valid.1) (cv dom hs valid.2.1)
   (cv dom hs valid.2.2)
 refine ⟨_,Reach.two op hp hx hy,?_⟩
 intro a hm
 rcases List.mem_cons.mp hm with rfl | hm
 · rw [bw,qw,ju,e]
   exact Or.inl (by simp)
 · exact cC _ (hs _ hm)
def hD (u:Bool) (d:Sig) (pool:List Sig):List eR → Option (List Sig)
 | [] => some pool
 | c::cs => if gn u d pool c then hD u d (bw c::pool) cs else none
lemma iV {u} {d:Sig} {f:Row → Row} (dom: ∀ r,bit (f r) d = true)
   {roots bank q pool} (hp:Reach u roots q bank) (hs:ef u f bank pool)
   (cs:List eR) {result} (ok:hD u d pool cs = some result):
   ∃ next,Reach u roots (q+cs.length) next ∧ ef u f next result:= by
 induction cs generalizing bank q pool with
 | nil => cases ok;exact ⟨_,hp,hs⟩
 | cons c cs ih =>
   simp only [hD] at ok
   split at ok
   next h =>
     obtain ⟨next,hr,sh⟩:= m4 dom hp hs c h
     obtain ⟨out,hr',sh'⟩:= ih hr sh ok
     exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
   next => contradiction
def aE (d a:Sig):= bZ d a == zero || bZ d a == d
lemma iM {d:Sig} {f:Row → Row} (dom: ∀ r,bit (f r) d = true)
   (ws:List Sig):ws.countP (aE d) ≤ mass ((ws.map aF).map (aD f)):= by
 classical
 induction ws with
 | nil => simp [mass]
 | cons a ws ih =>
   simp only [List.countP_cons,List.map_cons,gg]
   cases h:aE d a
   · simpa using (Nat.le_add_left _ _ |> ih.trans)
   · have hc:aS (aD f (aF a)):= by
       have hh:bZ d a = zero ∨ bZ d a = d:= by simpa only [aE,Bool.or_eq_true,beq_iff_eq] using h
       rcases hh with hz | ho
       · exact ⟨false,l7 dom hz⟩
       · exact ⟨true,mN dom ho⟩
     simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def kz (u:Bool) (d:Sig) (L k p:Nat) (pool ws:List Sig):=
 decide (k+p < L+ws.countP (aE d)) && ws.all (aY u d pool)
lemma jm {u raw T d L} (slice:Slice u raw T d L) (cs:List eR)
   {pool ws cap} (built:hD u d raw cs = some pool)
   (nd:ws.Nodup) (cut:kz u d L cap cs.length pool ws = true):
   az u T cap ws.toFinset:= by
 intro k hk h
 obtain ⟨f,roots,dom,base,nc,lo⟩:= slice
 obtain ⟨bank,hr,hs⟩:= iV dom (Reach.start (roots:=roots.map aF)) base cs built
 simp only [kz,Bool.and_eq_true,decide_eq_true_eq] at cut
 obtain ⟨ineq,all⟩:= cut
 have coveredS:co u bank ((ws.map aF).map (aD f)):= by
   intro v hv
   obtain ⟨_,hm,rfl⟩:= List.mem_map.mp hv
   obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hm
   exact cv dom hs (List.all_eq_true.mp all a ha)
 have b:= fg f (m8 h ws nd rfl) nc hr coveredS lo
 have massLo:= iM dom ws
 have hu:= ineq
 simp only [Nat.zero_add] at b
 omega
abbrev Move:= Sig × Sig × Row
def mA (d r:Row):Row:=
 if h:r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def oe (d:Row):Row:= Fin.ofNat 512 (512-d.val)
def oC (m:Move) (r:Row):Row:=
 if bit r m.1 then mA m.2.2 r else if bit r m.2.1 then mA (oe m.2.2) r else r
def mux (m a b:Sig):= (m &&& a) ||| (~~~m &&& b)
def iQ (m:Move) (a:Sig):=
 mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (oe m.2.2).val) a)
lemma rf (d r:Row) (a:Sig):bit r (a.rotateRight d.val) = bit (mA d r) a:= by
 unfold bit
 rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
 by_cases h:r.val < 512-d.val <;> simp [mA,h,r.isLt]
lemma sq (p x y:Bool):(p && x || !p && y) = (if p then x else y):= by cases p <;> simp
lemma vc (r:Row) (m a b:Sig):
   bit r (mux m a b) = if bit r m then bit r a else bit r b:= by
 simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
   decide_true,Bool.true_and]
 exact sq _ _ _
lemma tw (r:Row) (m:Move) (a:Sig):bit r (iQ m a) = bit (oC m r) a:= by
 simp only [iQ,vc,rf,oC]
 cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def cD (ms:List Move) (r:Row):= ms.foldl (fun j m => oC m j) r
def bg (ms:List Move) (a:Sig):= ms.foldr iQ a
lemma il (ms:List Move) (a:Sig) (r:Row):
   bit r (bg ms a) = bit (cD ms r) a:= by
 induction ms generalizing r with
 | nil => rfl
 | cons m ms ih => exact (tw r m _).trans (ih _)
lemma cj (ms:List Move) (a:Sig):bg ms a = cF (cD ms) a:= by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 exact (il ms a ⟨j,hj⟩).trans (de _ _ ⟨j,hj⟩).symm
def m0 (roots:List Sig) (w:Sig):= w==zero || w==one || roots.contains w
lemma pg {u roots w} (ok:m0 roots w = true):
   ad u (roots.map aF) (aF w):= by
 simp only [m0,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
 rcases ok with (rfl | rfl) | hm
 · exact Or.inr (Or.inl ⟨false,funext dg⟩)
 · exact Or.inr (Or.inl ⟨true,funext eV⟩)
 · exact Or.inl (List.mem_map_of_mem hm)
def fd (ms:List Move) (raw:List Sig) (T:Sig) (base:List Sig) (G:Sig):=
 bg ms T == G && raw.all (fun a => m0 base (bg ms a))
lemma i2 {u ms raw T base G} (ok:fd ms raw T base G = true):
   cF (cD ms) T = G ∧
   ∀ a ∈ raw,ad u (base.map aF) (aF (cF (cD ms) a)):= by
 simp only [fd,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,cj] at ok
 exact ⟨ok.1,fun a ha => pg (ok.2 a ha)⟩
lemma sf {u ms raw T base G L} (ok:fd ms raw T base G = true)
   (pT:bu T) (nT:bJ T=true) (nR:raw.all bJ=true) (pG:bu G)
   (hL:Lower u base G L):Lower u raw T L:= by
 obtain ⟨eq,supp⟩:= i2 ok
 simpa using l6 pT nT nR pG (cD ms) eq supp ∅ (by simp) (by simp) L hL
lemma nW {u ms raw T base G L d} (ok:fd ms raw T base G = true)
   (all:bg ms d = one) (properG:bu G) (hL:Lower u base G L):
   Slice u raw T d L:= by
 obtain ⟨eq,supp⟩:= i2 ok
 have obs:aD (cD ms) (aF T) = aF G:=
   (dh _ _).symm.trans (congrArg aF eq)
 refine ⟨cD ms,base,?_,?_,?_,?_⟩
 · intro r
   rw [←il,all,eV]
 · intro a ha
   rw [←dh]
   exact supp a ha
 · rw [obs]
   exact gz properG
 · rw [obs]
   exact hL
def kx (T:Sig) (roots:List Sig) (a:Sig) (rs:Row × Row):=
 (bit rs.1 T != bit rs.2 T) &&
 roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
lemma iT {T roots a rs} (ok:kx T roots a rs = true):i5 T roots a:= by
 simp only [kx,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
 exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def bU (T:Sig) (raw:List Sig) (xs:List (Sig × Row × Row)):=
 bJ T && raw.all bJ && xs.all (fun a => kx T raw a.1 a.2)
lemma ga {T raw xs} (ok:bU T raw xs = true):
   ∀ a ∈ (xs.map Prod.fst).toFinset,i5 T raw a:= by
 simp only [bU,Bool.and_eq_true] at ok
 intro a ha
 obtain ⟨⟨a,r,s⟩,hm,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp ha)
 exact iT (List.all_eq_true.mp ok.2 _ hm)
lemma bX {T raw xs} (ok:bU T raw xs = true):
   bJ T=true ∧ raw.all bJ=true:= by
 simp only [bU,Bool.and_eq_true] at ok
 exact ok.1
lemma pF {u raw T} (properT:bu T) (xs:List (Sig × Row × Row))
   (ok:bU T raw xs = true):
   Lower u raw T ((xs.map Prod.fst).toFinset.card-1):= by
 intro p bank hr hit
 obtain ⟨k,S,hk,run,sub⟩:= gv properT (bX ok).1 (bX ok).2 hr hit
 have le:(xs.map Prod.fst).toFinset.card ≤ S.card:= by
   apply Finset.card_le_card
   intro a ha
   obtain ⟨r,s,hd,iso⟩:= ga ok a ha
   exact ex run raw a sub r s hd iso
 have bound:= lP run
 omega
def lZ (ms:List Move) (T:Sig) (raw:List Sig) (base:List Sig) (G:Sig)
   (xs:List (Sig × Row × Row)):=
 fd ms raw T base G && bU T raw xs &&
   xs.all (fun a => bg ms a.1 == zero || bg ms a.1 == one)
lemma uw {u ms T raw base G xs L} (ok:lZ ms T raw base G xs = true)
   (properT:bu T) (properG:bu G) (low:Lower u base G L):
   Lower u raw T (L+(xs.map Prod.fst).toFinset.card):= by
 simp only [lZ,Bool.and_eq_true] at ok
 obtain ⟨eq,supp⟩:= i2 ok.1.1
 apply l6 properT (bX ok.1.2).1 (bX ok.1.2).2 properG _ eq supp _ (ga ok.1.2) _ L low
 intro a ha
 obtain ⟨⟨v,r,s⟩,hm,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp ha)
 have hh:= List.all_eq_true.mp ok.2 _ hm
 simp only [Bool.or_eq_true,beq_iff_eq,cj] at hh
 rcases hh with h | h
 · rw [h]
   exact ⟨false,funext dg⟩
 · rw [h]
   exact ⟨true,funext eV⟩
def dy (m:Nat):List (Nat × Sig):=
 (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m:Nat):= (dy m).map Prod.snd
def lz (t:Nat):Sig:= bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m:Nat):List Sig:= if m<512 then vars m else vars m ++ [lz (m/512-1)]
def mS (m j:Nat):= if m.testBit j then inputs.getD j zero else zero
def au (m:Nat):Sig:=
 let x:= mS m
 (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
   (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
   (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def dX:Nat → Nat
 | 0 => 0xff
 | 1 => 0x55
 | 2 => 0x33
 | 3 => 0x11
 | 4 => 0xf
 | 5 => 0x5
 | 6 => 0x3
 | _ => 0x1
def dY:Nat → Nat
 | 0 => 0x101010101010101
 | 1 => 0x1000100010001
 | 2 => 0x10100000101
 | 3 => 0x100000001
 | 4 => 0x1010101
 | 5 => 0x10001
 | 6 => 0x101
 | _ => 0x1
def dZ:Nat → Nat
 | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
 | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
 | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
 | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
 | 4 => 0x1000000000000000100000000000000010000000000000001
 | 5 => 0x100000000000000000000000000000001
 | 6 => 0x10000000000000001
 | _ => 0x1
def hQ (z o:Nat):Sig:=
 let fixed:= z ||| o
 if z &&& o != 0 then zero else
   BitVec.ofNat 512 ((dX (fixed &&& 7)*dY ((fixed >>> 3) &&& 7)*dZ ((fixed >>> 6) &&& 7)) <<< o)
def oJ (z o:Nat):List Move:=
 (List.range 9).filterMap fun j =>
   let x:= inputs.getD j zero
   let step:= Fin.ofNat 512 (1 <<< j)
   if z.testBit j then some (zero,x,step)
   else if o.testBit j then some (~~~x,zero,step) else none
def cY (v:Nat):Move:=
 let i:= v &&& 15
 let j:= v >>> 4
 let a:= inputs.getD i zero
 let b:= inputs.getD j zero
 let d:= (1 <<< j)-(1 <<< i)
 (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def ku (t:Nat) (mask:Nat):List (Sig × Row × Row):=
 (dy mask).map fun (i,a) =>
   let r:= if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
   (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def pW (m hints:Nat):List (Sig × Row × Row):=
 (dy m).map fun (i,a) =>
   let r:= 1 <<< ((hints >>> (4*i)) &&& 15)
   (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def cS (T:Sig):= T != zero && T != one
lemma dp (T:Sig) (h:cS T = true):bu T:= by
 simpa only [cS,bu,Bool.and_eq_true,bne_iff_ne] using h
def aU (x off width:Nat):= (x >>> off) % 2^width
def ew {α:Type} (width:Nat) (read:Nat → α):Nat → Nat → List α
 | 0,_ => []
 | k+1,x => read x::ew width read k (x >>> width)
abbrev aZ:= Nat × Nat × Nat × Nat × Nat
def os (m z o:Nat):= m ^^^ (m &&& (z ||| o))
def ej (m:Nat):Sig:= au m
def hO (m:Nat) (c:aZ):Nat:= m % 512+512*(c.1/512)
def gm (m:Nat) (c:aZ) (prior:Nat → Nat):Bool:=
 let (z,o,q,s,L):= c
 let ms:= oJ z o
 let raw:= hO m c
 let free:= os raw (z % 512) o
 let G:= bg ms (ej m)
 let xs:= ku (z/512+80) s
 let count:= (xs.map Prod.fst).toFinset.card
 cS G && fd ms (varsX raw) (ej m) (varsX free) G &&
   (bg ms (hQ z o)==one) &&
   (if q=0 then bU G (varsX free) xs && decide (L ≤ count-1)
    else cS (au q) &&
      lZ (oJ (os free q 0) 0) G (varsX free) (varsX q) (au q) xs &&
      decide (L ≤ prior q+count))
lemma ig {u} {m:Nat} (c:aZ) (prior:Nat → Nat)
   (valid: ∀ q,Lower u (varsX q) (au q) (prior q))
   (ok:gm m c prior = true):Slice u (varsX (hO m c)) (ej m) (hQ c.1 c.2.1) c.2.2.2.2:= by
 revert ok
 obtain ⟨z,o,q,s,L⟩:= c
 intro ok
 let ms:= oJ z o
 let raw:= hO m (z,o,q,s,L)
 let free:= os raw (z % 512) o
 let G:= bg ms (ej m)
 let xs:= ku (z/512+80) s
 change (((cS G && fd ms (varsX raw) (ej m) (varsX free) G) &&
   (bg ms (hQ z o)==one)) && _) = true at ok
 simp only [Bool.and_eq_true,beq_iff_eq] at ok
 apply nW ok.1.1.2 ok.1.2 (dp _ ok.1.1.1)
 intro p bank hr ha
 have hh:= ok.2
 by_cases hq:q=0
 · simp only [gm,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
   exact hh.2.trans (pF (dp _ ok.1.1.1) xs hh.1 p bank hr ha)
 · simp only [gm,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
   exact hh.2.trans (uw hh.1.2 (dp _ ok.1.1.1) (dp _ hh.1.1) (valid q) p bank hr ha)
def mB (old rep:Nat) (swaps:List Nat):=
 (cS (au old) && bJ (au old) && (varsX old).all bJ) && cS (au rep) &&
   fd (swaps.map cY) (varsX old) (au old) (varsX rep) (au rep)
lemma pe {u old rep L swaps} (ok:mB old rep swaps = true)
   (h:Lower u (varsX rep) (au rep) L):Lower u (varsX old) (au old) L:= by
 simp only [mB,Bool.and_eq_true] at ok
 exact sf ok.2 (dp _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (dp _ ok.1.2) h
def aI (entries:List (Nat × Nat)) (q:Nat):=
 ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
lemma ag {u} (entries:List (Nat × Nat))
   (sound: ∀ e ∈ entries,Lower u (varsX e.1) (au e.1) e.2) (q:Nat):
   Lower u (varsX q) (au q) (aI entries q):= by
 unfold aI
 cases h:entries.find? (fun a => a.1 == q) with
 | none => exact fun _ _ _ _ => Nat.zero_le _
 | some e =>
   have he:= List.mem_of_find?_eq_some h
   have hit:(fun a:Nat × Nat => a.1 == q) e = true:= List.find?_some (p:=fun a:Nat × Nat => a.1 == q) (a:=e) h
   have eq:e.1=q:= beq_iff_eq.mp hit
   simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev bG:= Sig × Nat × Nat × List Sig
def bG.domain (c:bG):Sig:= c.1
def bG.bound (c:bG):Nat:= c.2.1
def bG.paid (c:bG):Nat:= c.2.2.1
def bG.wires (c:bG):List Sig:= c.2.2.2
def ei (u:Bool) (raw:List Sig) (T:Sig) (c:bG):=
 ∃ (f:Row → Row) (roots:List Sig) (bank:List (Wire Row)),
   (∀ r,bit (f r) c.domain = true) ∧ ¬aS (aD f (aF T)) ∧
   (∀ q ws,Reach u (roots.map aF) q ws → ad u ws (aD f (aF T)) → c.bound ≤ q) ∧
   Reach u (roots.map aF) c.paid bank ∧ ef u f bank c.wires ∧ True
lemma o4 {u raw T d lb} (h:Slice u raw T d lb) (cs:List eR) {ws}
   (build:hD u d raw cs = some ws):ei u raw T ⟨d,lb,cs.length,ws⟩:= by
 obtain ⟨f,roots,dom,sup,nc,prior⟩:= h
 obtain ⟨bank,hr,hs⟩:= iV dom (Reach.start (roots:=roots.map aF)) sup cs build
 exact ⟨f,roots,bank,dom,nc,prior,by simpa [bG.paid] using hr,hs,trivial⟩
lemma nP {u raw T c} (valid:ei u raw T c) (k:Nat) (rest:List Sig)
   (choice:eR) (paid:Bool)
   (known: ∀ a ∈ rest,aY u c.domain c.wires a = true)
   (buy:if paid then gn u c.domain c.wires choice = true
      else aY u c.domain c.wires (bw choice) = true)
   (bound:k+c.paid+paid.toNat <
     c.bound+(bw choice::rest).countP (aE c.domain))
   (nd:(bw choice::rest).Nodup):
   az u T k (bw choice::rest).toFinset:= by
 intro t ht run
 obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:= valid
 let ws:= bw choice::rest
 have done (n:Nat) (out:List (Wire Row)) (reach:Reach u (roots.map aF) n out)
     (zs:ef u f out (bw choice::rest)) (le:n = c.paid+paid.toNat):False:= by
   have dt:co u out ((ws.map aF).map (aD f)):= by
     intro v hv
     obtain ⟨_,hm,rfl⟩:= List.mem_map.mp hv
     obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hm
     exact zs _ ha
   have b:= fg f (m8 run ws nd rfl) nc reach dt lo
   have cm:= iM dom ws
   change k+c.paid+paid.toNat < c.bound+ws.countP (aE c.domain) at bound
   omega
 cases paid with
 | false =>
   apply done _ _ hp _ rfl
   intro a h
   rcases List.mem_cons.mp h with rfl | hm
   · exact cv dom hs buy
   · exact cv dom hs (known _ hm)
 | true =>
   obtain ⟨out,hr,hc⟩:= m4 dom hp hs choice buy
   apply done _ _ hr _ rfl
   intro a h
   rcases List.mem_cons.mp h with rfl | hm
   · exact hc _ (by simp)
   · have point: ∀ v ∈ c.wires,ad u out (aD f (aF v)):=
       fun v hu => hc v (List.mem_cons_of_mem _ hu)
     exact cv dom point (known _ hm)
def cp (u:Bool) (c:bG) (k:Nat) (rest:List Sig) (op:eR):=
 let z:= bw op
 let extra:= !(aY u c.domain c.wires z)
 ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (aE c.domain)) &&
   rest.all (aY u c.domain c.wires)) && (!extra || gn u c.domain c.wires op)
lemma ji {u raw T c} (valid:ei u raw T c) {k rest op}
   (nd:(bw op::rest).Nodup) (cut:cp u c k rest op = true):
   az u T k (bw op::rest).toFinset:= by
 let extra:= !(aY u c.domain c.wires (bw op))
 apply nP valid k rest op extra _ _ _ nd
 · simp only [cp,Bool.and_eq_true,List.all_eq_true] at cut
   exact cut.1.2
 · simp only [cp,Bool.and_eq_true,Bool.or_eq_true] at cut
   cases he:aY u c.domain c.wires (bw op) <;> simp_all [extra]
 · simp only [cp,Bool.and_eq_true,decide_eq_true_eq] at cut
   exact cut.1.1
def iZ (u:Bool) (raw:List Sig) (cs:List eR) (d:Sig) (lb:Nat):Option bG:=
 (hD u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
lemma ly {u raw T d L cs c} (slice:Slice u raw T d L)
   (h:iZ u raw cs d L = some c):ei u raw T c:= by
 unfold iZ at h
 cases he:hD u d raw cs with
 | none => simp [he] at h
 | some pool =>
   simp only [he,Option.map_some,Option.some.injEq] at h
   subst c
   exact o4 slice cs he
abbrev Bits:= BitVec 152
abbrev mz:= Bits × Bits
abbrev Decor:= Sig × mz
def gl {n:Nat} (r:Fin n → Row) (v:Sig):BitVec n:=
 (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
lemma cX {n:Nat} (r:Fin n → Row) (v:Sig) (i:Fin n):
   (gl r v).getLsbD i.val = bit (r i) v:= by
 simp only [gl,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
 simp [i.isLt]
def eW (r s:Fin 152 → Row) (a:Sig):mz:= (gl r a,gl s a)
def e8 (T:Sig) (r s:Fin 152 → Row):=
 ∀ i,bit (r i) T = true ∧ bit (s i) T = false
lemma tm {T r s} (h:e8 T r s):Sep T 152 r s (eW r s):= by
 exact ⟨h,fun a i => ⟨cX _ _ _,cX _ _ _⟩⟩
def cK (r s:Fin 152 → Row) (x:Decor):= x.2 = eW r s x.1
def bv {n:Nat} (d:Nat) (a b:BitVec n):BitVec n:=
 if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d:Nat) (x y:Decor):Decor:= (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
lemma p9 {n:Nat} (r:Fin n → Row) (d:Nat) (a b:Sig):
   gl r (bin d a b) = bv d (gl r a) (gl r b):= by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 have h:= cX r (bin d a b) ⟨j,hj⟩
 rw [hU,←cX r a ⟨j,hj⟩,←cX r b ⟨j,hj⟩] at h
 rw [h]
 unfold bv
 split_ifs <;> simp [hj]
lemma lm {r s x y} (d) (hx:cK r s x) (hy:cK r s y):
   cK r s (dbin d x y):= by
 change x.2 = _ at hx
 change y.2 = _ at hy
 simp only [cK,dbin,eW,p9,hx,hy]
def bq:Decor:= (zero,0,0)
lemma lW (r s):cK r s bq:= by
 apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
 · change (0:Bits).getLsbD j = (gl r zero).getLsbD j
   rw [show (gl r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from cX _ _ ⟨j,hj⟩,dg]
   simp
 · change (0:Bits).getLsbD j = (gl s zero).getLsbD j
   rw [show (gl s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from cX _ _ ⟨j,hj⟩,dg]
   simp
lemma lB {r s ws} (all: ∀ v ∈ ws,cK r s v) (i:Nat):
   cK r s (List.getD ws i bq):= by
 simp only [List.getD_eq_getElem?_getD]
 cases e:ws[i]? with
 | none => exact lW _ _
 | some v => exact all _ (List.mem_of_getElem? e)
def gr (n:Nat) (bits:Nat) (ws:List Decor):List Decor:=
 match n with
 | 0 => ws
 | k+1 =>
   let a:= ws.getD (bits &&& 15) bq
   let b:= ws.getD ((bits >>> 4) &&& 15) bq
   gr k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
lemma mx (n bits) (ws) (r s) (base: ∀ v ∈ ws,cK r s v):
   ∀ v ∈ gr n bits ws,cK r s v:= by
 induction n generalizing ws bits with
 | zero => exact base
 | succ n ih =>
   apply ih
   intro v hv
   rcases List.mem_append.mp hv with hw | hz
   · exact base _ hw
   · obtain rfl:= List.mem_singleton.mp hz
     exact lm _ (lB base _) (lB base _)
def asRow (cols:Nat → Bits) (i:Fin 152):Row:=
 (BitVec.ofBoolListLE (List.ofFn (fun j:Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
   (by simp [List.length_ofFn])
lemma w2: ∀ r:Row,bit r (inputs.getD 0 zero) = r.val.testBit 0:= by decide +kernel
lemma w3: ∀ r:Row,bit r (inputs.getD 1 zero) = r.val.testBit 1:= by decide +kernel
lemma w4: ∀ r:Row,bit r (inputs.getD 2 zero) = r.val.testBit 2:= by decide +kernel
lemma w5: ∀ r:Row,bit r (inputs.getD 3 zero) = r.val.testBit 3:= by decide +kernel
lemma w6: ∀ r:Row,bit r (inputs.getD 4 zero) = r.val.testBit 4:= by decide +kernel
lemma w7: ∀ r:Row,bit r (inputs.getD 5 zero) = r.val.testBit 5:= by decide +kernel
lemma w8: ∀ r:Row,bit r (inputs.getD 6 zero) = r.val.testBit 6:= by decide +kernel
lemma w9: ∀ r:Row,bit r (inputs.getD 7 zero) = r.val.testBit 7:= by decide +kernel
lemma wA: ∀ r:Row,bit r (inputs.getD 8 zero) = r.val.testBit 8:= by decide +kernel
lemma iI: ∀ (j:Fin 9) (r:Row),
   bit r (inputs.getD j.val zero) = r.val.testBit j.val:= by
 intro j r
 fin_cases j
 · exact w2 r
 · exact w3 r
 · exact w4 r
 · exact w5 r
 · exact w6 r
 · exact w7 r
 · exact w8 r
 · exact w9 r
 · exact wA r
lemma lG (cols:Nat → Bits) (i:Fin 152) (j:Fin 9):
   bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val:= by
 rw [iI]
 change (BitVec.ofBoolListLE (List.ofFn (fun h:Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
 simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
 simp [j.isLt]
def lq (m:Nat) (p q:Nat → Bits):List Decor:=
 (dy m).map (fun (j,a) => (a,p j,q j))
lemma iY {m j a} (h:(j,a) ∈ dy m):
   j<9 ∧ a=inputs.getD j zero:= by
 obtain ⟨v,hv,hh⟩:= List.mem_filterMap.mp h
 simp only [List.mem_range] at hv
 split at hh
 next =>
   cases hh
   exact ⟨hv,rfl⟩
 next => contradiction
lemma oN (m) (p q:Nat → Bits):
   ∀ a ∈ lq m p q,cK (asRow p) (asRow q) a:= by
 intro a ha
 obtain ⟨⟨j,v⟩,hv,rfl⟩:= List.mem_map.mp ha
 obtain ⟨hj,rfl⟩:= iY hv
 apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
 · exact (lG p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (cX _ _ ⟨i,hi⟩).symm
 · exact (lG q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (cX _ _ ⟨i,hi⟩).symm
def mX (m:Nat) (v:Nat → Bits):Bits:=
 let x:= fun j => if m.testBit j then v j else 0
 (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
   (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
   (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
lemma qk (m:Nat) (v:Nat → Bits) (i:Fin 152) (j:Fin 9):
   bit (asRow v i) (mS m j.val) =
   ((if m.testBit j.val then v j.val else 0):Bits).getLsbD i.val:= by
 by_cases hh:m.testBit j.val = true
 · simpa [mS,hh] using lG v i j
 · simp [mS,hh,dg]
lemma ox (m:Nat) (v:Nat → Bits) (i:Fin 152):
   bit (asRow v i) (au m) = (mX m v).getLsbD i.val:= by
 have pos (j:Nat) (hj:j<9):(mS m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0):Bits).getLsbD i.val:= qk m v i ⟨j,hj⟩
 simp only [bit,au,mX,BitVec.getLsbD_and,BitVec.getLsbD_or]
 simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:= Bits × Bits × Bits
def eO (z:Bits) (c:Cov):Cov:=
 (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
  (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def bM (d:Bool) (v:List Decor):Cov:=
 v.foldr (fun a c => eO (bc d a.2) c) (0,0,0)
def gf (c:Cov) (a:Bits):Bits:= c.1 &&& ~~~(c.2.1 &&& a)
def i7 (c:Cov) (a b:Bits):Bits:=
 c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private lemma vd (c:Cov) (a:Bits):gf (eO a c) a=c.1:= by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [gf,eO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private lemma uk (c:Cov) (a b:Bits):i7 (eO a (eO b c)) a b=c.1:= by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [i7,eO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
   cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private lemma tz (c:Cov) (a b:Bits):eO a (eO b c)=eO b (eO a c):= by
 apply Prod.ext
 · apply BitVec.eq_of_getLsbD_eq
   intro i hi
   simp only [eO,BitVec.getLsbD_or]
   cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
 · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
     simp only [eO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
     cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
     cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private lemma o6 (d:Bool) {l r:List Decor} (h:l.Perm r):bM d l=bM d r:= by
 induction h with
 | nil => rfl
 | cons a _ ih => exact congrArg (eO (bc d a.2)) ih
 | swap a b t => exact tz _ _ _
 | trans _ _ h1 h2 => exact h1.trans h2
lemma ub (d:Bool) (v:List Decor) {r s} (good: ∀ a ∈ v,cK r s a):
   (bM d v).1 = dt d (eW r s) (v.map Prod.fst):= by
 induction v with
 | nil => rfl
 | cons a v ih =>
   change (bc d a.2 ||| (bM d v).1) = bc d (eW r s a.1) ||| _
   rw [show a.2=eW r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def fh (ws:List Decor) (a:Decor) (keep:Bool):=
 if keep then ws else ws.erase a
def cB (ws:List Decor) (a b:Decor) (ka kb:Bool):=
 fh (fh ws a ka) b kb
lemma i1 {ws:List Decor} (a:Decor) (ha:a ∈ ws):
   ws.Perm (a::ws.erase a):= List.perm_cons_erase ha
lemma oq {ws:List Decor} (d:Bool) (a:Decor) (ha:a ∈ ws) (keep:Bool):
   (bM d (fh ws a keep)).1 =
     (if keep then (bM d ws).1 else gf (bM d ws) (bc d a.2)):= by
 cases keep
 · change (bM d (ws.erase a)).1 = gf (bM d ws) _
   rw [o6 d (i1 a ha)]
   exact (vd _ _).symm
 · rfl
lemma pq {ws:List Decor} (a b:Decor) (ha:a ∈ ws) (hb:b ∈ ws) (hne:a≠b):
   ws.Perm (a::b::(ws.erase a).erase b):= by
 have hm:b ∈ ws.erase a:= (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
 exact (i1 a ha).trans (List.Perm.cons _ (i1 b hm))
lemma rh {ws:List Decor} (d:Bool) (a b:Decor) (ha:a ∈ ws) (hb:b ∈ ws)
   (ne:a ≠ b) (ka kb:Bool):
   (bM d (cB ws a b ka kb)).1 =
     (if ka then (if kb then (bM d ws).1 else gf (bM d ws) (bc d b.2))
      else if kb then gf (bM d ws) (bc d a.2)
      else i7 (bM d ws) (bc d a.2) (bc d b.2)):= by
 cases ka <;> cases kb
 · change (bM d ((ws.erase a).erase b)).1 = i7 (bM d ws) _ _
   rw [o6 d (pq a b ha hb ne)]
   exact (uk _ _ _).symm
 · exact oq d a ha false
 · exact oq d b hb false
 · rfl
def gh (a b:List Sig):= (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
lemma fj {xs ys} (h:gh xs ys = true):xs.toFinset=ys.toFinset:= by
 simp only [gh,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
 ext a
 simp only [List.mem_toFinset]
 exact ⟨h.1 a,h.2 a⟩
def eo (v:Sig):=
 let n:= v.toNat % 2305843009213693951
 (n*(n+971)) % 2305843009213693951
def m9 (xs:List Sig):= xs.foldl (fun v x => v+eo x) 0
def eP (u:Bool) (pools:List bG) (links:Nat → List (List Sig)) (k:Nat)
   (rest:List Sig) (op:eR):=
 let ws:= bw op::rest
 (links (m9 ws)).any (gh ws) || pools.any (fun p => cp u p k rest op)
lemma lH {u raw T pools links k rest op}
   (pValid: ∀ p ∈ pools,ei u raw T p)
   (lValid: ∀ tag xs,xs ∈ links tag → az u T k (List.toFinset xs))
   (nd:(bw op::rest).Nodup)
   (h:eP u pools links k rest op = true):
   az u T k (bw op::rest).toFinset:= by
 simp only [eP,Bool.or_eq_true,List.any_eq_true] at h
 rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
 · rw [fj ok]
   exact lValid _ _ hx
 · exact ji (pValid _ hp) nd ok
abbrev qv:= Cov × Bool
def nn (u:Bool) (ws:List Decor):qv:= (bM (!u) ws,u)
def iD (v:Cov) (a b:Bits) (ka kb:Bool):=
 if ka then (if kb then v.1 else gf v b) else if kb then gf v a else i7 v a b
lemma kl (ws:List Decor) (a:Decor) (k:Bool):(fh ws a k).Sublist ws:= by
 cases k
 · exact List.erase_sublist
 · exact List.Sublist.refl _
lemma ti (ws:List Decor) (a b:Decor) (ka kb:Bool):
   (cB ws a b ka kb).Sublist ws:= (kl _ _ _).trans (kl _ _ _)
lemma ss (ws:List Decor) (a b:Decor) (ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b):
   (cB ws a b ka kb).length =
     ws.length - (if ka then 0 else 1) - (if kb then 0 else 1):= by
 have hm:b ∈ ws.erase a:= (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
 cases ka <;> cases kb <;> simp [cB,fh,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def bW (op:Nat) (a b:Decor):eR:= (op,a.1,b.1)
abbrev bd:= Nat × Nat × List Decor × qv × List bG × (Nat → List (List Sig))
def eZ (c:bd) (op:Nat) (a b z:Decor) (ka kb:Bool):=
 let (cap,n,ws,cov,pools,links):= c
 let len:= 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
 if len>cap then true else
   let d:= !cov.2
   let rs:= iD cov.1 (bc d a.2) (bc d b.2) ka kb
   if (rs ||| bc d z.2) != BitVec.allOnes 152 then true else
   if !cS z.1 || ws.any (fun v => v.1==z.1) then true else
     let rest:= (cB ws a b ka kb).map Prod.fst
     eP cov.2 pools links (cap-1) rest (bW op a b)
def lK (ws:List Decor) (op:Nat) (a b:Decor) (ka kb:Bool):=
 (dbin op a b).1::(cB ws a b ka kb).map Prod.fst
lemma mH {u raw T r s ws pools links cap a b op ka kb}
   (pairs:e8 T r s) (faith: ∀ w ∈ ws,cK r s w)
   (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws)
   (ne:a≠b) (hcap:0<cap)
   (pv: ∀ p ∈ pools,ei u raw T p)
   (lv: ∀ tag xs,xs ∈ links tag → az u T (cap-1) (List.toFinset xs))
   (pro:bu (dbin op a b).1) (fresh:(dbin op a b).1 ∉ ws.map Prod.fst)
   (test:eZ (cap,ws.length,ws,nn u ws,pools,links) op a b (dbin op a b) ka kb = true):
   az u T (cap-1) (lK ws op a b ka kb).toFinset:= by
 let z:= dbin op a b
 let rest:= cB ws a b ka kb
 let child:= z.1::rest.map Prod.fst
 have sub:rest.Sublist ws:= ti _ _ _ _ _
 have ndc:child.Nodup:= List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
   nd.sublist (sub.map _)⟩
 have fr:ws.any (fun v => v.1==z.1) = false:= by
   apply Bool.eq_false_iff.mpr
   intro hh
   obtain ⟨x,hx,he⟩:= List.any_eq_true.mp hh
   exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
 have pp:cS z.1 = true:= by simpa [cS,bu] using pro
 have leq:1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length:= by
   change _ = (z.1::rest.map Prod.fst).length
   rw [List.length_cons,List.length_map,ss _ _ _ _ _ ha hb ne,Nat.add_comm 1]
 intro k hk h
 have hsz:= lP h
 change child.toFinset.card ≤ k+1 at hsz
 rw [List.toFinset_card_of_nodup ndc] at hsz
 have len:child.length ≤ cap:= by omega
 unfold eZ at test
 change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
 rw [leq,if_neg (by omega)] at test
 have sep:= m2 h (tm pairs)
 let d:= !u
 have g:(bM d rest).1 = dt d (eW r s) (rest.map Prod.fst):=
   ub _ _ (fun v hv => faith _ (sub.subset hv))
 have rz:(bM d rest).1 = iD (bM d ws) (bc d a.2) (bc d b.2) ka kb:=
   rh d a b ha hb ne ka kb
 have hf:= lm op (faith _ ha) (faith _ hb)
 change bc d (eW r s z.1) ||| dt d (eW r s) (rest.map Prod.fst) = _ at sep
 change z.2 = eW r s z.1 at hf
 rw [←hf,←g,rz,BitVec.or_comm] at sep
 have be:((iD (bM (!u) ws) (bc (!u) a.2) (bc (!u) b.2) ka kb ||| bc (!u) z.2) != BitVec.allOnes 152) = false:= by
   simpa using sep
 change (if (iD (bM (!u) ws) (bc (!u) a.2) (bc (!u) b.2) ka kb ||| bc (!u) z.2) != BitVec.allOnes 152 then true else if !cS z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
 rw [be,pp,fr] at test
 exact lH (op:=bW op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def hG (ctx:bd) (a b:Decor) (op:Nat):=
 let z:= dbin op a b
 let attempt:= eZ ctx op a b z
 attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u:Bool):List Nat:= if u then [0,1,2,3] else [0,1]
lemma oh {u d} (h:bK u d):d ∈ opsOf u:= by
 rcases cd h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
 · cases u <;> simp [opsOf]
 · cases u <;> simp [opsOf]
 · simp [opsOf]
 · simp [opsOf]
def oT (ctx:bd) (a:Decor) (bs:List Decor):=
   bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (hG ctx a b))
def fv (ctx:bd):List Decor → Bool
 | [] => true
 | a::bs => oT ctx a bs && fv ctx bs
lemma pR {ctx ws} (h:fv ctx ws=true) {a b:Decor} (ha:a∈ws) (hb:b∈ws)
   (ne:a≠b):(∀ d,bK ctx.2.2.2.1.2 d → hG ctx a b d=true) ∨
     (∀ d,bK ctx.2.2.2.1.2 d → hG ctx b a d=true):= by
 induction ws with
 | nil => simp at ha
 | cons w ws ih =>
   simp only [fv,Bool.and_eq_true,oT,List.all_eq_true] at h
   rcases List.mem_cons.mp ha with rfl | haTail
   · have bm:= (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
     exact Or.inl fun d hd => h.1 b bm d (oh hd)
   · rcases List.mem_cons.mp hb with rfl | hbTail
     · exact Or.inr fun d hd => h.1 a haTail d (oh hd)
     · exact ih h.2 haTail hbTail
lemma o7 {ctx a b d} (h:hG ctx a b d = true) (ka kb:Bool):
   eZ ctx d a b (dbin d a b) ka kb = true:= by
 simp only [hG,Bool.and_eq_true] at h
 cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
lemma po {v:List Sig} {w:Sig} (a:Sig) (k:Bool):
   w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v:= by cases k <;> simp [kept]
lemma nl {v:List Decor} (nd:v.Nodup) (a w:Decor) (k:Bool):
   w ∈ fh v a k ↔ w∈v ∧ (w≠a ∨ k=true):= by
 cases k <;> simp [fh,nd.mem_erase_iff,and_comm]
lemma lc {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
   (ha:a∈ws) (hb:b∈ws) (eq:a.1=b.1):a=b:= by
 induction ws with
 | nil => simp at ha
 | cons w ws ih =>
   obtain ⟨hn,ht⟩:= List.nodup_cons.mp nd
   rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
   · rfl
   · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
   · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
   · exact ih ht haTail hbTail
lemma nm {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
   (ha:a ∈ ws) (hb:b ∈ ws) (ka kb:Bool) (v:Sig):
   v ∈ (cB ws a b ka kb).map Prod.fst ↔
   v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true):= by
 have wn:= nd.of_map
 have dn:= wn.sublist (kl ws a ka)
 simp only [cB,List.mem_map,nl wn,nl dn]
 constructor
 · rintro ⟨w,hw,rfl⟩
   exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (lc nd hw.1.1 ha eq)) id,
         hw.2.imp (fun ne eq => ne (lc nd hw.1.1 hb eq)) id⟩
 · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
   exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
       h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
lemma oy {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
   (ha:a∈ws) (hb:b∈ws) (ne:a.1≠b.1) (d:Nat) (ka kb:Bool):
   (lK ws d a b ka kb).toFinset =
     (dd (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:= by
 ext v
 have av:= List.mem_map_of_mem (f:=Prod.fst) ha
 have bv':= List.mem_map_of_mem (f:=Prod.fst) hb
 simp only [lK,dd,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
   nm nd ha hb,po,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
 by_cases va:v=a.1 <;> by_cases vb:v=b.1 <;> cases ka <;> cases kb <;> simp_all
lemma nV {u} (v:List Sig) (nd:v.Nodup) (a b:Sig) (d:Nat) (hd:bK u d) (ka kb:Bool):
   (dd v a b d ka kb).toFinset = (dd v b a (i0 d) kb ka).toFinset:= by
 ext x
 simp only [dd,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
   po,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,mT hd a b]
 tauto
lemma p7 {u raw T r s ws pools links cap}
   (pairs:e8 T r s) (faith: ∀ w ∈ ws,cK r s w)
   (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst)
   (pv: ∀ p ∈ pools,ei u raw T p)
   (lv: ∀ tag xs,xs ∈ links tag → az u T (cap-1) (List.toFinset xs))
   (checks:fv (cap,ws.length,ws,nn u ws,pools,links) ws = true):
   az u T cap (ws.map Prod.fst).toFinset:= by
 by_cases hc:cap=0
 · intro k hk h
   have ke:k=0:= by omega
   subst k
   generalize he:(ws.map Prod.fst).toFinset = S at h
   obtain ⟨hS,_⟩:= h
   exact out (List.mem_toFinset.mp (by rw [he,hS];exact Finset.mem_singleton_self _))
 have hc':0<cap:= by omega
 apply sl nd out
 intro a ha b hb d hd ka kb ne fresh pro len
 obtain ⟨a,haW,rfl⟩:= List.mem_map.mp ha
 obtain ⟨b,hbW,rfl⟩:= List.mem_map.mp hb
 have ab:a≠b:= fun e => ne (congrArg Prod.fst e)
 have one (a b:Decor) (d:Nat) (aa:a∈ws) (bb:b∈ws) (ne':a.1≠b.1) (ka kb:Bool)
     (pr:bu (bin d a.1 b.1)) (fr:bin d a.1 b.1 ∉ ws.map Prod.fst)
     (test:hG (cap,ws.length,ws,nn u ws,pools,links) a b d = true):
     az u T (cap-1) (dd (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:= by
   rw [←oy nd aa bb ne']
   exact mH pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
     pr fr (o7 test ka kb)
 rcases pR checks haW hbW ab with hh | hh
 · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
 · rw [nV _ nd _ _ d hd]
   exact one b a (i0 d) hbW haW (Ne.symm ne) kb ka (mT hd a.1 b.1 ▸ pro)
     (mT hd a.1 b.1 ▸ fresh) (hh _ (rc hd).1)
lemma oB (r s:Row) (h: ∀ a ∈ inputs,bit r a = bit s a):r=s:= by
 apply Fin.ext
 apply Nat.eq_of_testBit_eq
 intro j
 by_cases hj:j<9
 · let i:Fin 9:= ⟨j,hj⟩
   have hm:inputs.getD i.val zero ∈ inputs:= by
     rw [← gt]
     exact List.mem_ofFn.mpr ⟨i,rfl⟩
   exact (iI i r).symm.trans ((h _ hm).trans (iI i s))
 · have le:512 ≤ 2^j:= by
     change 2^9 ≤ 2^j
     exact Nat.pow_le_pow_right (by decide) (by omega)
   exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
     (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def km (p q:List Move):= inputs.all (fun a => bg p (bg q a) == a)
lemma mh {p q} (h:km p q = true) (r:Row):
   cD q (cD p r) = r:= by
 apply oB
 intro a ha
 rw [←il,←il]
 have eq:= beq_iff_eq.mp (List.all_eq_true.mp h a ha)
 rw [eq]
def lU (T:Sig) (p:List Move):=
 (bg p T == T) && km p p.reverse && km p.reverse p
lemma mn {u T n} {ws:List Sig} (hi:az u T n ws.toFinset)
   (p:List Move) (ok:lU T p = true):az u T n (ws.map (bg p.reverse)).toFinset:= by
 simp only [lU,Bool.and_eq_true,beq_iff_eq] at ok
 have onto:Function.Surjective (cD p):= fun r => ⟨cD p.reverse r,mh ok.2 r⟩
 intro k hk h
 have run:= pz h (cD p) onto
 have goal:cF (cD p) T = T:= (cj p T).symm.trans ok.1.1
 have inv (x:Sig):cF (cD p) (bg p.reverse x) = x:= by
   apply BitVec.eq_of_getLsbD_eq
   intro j hj
   change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
   rw [de,il,mh ok.1.2]
 have back:(ws.map (bg p.reverse)).toFinset.image (cF (cD p)) = ws.toFinset:= by
   ext a
   simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
   constructor
   · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
     simpa only [inv] using hw
   · intro ha
     exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
 rw [goal,back] at run
 exact hi k hk run
abbrev aC:= Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def bi:aC:= (0,0,0,0,0,0,0,fun _ => 0)
def bE (word:Nat → Nat) (pos len:Nat):=
 let i:= pos/8192
 let shift:= pos % 8192
 let lo:= word i >>> shift
 if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
 else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def aL (nb slots sw vw iw pw:Nat) (data:Nat → Nat) (h:Nat):Option (Nat × Nat):=
 let a:= h % nb
 let sh:= bE data (a*sw) sw
 let row:= (h/nb+sh) % slots
 let word:= bE data (nb*sw+row*vw) vw
 if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
   some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
 else none
def bY (nb slots sw vw iw pw:Nat) (data:Nat → Nat) (h:Nat):Option (Nat × Nat):=
 let a:= h % nb
 let sh:= bE data (a*sw) sw
 let row:= (h/nb+sh) % slots
 let word:= bE data (nb*sw+row*vw) vw
 if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
   some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
 else none
abbrev aM:= Nat × Nat × (Nat → Bits × Bits) × List aZ × List (List Nat) ×
 (Nat → aC) × (Nat → Nat → Option (Nat × Nat))
def aM.mask (g:aM):Nat:= g.1
def aM.mode (g:aM):Bool:= !(g.1.testBit 10)
def aM.cap (g:aM):Nat:= g.2.1
def aM.samples (g:aM):Nat → Bits × Bits:= g.2.2.1
def aM.cols (g:aM):List aZ:= g.2.2.2.1
def aM.autos (g:aM):List (List Nat):= g.2.2.2.2.1
def aM.levels (g:aM):Nat → aC:= g.2.2.2.2.2.1
def aM.index (g:aM):Nat → Nat → Option (Nat × Nat):= g.2.2.2.2.2.2
def hJ (g:aM):=
 let ws:= lq g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
 ws
lemma mO (g:aM): ∀ a ∈ hJ g,
   cK (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a:= by
 exact oN g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
def bo (g:aM):= ej g.mask
def cU (m:Nat) (v:Nat → Bits):=
 mX m v
lemma rb (m:Nat) (v:Nat → Bits) (i:Fin 152):
   bit (asRow v i) (ej m) = (cU m v).getLsbD i.val:= by
 exact ox m v i
lemma hP {m:Nat} {p q:Nat → Bits}
   (hp:cU m p = BitVec.allOnes 152) (hq:cU m q = 0):
   e8 (ej m) (asRow p) (asRow q):= by
 intro i
 simp only [rb,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
 simp
def cN {α:Type} (bits:Nat):List α → List α
 | [] => []
 | w::ws => if bits &&& 1 == 1 then w::cN (bits >>> 1) ws else cN (bits >>> 1) ws
lemma mV {α:Type} (bits:Nat) (ws:List α):(cN bits ws).Sublist ws:= by
 induction ws generalizing bits with
 | nil => exact List.Sublist.slnil
 | cons a ws ih =>
   unfold cN
   split
   · exact List.Sublist.cons₂ _ (ih _)
   · exact List.Sublist.cons _ (ih _)
def fc (d:Nat):= 10*(d-1)
def jo (d flags:Nat):= flags % 16 + (if d=0 then 0 else 10) + flags/16
def jp (d raw dict:Nat):=
 (dict % 65536)*fc d + (dict/65536)*(raw+d)
def kq (tab:aC) (raw i:Nat):Nat:=
 let (_,d,_,dict,flags,_,marker,word):= tab
 let width:= 10*d+raw+d
 if marker<1024 then bE word (i*width) width else
   let off:= jp d raw dict+i*jo d flags
   let pre:= bE word off (flags % 16)
   let lastBits:= if d=0 then 0 else 10
   let last:= bE word (off+flags % 16) lastBits
   let mask:= bE word (off+flags % 16+lastBits) (flags/16)
   let base:= (dict % 65536)*fc d
   bE word (pre*fc d) (fc d) |||
     (last <<< fc d) ||| (bE word (base+mask*(raw+d)) (raw+d) <<< (10*d))
def mg (_g:aM) (depth:Nat):= depth
def lf (g:aM) (k i:Nat):Nat × List Decor × List Decor:=
 let raw:= hJ g
 let (_,depth,_,_,_,_,_,data):= g.levels k
 let len:= 10*mg g depth
 let width:= len+raw.length+depth
 let recp:= kq (g.levels k) raw.length i
 let stored:= recp &&& ((1 <<< len)-1)
 let ops:= stored
 let bank:= gr depth ops raw
 (ops,bank,cN (recp >>> len) bank)
def of (x pos width:Nat):= (x >>> pos) &&& ((1 <<< width)-1)
def l4 (bank:List Decor) (ops paid:Nat):Nat → List eR
 | 0 => []
 | n+1 =>
   let more:= l4 bank (ops >>> 10) (paid >>> 1) n
   if paid &&& 1 == 0 then more else
     (of ops 8 2,(bank.getD (ops &&& 15) bq).1,
       (bank.getD (of ops 4 4) bq).1)::more
def je (g:aM) (ops d:Nat) (bank:List Decor) (idx paid:Nat):Option bG:=
 (g.cols[idx]?).bind fun ci =>
   iZ g.mode (varsX (hO g.mask ci)) (l4 bank ops paid d) (hQ ci.1 ci.2.1) ci.2.2.2.2
lemma mw (g:aM)
   (cols: ∀ ci ∈ g.cols,Slice g.mode (varsX (hO g.mask ci)) (bo g) (hQ ci.1 ci.2.1) ci.2.2.2.2)
   {i ops depth bank paid c} (h:je g ops depth bank i paid = some c):
   ei g.mode (vars g.mask) (bo g) c:= by
 unfold je at h
 cases e:g.cols[i]? with
 | none => simp [e] at h
 | some ci =>
   simp only [e,Option.bind_some] at h
   apply ly _ h
   exact cols ci (List.mem_of_getElem? e)
def pi (data:Nat → Nat) (w v:Nat):Nat → Nat → List (Nat × Nat)
 | 0,_ => []
 | n+1,pos =>
   let x:= bE data pos (w+v)
   (x &&& ((1 <<< w)-1),x >>> w)::pi data w v n (pos+w+v)
def eS {α:Type}:Nat → (Nat → α) → α
 | 0,next => next 0
 | n+1,next => next (n+1)
def fm (data:Nat → Nat) (dict cw d gapBits:Nat):
   Nat → Nat → Nat → List (Nat × Nat)
 | 0,_,_ => []
 | left+1,st,first =>
   eS st fun pos => eS first fun base =>
   eS (bE data pos 32) fun head =>
   eS (Nat.log2 (head ^^^ (head+1))) fun ones =>
   eS (base+(ones <<< gapBits)+bE data (pos+ones+1) gapBits) fun key =>
   eS (bE data (dict+key*(cw+d)) (cw+d)) fun pair =>
     (pair &&& ((1 <<< cw)-1),pair >>> cw)::
       fm data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)
def oU {α:Type} (a b:Nat) (xs:List α):List α:=
 let rec collect:List α → Nat → List α → List α → List α → List α
   | [],_,first,second,other => first ++ second ++ other.reverse
   | x::tail,i,first,second,other =>
     if i=a then collect tail (i+1) [x] second other
     else if i=b then collect tail (i+1) first [x] other
     else collect tail (i+1) first second (x::other)
 collect xs 0 [] [] []
def ma (tab:aC) (raw i:Nat):List (Nat × Nat):=
 let (num,d,cw,dict,flags,ow,marker,data):= tab
 if marker<1024 then
   let start:= num*(10*d+raw+d)
   let pos:= start+num*ow+bE data (start+i*ow) ow
   pi data cw d (bE data pos 5) (pos+5+marker)
 else
   let off:= jp d raw dict + num*jo d flags
   let pairs:= off+num*ow
   let priority:= decide (4096≤marker)
   let pos:= pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+bE data (off+i*ow) ow
   let n:= bE data pos 5
   let gap:= bE data (pos+5) 3
   if !priority || decide (n≤1) then fm data pairs cw d gap n (pos+8) 0 else
     let width:= (n-1).log2+1
     let a:= bE data (pos+8) width
     let b:= if n=2 then 1-a else bE data (pos+8+width) width
     let extra:= if n=2 then width else 2*width
     let xs:= fm data pairs cw d gap n (pos+8+extra) 0
     oU a b xs
def bT (g:aM) (k i:Nat):= (lf g k i).2.2.map Prod.fst
def eI (g:aM) (k:Nat) (pair:Nat × Nat):Option (List Sig):=
 if pair.1 ≥ (g.levels k).1 then none else
   (g.autos[pair.2]?).map fun perm => (bT g k pair.1).map (bg (perm.map cY).reverse)
lemma mt (g:aM) (k:Nat)
   (names: ∀ x ∈ g.autos,lU (bo g) (x.map cY) = true)
   (earlier: ∀ i < (g.levels k).1,az g.mode (bo g) k (bT g k i).toFinset)
   {pair out} (h:eI g k pair = some out):
   az g.mode (bo g) k out.toFinset:= by
 unfold eI at h
 split at h
 · contradiction
 next valid =>
   cases e:g.autos[pair.2]? with
   | none => simp [e] at h
   | some perm =>
     simp only [e,Option.map_some,Option.some.injEq] at h
     subst out
     exact mn (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def cL (g:aM) (k i:Nat):=
 let raw:= hJ g
 let (num,depth,cw,iw,pw,offw,lw,data):= g.levels k
 let (ops,bank,ws):= lf g k i
 let values:= ws.map Prod.fst
 let rules:= (ma (g.levels k) raw.length i).filterMap (fun (a,b) => je g ops depth bank a b)
 let ls:= fun tag => ((g.index k tag).bind (eI g (k-1))).toList
 decide values.Nodup && !(values.contains (bo g)) &&
   (if k=0 then true else fv (k,ws.length,ws,nn g.mode ws,rules,ls) ws)
lemma cW (g:aM) (k i:Nat)
   (samples:e8 (bo g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
   (cols: ∀ ci ∈ g.cols,Slice g.mode (varsX (hO g.mask ci)) (bo g) (hQ ci.1 ci.2.1) ci.2.2.2.2)
   (names: ∀ x ∈ g.autos,lU (bo g) (x.map cY) = true)
   (prior:k>0 → ∀ j < (g.levels (k-1)).1,az g.mode (bo g) (k-1) (bT g (k-1) j).toFinset)
   (checked:cL g k i = true):az g.mode (bo g) k (bT g k i).toFinset:= by
 simp only [cL,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
 have hN:= checked.1.1
 have hT:bo g ∉ bT g k i:= by simpa [bT] using checked.1.2
 by_cases h0:k=0
 · subst k
   intro t lo h
   have ht:t=0:= by omega
   subst t
   generalize he:(bT g 0 i).toFinset = S at h
   obtain ⟨hS,_⟩:= h
   exact hT (List.mem_toFinset.mp (by rw [he,hS];exact Finset.mem_singleton_self _))
 apply p7 (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
 · intro v hv
   apply mx _ _ _ _ _ (mO g) v
   exact (mV _ _).subset hv
 · intro p hp
   obtain ⟨⟨a,b⟩,_,h⟩:= List.mem_filterMap.mp hp
   exact mw g cols h
 · intro tag xs hx
   have e:((g.index k tag).bind (eI g (k-1)))=some xs:= by simpa using hx
   obtain ⟨pair,_,h⟩:= Option.bind_eq_some_iff.mp e
   exact mt g _ names (prior (by omega)) h
def block (g:aM) (k start:Nat):Nat → Bool
 | 0 => true
 | n+1 => cL g k (start+n) && block g k start n
lemma mZ {g k start n} (h:block g k start n=true) (j:Nat) (lo:start≤j) (hi:j<start+n):
   cL g k j=true:= by
 induction n with
 | zero => omega
 | succ n ih =>
   simp only [block,Bool.and_eq_true] at h
   by_cases eq:j=start+n
   · simpa [eq] using h.1
   · exact ih h.2 (by omega)
lemma aT {g k start a b} (h:block g k start a=true)
   (h':block g k (start+a) b=true):block g k start (a+b)=true:= by
 induction b with
 | zero => simpa using h
 | succ b ih =>
   simp only [block,Bool.and_eq_true] at h'
   simp only [Nat.add_succ,block,Bool.and_eq_true]
   exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def bP (g:aM) (top:Nat):=
 ∀ k ≤ top,block g k 0 (g.levels k).1 = true
def aV (g:aM) (prior:Nat → Nat):=
 (cU g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
 (cU g.mask (fun j => (g.samples j).2) == 0) &&
 g.cols.all (fun c => gm g.mask c prior) &&
 g.autos.all (fun p => lU (bo g) (p.map cY))
lemma p1 (g:aM) (top:Nat) (prior:Nat → Nat)
   (lower: ∀ q,Lower g.mode (varsX q) (au q) (prior q))
   (geometry:aV g prior = true) (rows:bP g top):
   ∀ k ≤ top,∀ i < (g.levels k).1,az g.mode (bo g) k (bT g k i).toFinset:= by
 simp only [aV,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
 intro k
 induction k with
 | zero =>
   intro hk i hi
   apply cW g 0 i (hP geometry.1.1.1 geometry.1.1.2)
     (fun x hx => ig _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
   exact mZ (rows 0 hk) i (by omega) (by omega)
 | succ k ih =>
   intro hk i hi
   apply cW g _ i (hP geometry.1.1.1 geometry.1.1.2)
     (fun x hx => ig _ prior lower (geometry.1.2 x hx)) geometry.2
     (fun _ => by simpa using ih (by omega))
   exact mZ (rows _ hk) i (by omega) (by omega)
def eh (g:aM) (k i:Nat) (ws:List Sig):=
 decide (i < (g.levels k).1) && gh (bT g k i) ws
lemma nj {g top prior k i ws} (low: ∀ q,Lower g.mode (varsX q) (au q) (prior q))
   (geom:aV g prior = true) (blocks:bP g top) (le:k ≤ top)
   (idx:eh g k i ws = true):az g.mode (bo g) k ws.toFinset:= by
 simp only [eh,Bool.and_eq_true,decide_eq_true_eq] at idx
 rw [←fj idx.2]
 exact p1 g top prior low geom blocks _ le i idx.1
def Known (u:Bool) (entries:List (Nat × Nat)):= ∀ e ∈ entries,Lower u (varsX e.1) (au e.1) e.2
def l8 (old:List (Nat × Nat)) (L:Nat) (carries:List (Nat × List Nat)):=
 carries.map (fun v => (v.1,L)) ++ old
lemma aw {u old L m carries} (previous:Known u old)
   (main:Lower u (varsX m) (au m) L)
   (ok:carries.all (fun v => mB v.1 m v.2) = true):
   Known u (l8 old L carries):= by
 intro e he
 rcases List.mem_append.mp he with hx | h
 · obtain ⟨v,hv,rfl⟩:= List.mem_map.mp hx
   exact pe (List.all_eq_true.mp ok _ hv) main
 · exact previous e h
lemma oo:Known true []:= by simp [Known]
lemma pX {u es} (h:Known true es):Known u es:= fun e he => pZ (h e he)
def bV (v:Nat) (upper:Nat):= 2^153*upper+v
def aN {α:Type} (f:α → Bits):List α → Nat
 | [] => 0
 | x::xs => bV (f x).toNat (aN f xs)
def units:Nat → Nat
 | 0 => 0
 | n+1 => bV 1 (units n)
lemma lF (x:Bits):x.toNat < 2^153:=
 lt_trans x.isLt (by decide +kernel)
lemma sk (a b:Bits) (u v:Nat):
   bV a.toNat u &&& bV b.toNat v = bV (a &&& b).toNat (u &&& v):= by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [bV,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (lF _)]
 by_cases h:i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
lemma tr (a b:Bits) (u v:Nat):
   bV a.toNat u ||| bV b.toNat v = bV (a ||| b).toNat (u ||| v):= by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [bV,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (lF _)]
 by_cases h:i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
lemma rv (a b:Bits) (u v:Nat):
   bV a.toNat u ^^^ bV b.toNat v = bV (a ^^^ b).toNat (u ^^^ v):= by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [bV,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (lF _)]
 by_cases h:i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
lemma ip {α} (f g:α → Bits) (xs):
   aN f xs &&& aN g xs = aN (fun x => f x &&& g x) xs:= by
 induction xs with
 | nil => simp [aN]
 | cons a xs ih => simp only [aN,sk,ih]
lemma mK {α} (f g:α → Bits) (xs):
   aN f xs ||| aN g xs = aN (fun x => f x ||| g x) xs:= by
 induction xs with
 | nil => simp [aN]
 | cons a xs ih => simp only [aN,tr,ih]
lemma i9 {α} (f g:α → Bits) (xs):
   aN f xs ^^^ aN g xs = aN (fun x => f x ^^^ g x) xs:= by
 induction xs with
 | nil => simp [aN]
 | cons a xs ih => simp only [aN,rv,ih]
def jg (r packed:Nat):= ((packed+r) >>> 152) &&& r
lemma ua (n i:Nat) (hi:i<n):(units n).testBit (153*i) = true:= by
 induction n generalizing i with
 | zero => omega
 | succ n ih =>
   rw [units,bV,Nat.testBit_two_pow_mul_add _ (by decide +kernel:1 < 2^153)]
   cases i with
   | zero => simp
   | succ i =>
     have di:153*(i+1)-153=153*i:= by omega
     have ge: ¬153*(i+1)<153:= by omega
     simp only [ge,ite_false,di]
     exact ih _ (by omega)
set_option maxRecDepth 8192 in
lemma tq (a:Bits):(a.toNat+1).testBit 152 = (a==BitVec.allOnes 152):= by
 by_cases h:a=BitVec.allOnes 152
 · subst a
   decide +kernel
 · have lim:= a.isLt
   have ne:a.toNat ≠ 2^152-1:= by
     intro eq
     apply h
     apply BitVec.eq_of_toNat_eq
     simpa only [BitVec.toNat_allOnes] using eq
   have lt:a.toNat+1<2^152:= by omega
   rw [Nat.testBit_eq_false_of_lt lt]
   exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
lemma ur {α} (f:α → Bits) (xs:List α) (i:Nat) (hi:i<xs.length):
   (jg (units xs.length) (aN f xs)).testBit (153*i) =
     (f xs[i]==BitVec.allOnes 152):= by
 simp only [jg,Nat.testBit_and,Nat.testBit_shiftRight,ua _ _ hi,Bool.and_true]
 induction xs generalizing i with
 | nil => simp at hi
 | cons a xs ih =>
   simp only [aN,List.length_cons,units,bV]
   have sum (u v x:Nat):2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1):= by omega
   rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have:= (f a).isLt;omega)]
   have hi':i < xs.length+1:= hi
   cases i with
   | zero => simpa using tq (f a)
   | succ i =>
     have ge: ¬153*(i+1)+152<153:= by omega
     have di:153*(i+1)+152-153=153*i+152:= by omega
     simp only [ge,ite_false,di,List.getElem_cons_succ]
     apply ih i (by omega)
abbrev ii:= Nat × Nat
abbrev lS:= Nat × Nat × Nat
def cP {α} (s:α → mz) (xs:List α):ii:=
 (aN (fun x => (s x).1) xs,aN (fun x => (s x).2) xs)
def jc {α} (c:α → Cov) (xs:List α):lS:=
 (aN (fun x => (c x).1) xs,aN (fun x => (c x).2.1) xs,
  aN (fun x => (c x).2.2) xs)
def cM (d:Bool) (a:ii):=
 if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
lemma la (a b:Bits):a ^^^ (a &&& b) = a &&& ~~~b:= by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
lemma h6 {α} (s:α → mz) (xs:List α) (d:Bool):
   cM d (cP s xs) = aN (fun x => bc d (s x)) xs:= by
 cases d <;> simp only [cM,cP,bc,Bool.false_eq_true,ite_false,ite_true,ip,i9,la]
def hH (op:Nat) (a b:ii):ii:=
 if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
 else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
 else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
lemma rt {α} (a b:α → Decor) (xs:List α) (op:Nat):
   hH op (cP (fun x => (a x).2) xs) (cP (fun x => (b x).2) xs) =
   cP (fun x => (dbin op (a x) (b x)).2) xs:= by
 by_cases h0:op=0
 · simp only [hH,h0,ite_true,cP,ip,dbin,bv]
 by_cases h1:op=1
 · simp [hH,h1,cP,mK,dbin,bv]
 by_cases h2:op=2
 · simp [hH,h2,cP,ip,i9,la,dbin,bv]
 · have e (x y:Bits): ~~~x &&& y = y &&& ~~~x:= BitVec.and_comm _ _
   simp only [hH,h0,h1,h2,ite_false,cP,ip,i9,la,dbin,bv,e]
def iz (c:lS) (a b:Nat) (ka kb:Bool):=
 let without1:= fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
 let without2:= c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
 if ka then (if kb then c.1 else without1 b)
 else if kb then without1 a else without2
lemma nz {α} (c:α → Cov) (a b:α → Bits) (xs:List α) (ka kb:Bool):
   iz (jc c xs) (aN a xs) (aN b xs) ka kb =
   aN (fun x => iD (c x) (a x) (b x) ka kb) xs:= by
 cases ka <;> cases kb <;>
   simp only [iz,jc,ip,mK,i9,la,iD,gf,i7,
     Bool.false_eq_true,ite_false,ite_true]
def ay (c:bd) (i:Nat):= c.2.2.1.getD i bq
def iv (c:bd) (i j op:Nat) (ka kb:Bool):=
 let a:= ay c i
 let b:= ay c j
 eZ c op a b (dbin op a b) ka kb
def lO (c:bd) (d ka kb:Bool) (op i j:Nat):=
 let a:= ay c i
 let b:= ay c j
 iD c.2.2.2.1.1 (bc d a.2) (bc d b.2) ka kb |||
   bc d (dbin op a b).2
def ks {α:Type} (f:α → Bool) (mask:Nat):List α → Bool
 | [] => true
 | x::xs => if mask=0 then true else
   ((mask &&& 1 == 0) || f x) && ks f (mask >>> 153) xs
lemma se {α} (f:α → Bool) (mask:Nat) (xs:List α) (i:Nat) (hi:i<xs.length)
   (bitOn:mask.testBit (153*i)=true) (ok:ks f mask xs=true):f xs[i]=true:= by
 induction xs generalizing mask i with
 | nil => simp at hi
 | cons x xs ih =>
   have ne:mask≠0:= by intro e;simp [e] at bitOn
   simp only [ks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
   cases i with
   | zero =>
     have nonzero:mask &&& 1 ≠ 0:= by
       intro he
       have at0:= congrArg (fun n:Nat => n.testBit 0) he
       simp only [Nat.testBit_and] at at0
       change mask.testBit 0=true at bitOn
       simp [bitOn] at at0
     exact ok.1.resolve_left nonzero
   | succ i =>
     apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
     simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch:= Nat × Nat × Nat × List ii × lS
def db (k n:Nat) (xs:List bd):Batch:=
 (k,n,units xs.length,(List.range n).map (fun i => cP (fun c => (ay c i).2) xs),
   jc (fun c => c.2.2.2.1.1) xs)
def ie (b:Batch) (i:Nat):= b.2.2.2.1.getD i (0,0)
lemma mb (k n) (xs) {i:Nat} (h:i<n):
   ie (db k n xs) i = cP (fun c => (ay c i).2) xs:= by
 simp [ie,db,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
lemma o5 (d x:Sig):bZ d (neg x) = d ^^^ bZ d x:= by
 apply du
 intro r
 simp only [bZ,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
 cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def bx (p:Decor → Bool) (a:Decor) (keep:Bool):=
 if keep then 0 else (p a).toNat
lemma oc (p:Decor → Bool) (ws:List Decor) (a:Decor) (keep:Bool):
   ws.countP p ≤ (fh ws a keep).countP p + bx p a keep:= by
 cases keep
 · simp only [fh,Bool.false_eq_true,ite_false,bx,List.countP_erase]
   split
   next h => simp [h.2];omega
   next => omega
 · simp [fh,bx]
lemma rk (p:Decor → Bool) (ws:List Decor) (a b:Decor) (ka kb:Bool):
   ws.countP p - bx p a ka - bx p b kb ≤
   (cB ws a b ka kb).countP p:= by
 have h1:= oc p ws a ka
 have h2:= oc p (fh ws a ka) b kb
 simp only [cB]
 omega
noncomputable def force {β:Type} (n:Nat) (f:Nat → β):β:= Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
lemma eA {β:Type} (n:Nat) (f:Nat → β):force n f = f n:= by cases n <;> rfl
noncomputable def forceMap {α β:Type} (f:α → Nat) (l:List α):(List Nat → β) → β:=
 List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
lemma iR {α β:Type} (f:α → Nat) (l:List α) (k:List Nat → β):forceMap f l k = k (l.map f):= by
 induction l generalizing k with
 | nil => rfl
 | cons a l ih =>
   change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
   rw [eA,ih]
   rfl
def nmask (d:Nat) (a:Sig):Nat:= Nat.land a.toNat d
noncomputable def anyEq (m:Nat) (l:List Nat):Bool:= List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def iX (d m:Nat):Bool:= or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u:Bool) (d:Nat) (pm:List Nat) (m:Nat):Bool:=
 or (or (iX d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
lemma i3 (d a:Sig):nmask d.toNat a = (bZ d a).toNat:= (BitVec.toNat_and _ _).symm
lemma l3 (a b:Sig):Nat.beq a.toNat b.toNat = (a==b):= by
 rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
 exact BitVec.toNat_inj
lemma jd (d a:Sig):iX d.toNat (nmask d.toNat a) = aE d a:= by
 rw [i3]
 have e:Nat.beq (bZ d a).toNat 0 = (bZ d a == zero):= by
   have z0:zero.toNat=0:= by simp [zero]
   rw [←l3,z0]
 rw [iX,e,l3]
 rfl
lemma o2 (x d:Sig) (pool:List Sig):anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (bZ d)).any (fun v => v==x):= by
 induction pool with
 | nil => rfl
 | cons a l ih =>
   change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
   rw [ih,i3,l3,List.map_cons,List.any_cons,Bool.beq_comm]
lemma i8 (u:Bool) (d a:Sig) (pool:List Sig):
   navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = aY u d pool a:= by
 have x:Nat.xor d.toNat (bZ d a).toNat = (bZ d (neg a)).toNat:= by
   rw [o5]
   exact (BitVec.toNat_xor _ _).symm
 rw [navail,jd,i3,x,o2,o2]
 simp only [aY,aE]
def unav (u:Bool) (p:bG) (w:Decor):Nat:= cond (aY u p.domain p.wires w.1) 0 1
def kr (u:Bool) (p:bG) (ws:List Decor) (k:Nat) (a b:Decor) (op:Nat) (ka kb:Bool):Bool:=
 let const:= fun w:Decor => aE p.domain w.1
 let z:= bin op a.1 b.1
 let cm:= ws.countP const - bx const a ka - bx const b kb + (aE p.domain z).toNat
 (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
   decide (k+p.paid+(!aY u p.domain p.wires z).toNat < p.bound+cm)) &&
   (aY u p.domain p.wires z || (aY u p.domain p.wires a.1 && aY u p.domain p.wires b.1))
def zN (op x y:Nat):Nat:= cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
 (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
lemma zN_eq (op:Nat) (d a b:Sig):zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b):= by
 have tn (x y:Sig):Nat.land x.toNat y.toNat = (x &&& y).toNat:= (BitVec.toNat_and x y).symm
 have tx (x y:Sig):Nat.xor x.toNat y.toNat = (x ^^^ y).toNat:= (BitVec.toNat_xor x y).symm
 have tor (x y:Sig):Nat.lor x.toNat y.toNat = (x ||| y).toNat:= (BitVec.toNat_or x y).symm
 simp only [i3]
 unfold zN
 by_cases h0:op=0
 · subst h0
   change Nat.land _ _ = _
   rw [tn]
   congr 1
   apply du
   intro r
   simp only [bZ,bin,bit,ite_true,BitVec.getLsbD_and]
   cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
 by_cases h1:op=1
 · subst h1
   change Nat.lor _ _ = _
   rw [tor]
   congr 1
   apply du
   intro r
   simp only [bZ,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
   cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
 have e0:Nat.beq op 0=false:= Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
 have e1:Nat.beq op 1=false:= Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
 by_cases h2:op=2
 · subst h2
   change Nat.xor _ (Nat.land _ _) = _
   rw [tn,tx]
   congr 1
   apply du
   intro r
   simp only [bZ,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
   cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
 have e2:Nat.beq op 2=false:= Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
 rw [e0,e1,e2]
 change Nat.xor _ (Nat.land _ _) = _
 rw [tn,tx]
 congr 1
 apply du
 intro r
 simp only [bZ,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
 cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x:Nat) (keep:Bool):Nat:= cond keep 0 (cond (iX d x) 1 0)
lemma o9 (d:Sig) (a:Decor) (keep:Bool):
   nloss d.toNat (nmask d.toNat a.1) keep = bx (fun w:Decor => aE d w.1) a keep:= by
 rw [nloss,jd,bx]
 cases keep
 · cases aE d a.1 <;> rfl
 · rfl
abbrev QS:= Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u:Bool) (k:Nat) (ws:List Decor) (p:bG):QS:=
 let d:= p.domain.toNat
 let ms:= ws.map (fun w:Decor => nmask d w.1)
 (d,ms.countP (iX d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β:Type} (b:Bool) (f:Bool → β):β:= Bool.rec (f false) (f true) b
noncomputable def forcePool {β:Type} (u:Bool) (k:Nat) (ws:List Decor) (p:bG) (f:QS → β):β:=
 force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w:Decor => nmask d w.1) ws fun ms =>
 force (ms.countP (iX d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
 force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
lemma oM {β:Type} (u k ws p) (f:QS → β):forcePool u k ws p f = f (quickSpec u k ws p):= by
 have e (b:Bool) (f:Bool → β):forceBool b f = f b:= by cases b <;> rfl
 simp only [forcePool,eA,iR,e]
 rfl
noncomputable def forcePools {β:Type} (u:Bool) (k:Nat) (ws:List Decor) (ps:List bG):(List QS → β) → β:=
 List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
lemma nM {β:Type} (u k ws ps) (f:List QS → β):forcePools u k ws ps f = f (ps.map (quickSpec u k ws)):= by
 induction ps generalizing f with
 | nil => rfl
 | cons p ps ih =>
   change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
   rw [oM,ih]
   rfl
def kwN (v:Nat):Nat:=
 let n:= v % 2305843009213693951
 (n*(n+971)) % 2305843009213693951
abbrev Lane:= bd × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c:bd):Lane:=
 let ws:= c.2.2.1.map (fun w:Decor => w.1.toNat)
 (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β:Type} (cs:List bd):(List Lane → β) → β:=
 List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
   forceMap (fun w:Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
   forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
lemma jl {β:Type} (cs) (f:List Lane → β):forceLanes cs f = f (cs.map laneOf):= by
 induction cs generalizing f with
 | nil => rfl
 | cons c cs ih =>
   change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
     forceMap (fun w:Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
     forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
   rw [eA,eA,iR,eA,nM,ih]
   rfl
noncomputable def fastCost (s:QS) (i j op:Nat) (ka kb:Bool):Bool:=
 force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
 let av:= navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
 let hi:= Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
 let lo:= s.2.2.2.1
 and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
 (cond (Nat.ble (Nat.succ lo) hi)
   (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
   (cond (Nat.ble lo hi) (iX s.1 (zN op x y)) false))
lemma td {d:Nat} (ws:List Decor) (i:Nat) (hd:nmask d zero=0):
   (ws.map (fun w:Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i bq).1:= by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
 cases ws[i]? with
 | none => exact hd.symm
 | some v => rfl
lemma rp {u k p ws i j op ka kb} (h:fastCost (quickSpec u k ws p) i j op ka kb=true):
   kr u p ws k (ws.getD i bq) (ws.getD j bq) op ka kb=true:= by
 have z0:nmask p.domain.toNat zero=0:= by
   have:zero.toNat=0:= by simp [zero]
   simp [nmask,this]
 have su:(((ws.map (fun w:Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
     (ws.map (unav u p)).sum:= by
   rw [List.map_map]
   refine congrArg List.sum (List.map_congr_left ?_)
   intro w _
   change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
   rw [i8]
   rfl
 simp only [fastCost,quickSpec,eA,td _ _ z0,su,List.countP_map,Function.comp_def,jd] at h
 generalize ws.getD i bq=a at h ⊢
 generalize ws.getD j bq=b at h ⊢
 replace h:and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
  (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:Decor => aE p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
   (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:Decor => aE p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
   (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:Decor => aE p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (iX p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true:= h
 rw [zN_eq,jd,i8,i8,i8,o9,o9] at h
 have ca:aE p.domain (bin op a.1 b.1)=true → aY u p.domain p.wires (bin op a.1 b.1)=true:= by
   intro zc
   simp only [aY,aE,Bool.or_eq_true] at zc ⊢
   exact Or.inl (Or.inl zc)
 simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
 obtain ⟨hu,h⟩:= h
 simp only [kr,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
 refine ⟨⟨hu,?_⟩,?_⟩
 all_goals
   generalize ws.countP (fun w => aE p.domain w.1) - bx (fun w:Decor => aE p.domain w.1) a ka -
     bx (fun w:Decor => aE p.domain w.1) b kb = c at h ⊢
   generalize aE p.domain (bin op a.1 b.1)=r at h ca ⊢
   generalize aY u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
   cases h1:Nat.ble (k+p.paid+1) (p.bound+c)
   · rw [h1] at h
     cases h2:Nat.ble (k+p.paid) (p.bound+c)
     · simp [h2] at h
     · have:= Nat.ble_eq.mp h2
       simp only [h2,cond_true,cond_false] at h
       subst h
       rw [ca rfl]
       simp <;> omega
   · rw [h1] at h
     have l1:= Nat.ble_eq.mp h1
     simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
     rcases h with rfl | ⟨l2,ha,hb⟩
     · simp <;> omega
     · first
       | (have:(!q).toNat ≤ 1:= Bool.toNat_le _
          omega)
       | simp [ha,hb]
lemma sn (m:Nat) (l:List Nat):anyEq m l=true ↔ m ∈ l:= by
 induction l with
 | nil => simp [anyEq]
 | cons a l ih =>
   change or (Nat.beq m a) (anyEq m l)=true ↔ _
   rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl:Nat → Option (List Nat)) (l:Lane) (i j op:Nat) (ka kb:Bool):Bool:=
 force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
 Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
   and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
     (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
   (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
lemma p2 (xs:List Sig):m9 xs = (xs.map eo).sum:= by
 have go (a:Nat):xs.foldl (fun v x => v+eo x) a = a+(xs.map eo).sum:= by
   induction xs generalizing a with
   | nil => rfl
   | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
 exact (go 0).trans (Nat.zero_add _)
lemma mQ (f:Decor → Nat) {ws:List Decor} {a b:Decor} (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b) (ka kb:Bool):
   ((cB ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)):= by
 have er {l:List Decor} {x:Decor} (hx:x ∈ l):(l.map f).sum = f x + ((l.erase x).map f).sum:= by
   have:= ((List.perm_cons_erase hx).map f).sum_eq
   rwa [List.map_cons,List.sum_cons] at this
 have hm:b ∈ ws.erase a:= (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
 have e1:= er ha
 have e2:= er hb
 have e3:= er hm
 cases ka <;> cases kb <;> simp only [cB,fh,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
lemma nN {u p k ws a b op ka kb} (ha:a∈ws) (hb:b∈ws) (ne:a≠b) (al:is u op=true)
   (h:kr u p ws k a b op ka kb=true):
   cp u p k ((cB ws a b ka kb).map Prod.fst) (bW op a b)=true:= by
 let const:= fun w:Decor => aE p.domain w.1
 let z:= bin op a.1 b.1
 let rest:= cB ws a b ka kb
 have ck:= rk const ws a b ka kb
 change ws.countP const - bx const a ka - bx const b kb ≤ rest.countP const at ck
 simp only [kr,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
 obtain ⟨⟨hu,hc⟩,hz⟩:= h
 have sum:= mQ (unav u p) ha hb ne ka kb
 rw [hu] at sum
 have zs:((cB ws a b ka kb).map (unav u p)).sum=0:= by omega
 have hs:(rest.map Prod.fst).all (aY u p.domain p.wires)=true:= by
   apply List.all_eq_true.mpr
   intro _ hm
   obtain ⟨w,hw,rfl⟩:= List.mem_map.mp hm
   have v:= List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
   cases e:aY u p.domain p.wires w.1
   · simp [unav,e] at v
   · rfl
 have opOK:(!(!aY u p.domain p.wires z) || gn u p.domain p.wires (bW op a b))=true:= by
   simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
   rcases hz with hz | ⟨x,y⟩
   · simp [z,hz]
   · simp [gn,bW,x,y,al]
 change k+p.paid+(!aY u p.domain p.wires z).toNat < p.bound+(ws.countP const - bx const a ka -
       bx const b kb+(aE p.domain z).toNat) at hc
 dsimp only [rest] at hs
 have ez:bw (bW op a b)=z:= rfl
 simp only [cp,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
     List.countP_map,Function.comp_def]
 change k+p.paid+(!aY u p.domain p.wires z).toNat <
     p.bound+(rest.countP const + if aE p.domain z then 1 else 0)
 cases hc':aE p.domain z <;> simp [hc'] at hc ⊢ <;> omega
lemma qy (op:Nat) (a b:Sig):zN op a.toNat b.toNat = (bin op a b).toNat:= by
 have e (v:Sig):nmask one.toNat v = v.toNat:= by
   rw [i3]
   congr 1
   exact BitVec.and_allOnes
 have:= zN_eq op one a b
 rwa [e,e,e] at this
lemma getW (ws:List Decor) (i:Nat):
   (ws.map (fun w:Decor => w.1.toNat)).getD i 0 = (ws.getD i bq).1.toNat:= by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
 cases ws[i]? with
 | none =>
   have z0:zero.toNat=0:= by simp [zero]
   exact z0.symm
 | some v => rfl
lemma qx {c:bd} {i j} (nd:(c.2.2.1.map Prod.fst).Nodup)
   (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length) (hij:i≠j):(ay c i).1 ≠ (ay c j).1:= by
 have gi:ay c i = c.2.2.1[i]:= by simp [ay,List.getD_eq_getElem?_getD,hi]
 have gj:ay c j = c.2.2.1[j]:= by simp [ay,List.getD_eq_getElem?_getD,hj]
 rw [gi,gj]
 intro e
 apply hij
 apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
 simpa using e
lemma qc {c:bd} {fl i j op ka kb} (nd:(c.2.2.1.map Prod.fst).Nodup)
   (hfl: ∀ tag ys,fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat)
   (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length) (hij:i≠j) (h:linkAt fl (laneOf c) i j op ka kb=true):
   (c.2.2.2.2.2 (m9 (bw (bW op (ay c i) (ay c j))::
     (cB c.2.2.1 (ay c i) (ay c j) ka kb).map Prod.fst))).any (gh
     (bw (bW op (ay c i) (ay c j))::
     (cB c.2.2.1 (ay c i) (ay c j) ka kb).map Prod.fst))=true:= by
 have mem (t) (ht:t<c.2.2.1.length):ay c t ∈ c.2.2.1:= by
   simp [ay,List.getD_eq_getElem?_getD,ht]
 have hne:= qx nd hi hj hij
 have ha:= mem i hi
 have hb:= mem j hj
 have hab:ay c i ≠ ay c j:= fun e => hne (congrArg Prod.fst e)
 have kv (v:Sig):= nm nd ha hb ka kb v
 have sum:= mQ (fun w:Decor => eo w.1) ha hb hab ka kb
 have wi:ay c i = c.2.2.1.getD i bq:= rfl
 have wj:ay c j = c.2.2.1.getD j bq:= rfl
 simp only [linkAt,laneOf,eA,getW,←wi,←wj,qy] at h
 generalize ay c i=a at *
 generalize ay c j=b at *
 change Option.rec false _ (fl (eo (bin op a.1 b.1)+(((c.2.2.1.map (fun w:Decor => w.1.toNat)).map kwN).sum -
   (cond ka 0 (eo a.1)) - (cond kb 0 (eo b.1)))))=true at h
 have tot:((c.2.2.1.map (fun w:Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w:Decor => eo w.1)).sum:= by
   rw [List.map_map]
   rfl
 rw [tot,←sum] at h
 have tag:m9 (bw (bW op a b)::(cB c.2.2.1 a b ka kb).map Prod.fst) =
     eo (bin op a.1 b.1)+((cB c.2.2.1 a b ka kb).map (fun w:Decor => eo w.1)).sum:= by
   rw [p2,List.map_cons,List.sum_cons,List.map_map]
   rfl
 rw [←tag] at h
 generalize m9 (bw (bW op a b)::(cB c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
 cases hf:fl t with
 | none => simp [hf] at h
 | some ys =>
   obtain ⟨xs,hx,rfl⟩:= hfl t ys hf
   rw [hf] at h
   simp only [iR,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,sn,Nat.beq_eq,Bool.not_eq_true'] at h
   obtain ⟨h1,h2,h3⟩:= h
   have back {v:Sig} (hv:v.toNat ∈ xs.map BitVec.toNat):v ∈ xs:= by
     obtain ⟨w,hw,e⟩:= List.mem_map.mp hv
     exact BitVec.toNat_inj.mp e ▸ hw
   apply List.any_eq_true.mpr
   refine ⟨xs,hx,?_⟩
   simp only [gh,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
   constructor
   · intro v hv
     rcases List.mem_cons.mp hv with rfl | hv
     · exact back h1
     · obtain ⟨hw,va,vb⟩:= (kv v).mp hv
       obtain ⟨w,hm,rfl⟩:= List.mem_map.mp hw
       rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
       · rcases va with va | va
         · exact absurd (BitVec.toNat_inj.mp y) va
         · simp [va] at x
       · rcases vb with vb | vb
         · exact absurd (BitVec.toNat_inj.mp y) vb
         · simp [vb] at x
       · exact back x
   · intro v hv
     rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
     · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
     · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
       · obtain ⟨w,hw,e⟩:= List.mem_map.mp m
         exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
       · rcases x with x | x
         · exact Or.inr x
         · refine Or.inl fun e => ?_
           subst e
           simp at x
       · rcases y with x | x
         · exact Or.inr x
         · refine Or.inl fun e => ?_
           subst e
           simp at x
noncomputable def fallbackAt (fl:Nat → Option (List Nat)) (l:Lane) (i j op:Nat) (ka kb:Bool):Bool:=
 or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
   (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (iv l.1 i j op ka kb)
lemma m7 {c:bd} {fl i j op ka kb} (nd:(c.2.2.1.map Prod.fst).Nodup)
   (hfl: ∀ tag ys,fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat)
   (h:fallbackAt fl (laneOf c) i j op ka kb=true):
   iv c i j op ka kb=true:= by
 simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
 rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
 · have hi:= Nat.ble_eq.mp hi
   have hj:= Nat.ble_eq.mp hj
   have ho:= Nat.ble_eq.mp ho
   change Nat.succ i ≤ c.2.2.1.length at hi
   change Nat.succ j ≤ c.2.2.1.length at hj
   change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
   have al:is c.2.2.2.1.2 op=true:= by
     cases hu:c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [is] <;> omega
   have mem (t) (ht:t<c.2.2.1.length):ay c t ∈ c.2.2.1:= by
     simp [ay,List.getD_eq_getElem?_getD,ht]
   obtain ⟨_,hm,ok⟩:= List.any_eq_true.mp h
   obtain ⟨p,hp,rfl⟩:= List.mem_map.mp hm
   have hne:= qx nd hi hj (fun e => by simp [e] at hn)
   have closed:= nN (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (rp ok)
   have cut:c.2.2.2.2.1.any (fun p => cp c.2.2.2.1.2 p (c.1-1)
       ((cB c.2.2.1 (ay c i) (ay c j) ka kb).map Prod.fst)
       (bW op (ay c i) (ay c j)))=true:=
     List.any_eq_true.mpr ⟨p,hp,closed⟩
   simp only [iv,eZ,eP,cut,Bool.or_true]
   repeat' split
   all_goals rfl
 · have cut:= qc nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
   simp only [iv,eZ,eP,cut,Bool.true_or]
   repeat' split
   all_goals rfl
 · exact h
def ld (v t:Nat):Nat:= cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def eM (v:Nat):Bool:= and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
lemma qg: ∀ v:Fin 144,eM v.val=true → ∀ t:Fin 9,ld v.val t.val<9 ∧
   iQ (cY v.val) (inputs.getD t.val zero) = inputs.getD (ld v.val t.val) zero:= by decide +kernel
lemma qh {v t:Nat} (hv:eM v=true) (ht:t<9):ld v t<9 ∧
   iQ (cY v) (inputs.getD t zero) = inputs.getD (ld v t) zero:= by
 have lt:v<144:= by
   simp only [eM,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
   omega
 exact qg ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm:List Nat) (t:Nat):Nat:= perm.foldl (fun t v => ld v t) t
lemma tv {perm:List Nat} (ok:perm.all eM=true) {t:Nat} (ht:t<9):
   bg (perm.map cY).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero:= by
 rw [bg,List.foldr_reverse,List.foldl_map]
 induction perm generalizing t with
 | nil => rfl
 | cons v perm ih =>
   simp only [List.all_cons,Bool.and_eq_true] at ok
   obtain ⟨lt,e⟩:= qh ok.1 ht
   rw [List.foldl_cons,e,ih ok.2 lt]
   rfl
noncomputable def decodeN:Nat → Nat → List Nat → List Nat
 | 0,_,ws => ws
 | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
     fun z => decodeN n (bits >>> 10) (ws++[z])
lemma ql (F:Sig → Nat) (F0:F zero=0) (Fb: ∀ op a b,F (bin op a b)=zN op (F a) (F b))
   (n bits:Nat) (ds:List Decor):
   (gr n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1):= by
 have gd (ds:List Decor) (i:Nat):(ds.map fun w => F w.1).getD i 0 = F (ds.getD i bq).1:= by
   simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
   cases ds[i]? with
   | none => exact F0.symm
   | some v => rfl
 induction n generalizing bits ds with
 | zero => rfl
 | succ n ih =>
   rw [decodeN,eA,gr,ih,gd,gd,←Fb,List.map_append]
   rfl
lemma mF {α β:Type} (f:α → β) (bits:Nat) (ws:List α):
   (cN bits ws).map f = cN bits (ws.map f):= by
 induction ws generalizing bits with
 | nil => rfl
 | cons w ws ih =>
   rw [List.map_cons,cN,cN]
   split
   · rw [List.map_cons,ih]
   · exact ih _
noncomputable def fastState (g:aM) (k i:Nat) (perm:List Nat):List Nat:=
 let raw:= (dy g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
 let (_,depth,_,_,_,_,_,data):= g.levels k
 let len:= 10*depth
 force (kq (g.levels k) (dy g.mask).length i) fun rec =>
 cN (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
lemma oX (g:aM) (k i:Nat) {perm:List Nat} (ok:perm.all eM=true):
   fastState g k i perm = ((bT g k i).map (bg (perm.map cY).reverse)).map BitVec.toNat:= by
 let ms:= (perm.map cY).reverse
 let F (a:Sig):Nat:= (bg ms a).toNat
 have F0:F zero=0:= by
   change (bg ms zero).toNat=0
   rw [cj,(iq _).1]
   simp [zero]
 have Fb (op a b):F (bin op a b)=zN op (F a) (F b):= by
   change (bg ms (bin op a b)).toNat = zN op (bg ms a).toNat (bg ms b).toNat
   rw [qy,cj,mR,cj,cj]
 have raw:(hJ g).map (fun w => F w.1) = (dy g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat:= by
   simp only [hJ,lq,List.map_map]
   apply List.map_congr_left
   rintro ⟨j,a⟩ hm
   obtain ⟨hj,rfl⟩:= iY hm
   exact congrArg BitVec.toNat (tv ok hj)
 have len:(hJ g).length = (dy g.mask).length:= by simp [hJ,lq]
 unfold fastState bT lf
 rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
 simp only [eA,mg,len]
 rw [List.map_map,List.map_map,mF,←raw,←ql F F0 Fb]
 rfl
noncomputable def linkedFast (g:aM) (k:Nat) (pair:Nat × Nat):Option (List Nat):=
 if pair.1 ≥ (g.levels k).1 then none else
   (g.autos[pair.2]?).bind fun perm => cond (perm.all eM) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g:aM) (k:Nat):Nat → Option (List Nat):= fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i j op:Nat) (ka kb:Bool):=
 let (k,n,r,_,cov):= b
 let len:= 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
 if len>k then true else
   let a:= ie b i
   let b':= ie b j
   let z:= hH op a b'
   let mask:= jg r (iz cov (cM (!u) a) (cM (!u) b') ka kb ||| cM (!u) z)
   ks (fun c => fallbackAt fl c i j op ka kb) mask xs
lemma oE {fl u} (k n) (xs:List bd) {i j op:Nat} {ka kb}
   (hi:i<n) (hj:j<n) {q:Nat} (hq:q<xs.length)
   (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl: ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (pass:batchMove fl u (db k n xs) (xs.map laneOf) i j op ka kb=true):
   iv xs[q] i j op ka kb=true:= by
 let len:= 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
 have eval:iv xs[q] i j op ka kb =
     if len>k then true else if lO xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
     else if !cS (dbin op (ay xs[q] i) (ay xs[q] j)).1 ||
       xs[q].2.2.1.any (fun v => v.1==(dbin op (ay xs[q] i) (ay xs[q] j)).1)
     then true else eP u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
       ((cB xs[q].2.2.1 (ay xs[q] i) (ay xs[q] j) ka kb).map Prod.fst)
       (bW op (ay xs[q] i) (ay xs[q] j)):= by
   simp only [iv,eZ,budget,arity,mode,len,lO] <;> rfl
 by_cases small:len>k
 · simp [eval,small]
 · let r:= units xs.length
   let a:= ie (db k n xs) i
   let b:= ie (db k n xs) j
   let cov:= jc (fun c:bd => c.2.2.2.1.1) xs
   change (if len>k then true else ks _ (jg r
      (iz cov (cM (!u) a) (cM (!u) b) ka kb |||
       cM (!u) (hH op a b))) (xs.map laneOf)) = true at pass
   rw [if_neg small] at pass
   have ca:a = _:= mb k n xs hi
   have cb:b = _:= mb k n xs hj
   dsimp only [r,cov] at pass
   rw [ca,cb,rt,h6,h6,h6,nz,mK] at pass
   by_cases hit:lO xs[q] (!u) ka kb op i j = BitVec.allOnes 152
   · apply m7 nd hfl
     have m:= se _ _ _ q (by simpa using hq) (by
       rw [ur _ _ _ hq]
       exact beq_iff_eq.mpr hit) pass
     simpa only [List.getElem_map] using m
   · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def batchPair (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i j op:Nat):=
 let f:= batchMove fl u b xs i j op
 f false false && f true false && f false true && f true true
noncomputable def batchRow (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i:Nat) (js:List Nat):=
   js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane):List Nat → Bool
 | [] => true
 | i::js => batchRow fl u b xs i js && batchRows fl u b xs js
lemma oV {fl u} (k n) (xs:List bd) {q:Nat} (hq:q<xs.length)
   (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl: ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (js:List Nat)
   (bounds: ∀ j ∈ js,j<n) (allRows:batchRows fl u (db k n xs) (xs.map laneOf) js=true):
   fv xs[q] (js.map (ay xs[q])) = true:= by
 induction js with
 | nil => rfl
 | cons i js ih =>
   simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
   simp only [List.map_cons,fv,oT,Bool.and_eq_true,List.all_eq_true,List.mem_map]
   have hi:= bounds i List.mem_cons_self
   refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
   rintro _ ⟨j,hj,rfl⟩ op hop
   have hj':= bounds j (List.mem_cons_of_mem _ hj)
   rw [mode] at hop
   have pass:= allRows.1 j hj op hop
   have check:= @oE fl u k n xs i j op
   simp only [batchPair,Bool.and_eq_true] at pass
   simp only [hG,Bool.and_eq_true]
   exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
     check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def runBatch (fl:Nat → Option (List Nat)) (u:Bool) (k n:Nat) (xs:List bd):=
   batchRows fl u (db k n xs) (xs.map laneOf) (List.range n)
lemma pd {fl u k n} {xs:List bd} {q} (hq:q<xs.length)
   (hb:xs[q].1=k) (ha:xs[q].2.1=n) (hm:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl: ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (hn:xs[q].2.2.1.length=n)
   (pass:runBatch fl u k n xs=true):fv xs[q] xs[q].2.2.1=true:= by
 have all:= oV k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
 have eq:(List.range n).map (ay xs[q]) = xs[q].2.2.1:= by
   apply List.ext_getElem
   · simp [hn]
   · intro i h1 h2
     simp [ay,List.getD_eq_getElem?_getD,h2]
 rwa [eq] at all
def gk (g:aM) (k i:Nat):bd:=
 let raw:= hJ g
 let (num,depth,cw,iw,pw,offw,lw,data):= g.levels k
 let (ops,bank,ws):= lf g k i
 let rules:= (ma (g.levels k) raw.length i).filterMap (fun (a,b) => je g ops depth bank a b)
 let ls:= fun tag => ((g.index k tag).bind (eI g (k-1))).toList
 (k,ws.length,ws,nn g.mode ws,rules,ls)
lemma us (g:aM) (k i tag:Nat) (ys) (h:flOf g k tag=some ys):
   ∃ xs ∈ (gk g k i).2.2.2.2.2 tag,ys=xs.map BitVec.toNat:= by
 change ∃ xs ∈ ((g.index k tag).bind (eI g (k-1))).toList,_
 unfold flOf at h
 cases hp:g.index k tag with
 | none => simp [hp] at h
 | some pair =>
   simp only [hp,Option.bind_some,linkedFast] at h
   simp only [Option.bind_some,eI]
   split at h
   · contradiction
   next v =>
     cases ha:g.autos[pair.2]? with
     | none => simp [ha] at h
     | some perm =>
       simp only [ha,Option.bind_some] at h
       cases hv:perm.all eM with
       | false => simp [hv] at h
       | true =>
         simp only [hv,cond_true,Option.some.injEq] at h
         refine ⟨(bT g (k-1) pair.1).map (bg (perm.map cY).reverse),?_,?_⟩
         · simp [v]
         · exact h.symm.trans (oX g _ _ hv)
def qe (T:Sig) (c:bd):=
 let ws:= c.2.2.1.map Prod.fst
 decide ws.Nodup && !(ws.contains T)
lemma o0 (g:aM) (k i:Nat):
   cL g k i = (qe (bo g) (gk g k i) &&
     (if k=0 then true else fv (gk g k i) (gk g k i).2.2.1)):= rfl
lemma sj {g k start n} (h: ∀ (i:Nat),start ≤ i → i < start + n → cL g k i = true):
   block g k start n=true:= by
 induction n with
 | zero => rfl
 | succ n ih =>
   simp only [block,Bool.and_eq_true]
   exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def gp (g:aM) (k start n:Nat):=
 ((List.range n).map (start+·)).map (gk g k)
def ts (g:aM) (k start n ar:Nat):=
 (gp g k start n).all (fun c => c.2.1==ar && qe (bo g) c)
noncomputable def rowCut (g:aM) (k start n ar lo len:Nat):=
 let xs:= gp g k start n
 let b:= db k ar xs
 forceLanes xs fun ys => (List.range len).all (fun d =>
   let i:= lo+d
   batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
lemma lX {g k start n ar lo len} (h:rowCut g k start n ar lo len=true)
   (i:Nat) (l:lo ≤ i) (r:i < lo+len):
   batchRow (flOf g k) g.mode (db k ar (gp g k start n)) ((gp g k start n).map laneOf)
     i (List.range' (i+1) (ar-(i+1)))=true:= by
 simp only [rowCut,jl] at h
 have ha:= List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
 simpa only [Nat.add_sub_of_le l] using ha
lemma ot {g k start n ar lo a b}
   (h:rowCut g k start n ar lo a=true) (t:rowCut g k start n ar (lo+a) b=true):
   rowCut g k start n ar lo (a+b)=true:= by
 simp only [rowCut,jl]
 apply List.all_eq_true.mpr
 intro j hj
 have jlt:= List.mem_range.mp hj
 by_cases first:j<a
 · exact lX h (lo+j) (by omega) (by omega)
 · exact lX t (lo+j) (by omega) (by omega)
lemma um {g k start n ar} (h:rowCut g k start n ar 0 ar=true):
   runBatch (flOf g k) g.mode k ar (gp g k start n)=true:= by
 let xs:= gp g k start n
 have go (lo num:Nat) (eq:lo+num=ar):
     batchRows (flOf g k) g.mode (db k ar xs) (xs.map laneOf) (List.range' lo num)=true:= by
   induction num generalizing lo with
   | zero => rfl
   | succ num ih =>
     simp only [List.range'_succ,batchRows,Bool.and_eq_true]
     refine ⟨?_,ih (lo+1) (by omega)⟩
     have ok:= lX h lo (by omega) (by omega)
     simpa only [show ar-(lo+1)=num by omega] using ok
 unfold runBatch
 rw [List.range_eq_range']
 exact go 0 ar (by omega)
lemma re {g k start n ar} (hd:ts g k start n ar=true)
   (h:rowCut g k start n ar 0 ar=true):block g k start n=true:= by
 apply sj
 intro i lo hi
 let xs:= gp g k start n
 have hm:gk g k i ∈ xs:= by
   apply List.mem_map.mpr
   exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
 obtain ⟨q,hq,e⟩:= List.getElem_of_mem hm
 have one:= List.all_eq_true.mp hd _ hm
 simp only [Bool.and_eq_true,beq_iff_eq] at one
 have hb:xs[q].1=k:= by rw [e];rfl
 have ha:xs[q].2.1=ar:= e ▸ one.1
 have nd:(xs[q].2.2.1.map Prod.fst).Nodup:= by
   have p:= one.2
   simp only [qe,Bool.and_eq_true,decide_eq_true_eq] at p
   rw [e]
   exact p.1
 have hfl: ∀ tag ys,flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat:= by
   rw [e]
   exact fun tag ys h => us g k i tag ys h
 have hm:xs[q].2.2.2.1.2=g.mode:= by rw [e];rfl
 have hn:xs[q].2.2.1.length=ar:= by rw [e];exact one.1
 rw [o0,Bool.and_eq_true]
 refine ⟨one.2,?_⟩
 split
 · rfl
 · exact e ▸ pd hq hb ha hm nd hfl hn (um h)
def boxes (g:aM) (k start n ar lo num:Nat):Nat → Prop
 | 0 => rowCut g k start n ar lo num=true
 | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
lemma tj {g k start n ar lo num d} (h:boxes g k start n ar lo num d):
   rowCut g k start n ar lo num=true:= by
 induction d generalizing lo num with
 | zero => exact h
 | succ d ih =>
   have v:= ot (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g:aM) (k start n ar rows:Nat):Nat → Prop
 | 0 => ts g k start n ar=true ∧ boxes g k start n ar 0 ar rows
 | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
lemma bC {g k start n ar rows d} (h:cells g k start n ar rows d):
   block g k start n=true:= by
 induction d generalizing start n with
 | zero => exact re h.1 (tj h.2)
 | succ d ih =>
   have v:= aT (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def cA {α} (f:α → Bool) (xs:List α):Nat → Prop
 | 0 => xs.all f=true
 | d+1 => cA f (xs.take (xs.length/2)) d ∧ cA f (xs.drop (xs.length/2)) d
lemma df {α f xs d} (h: @cA α f xs d):xs.all f=true:= by
 induction d generalizing xs with
 | zero => exact h
 | succ d ih =>
   have ap:((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:= by
     simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
   simpa only [List.take_append_drop] using ap
lemma qb {u} {raw:List Sig} {T:Sig} {L:Nat} (pT:bu T) (h:Lower u raw T L):
   Slice u raw T one L:= by
 refine ⟨id,raw,fun r => eV r,fun a ha => ?_,gz pT,h⟩
 exact Or.inl (List.mem_map_of_mem ha)
lemma iB {u} {m q cap:Nat} {prior:Nat → Nat} (low: ∀ q,Lower u (varsX q) (au q) (prior q))
   (e:(au q == au m && (varsX q == vars m) && (prior q == cap+1) && cS (au m) &&
     decide (vars m).Nodup && kz u one (cap+1) cap 0 (vars m) (vars m)) = true):
   az u (au m) cap (vars m).toFinset:= by
 simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
 obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩:= e
 have h:= low q
 rw [e1,e2,e3] at h
 exact jm (qb (dp _ e4) h) [] rfl e5 e6
lemma tt {u} {m cap:Nat} {prior:Nat → Nat} {ws:List Sig}
   (low: ∀ q,Lower u (varsX q) (au q) (prior q)) (ci:aZ)
   (ok:gm m ci prior = true)
   (cut:(decide ws.Nodup && kz u (hQ ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (hO m ci)) ws)=true):
   az u (au m) cap ws.toFinset:= by
 simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
 exact jm (ig ci prior low ok) [] rfl cut.1 cut.2
lemma ed {u} {g:aM} {m cap i:Nat} {prior:Nat → Nat} {ws:List Sig}
   (hm:g.mask=m) (hu:g.mode=u) (low: ∀ q,Lower u (varsX q) (au q) (prior q))
   (geom:aV g prior = true) (blocks:bP g cap)
   (idx:eh g cap i ws = true):az u (au m) cap ws.toFinset:= by
 subst hm
 subst hu
 exact nj low geom blocks (Nat.le_refl _) idx
def essOK (m hints:Nat):Bool:=
 let xs:= pW m hints
 cS (au m) && bU (au m) (vars m) xs && (xs.map Prod.fst == vars m)
lemma cu {u} {m hints cap:Nat} (ok:essOK m hints = true)
   (a:az u (au m) cap (vars m).toFinset):Lower u (vars m) (au m) (cap+1):= by
 simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
 apply eL (dp _ ok.1.1) (bX ok.1.2).1 (bX ok.1.2).2 _ a
 intro v hv
 apply ga ok.1.2 v
 rw [ok.2]
 exact List.mem_toFinset.mpr hv
def tp (m:Nat) (rs:List Nat):List (Sig × Row × Row):=
 ((dy m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def mE (m:Nat) (rs:List Nat):Bool:=
 let xs:= tp m rs
 bU (au m) (varsX m) xs && (xs.map Prod.fst == vars m) &&
   cS (au m) && decide (varsX m = vars m ++ [lz (m/512-1)])
lemma qi {u} {m:Nat} {rs:List Nat} (ok:mE m rs = true) {k:Nat} {S:Finset Sig}
   (h:Live u (au m) k S) (sub: ∀ v ∈ S,v ∈ varsX m):
   S=(vars m).toFinset ∨ S=(varsX m).toFinset:= by
 simp only [mE,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
 obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩:= ok
 have rest: ∀ v ∈ vars m,v ∈ S:= by
   intro v hv
   rw [←alls] at hv
   obtain ⟨r,s,hd,hi⟩:= ga ess v (List.mem_toFinset.mpr hv)
   exact ex h (varsX m) v sub r s hd hi
 have mem: ∀ v,v ∈ varsX m ↔ v ∈ vars m ∨ v=lz (m/512-1):= by
   intro v;rw [hX];simp
 by_cases hs:lz (m/512-1) ∈ S
 · refine Or.inr ?_
   ext v
   rw [List.mem_toFinset]
   refine ⟨sub v,fun hv => ?_⟩
   rcases (mem v).mp hv with hv | rfl
   · exact rest v hv
   · exact hs
 · refine Or.inl ?_
   ext v
   rw [List.mem_toFinset]
   refine ⟨fun hv => ?_,rest v⟩
   rcases (mem v).mp (sub v hv) with hv | rfl
   · exact hv
   · exact absurd hv hs
lemma pj {u} {m q cap:Nat} {rs:List Nat} (ok:mE m rs = true)
   (e:au m = au q) (ev:vars m = vars q)
   (a:az u (au q) cap (vars q).toFinset)
   (b:az u (au q) cap (varsX m).toFinset):
   Lower u (varsX m) (au m) (cap+1):= by
 have ok':= ok
 simp only [mE,Bool.and_eq_true] at ok'
 intro p bank hr ha
 obtain ⟨k,S,hk,run,hs⟩:= gv (dp _ ok'.1.2) (bX ok'.1.1.1).1 (bX ok'.1.1.1).2 hr ha
 by_contra! small
 rcases qi ok run hs with h | h
 · rw [ev] at h;rw [e,h] at run;exact a k (by omega) run
 · rw [e,h] at run;exact b k (by omega) run
structure eu (S:Finset Sig) (T:Sig) where
 owns:Sig → Row → Row → Prop
 total: ∀ p n,bit p T=true → bit n T=false → ∃ v,owns v p n
 valid: ∀ {v p n},owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
 unique: ∀ {v w p n},owns v p n → owns w p n → v=w
 rect: ∀ {v p n p' n'},owns v p n' → owns v p' n → owns v p n
def qj (T:Sig):eu {T} T where
 owns v p n:= v=T ∧ bit p T=true ∧ bit n T=false
 total p n hp hn:= ⟨T,rfl,hp,hn⟩
 valid:= by rintro v p n ⟨rfl,hp,hn⟩;exact ⟨by simp,hp,hn⟩
 unique:= by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩;exact eq.symm
 rect:= by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩;exact ⟨e,hp,hn⟩
def uh {U:Finset Sig} {T a b:Sig} {d:Nat} (d01:d=0 ∨ d=1)
   (ha:a∉U) (hb:b∉U) (hz:bin d a b∉U)
   (H:eu (insert (bin d a b) U) T):eu (insert a (insert b U)) T:= by
 let z:= bin d a b
 let sel:= fun p n:Row => if d=0 then (if bit n a then b else a)
   else (if bit p a then a else b)
 have pick (p n):sel p n=a ∨ sel p n=b:= by
   dsimp only [sel];split <;> split <;> simp
 have outside (p n):sel p n ∉ U:= by
   rcases pick p n with eq | eq
   · simpa only [eq] using ha
   · simpa only [eq] using hb
 have separates (p n) (hp:bit p z=true) (hn:bit n z=false):
     bit p (sel p n) = true ∧ bit n (sel p n) = false:= by
   have b0 (r:Row):bit r (bin 0 a b) = (bit r a && bit r b):= by simp [bin,bit]
   have b1 (r:Row):bit r (bin 1 a b) = (bit r a || bit r b):= by simp [bin,bit]
   rcases d01 with e | e <;> cases pA:bit p a <;> cases nA:bit n a <;>
     simp_all [sel,z]
 refine { owns:= fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
          total:= ?_
          valid:= ?_
          unique:= ?_
          rect:= ?_}
 · intro p n hp hn
   obtain ⟨v,hv⟩:= H.total p n hp hn
   rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
   · have vz:v=z:= eq
     refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
     rw [←vz]
     exact hv
   · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
 · intro v p n h
   rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
   · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
   · subst v
     have inS:sel p n ∈ insert a (insert b U):= by
       rcases pick p n with eq | eq <;> simp [eq]
     exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
 · intro v w p n h1 h2
   rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
   · exact H.unique hv hw
   · apply False.elim
     apply hz
     change z∈U
     rw [←H.unique hv hw]
     exact vU
   · apply False.elim
     apply hz
     change z∈U
     rw [←H.unique hw hv]
     exact wU
   · exact ve.trans we.symm
 · intro v p n p' n' h1 h2
   rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
   · exact Or.inl ⟨vU,H.rect hv hw⟩
   · exact False.elim (outside p' n (we ▸ vU))
   · exact False.elim (outside p n' (ve ▸ wU))
   · refine Or.inr ⟨?_,H.rect hv hw⟩
     by_cases h:d=0
     · simpa only [sel,h,ite_true] using we
     · simpa only [sel,h,ite_false] using ve
lemma oP {u T k S} (h:Live u T k S):S.card ≤ k+1:= by
 induction h using Live.ind with
 | stop hp => simp
 | @binary k U a b d hd ha hb hab hf tail ih =>
   have hu:bin d a b ∉ U:= fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
   rw [Finset.card_insert_of_notMem hu] at ih
   have h1:= Finset.card_insert_le (a:=a) (insert b U)
   have h2:= Finset.card_insert_le (a:=b) U
   omega
lemma oY {T k S} (run:Live false T k S) (tight:S.card=k+1):
   Nonempty (eu S T):= by
 induction k generalizing S with
 | zero =>
   obtain ⟨rfl,_⟩:= run
   exact ⟨qj T⟩
 | succ k ih =>
   obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩:= run
   have fresh:bin d a b∉U:= fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
   have li:= oP tail
   rw [Finset.card_insert_of_notMem fresh] at li
   have le1:= Finset.card_insert_le (a:=a) (insert b U)
   have le2:= Finset.card_insert_le (a:=b) U
   have ha:a∉U:= by
     intro h
     rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h:a∈insert b U)] at tight
     omega
   have hb:b∉U:= by
     intro h
     rw [Finset.insert_eq_of_mem h] at tight le1
     omega
   have eq:(insert (bin d a b) U).card=k+1:= by
     rw [Finset.card_insert_of_notMem fresh]
     omega
   obtain ⟨H⟩:= ih tail eq
   have d01:d=0 ∨ d=1:= by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
   exact ⟨uh d01 ha hb fresh H⟩
def bA (S:Finset Sig) (T v:Sig) (p n:Row):=
 bit p T=true ∧ bit n T=false ∧ ∀ w∈S,bit p w=true → bit n w=false → w=v
lemma kwOwn {S T v p n} (H:eu S T) (one:bA S T v p n):H.owns v p n:= by
 obtain ⟨w,hw⟩:= H.total p n one.1 one.2.1
 have eq:= one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
 exact eq ▸ hw
lemma un {S T k a b p n pa pb na nb} (size:k+1=S.card) (different:a≠b)
   (A:bA S T a p na) (B:bA S T b p nb)
   (C:bA S T a pa n) (D:bA S T b pb n):az false T k S:= by
 intro j hj run
 have lb:= oP run
 have tight:S.card=j+1:= by omega
 obtain ⟨H⟩:= oY run tight
 exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
structure dq (S:Finset Sig) (T H:Sig) where
 owns:Sig → Row → Row → Prop
 total: ∀ p n,bit p T=true → bit n T=false →
   (bit p H=true ∧ bit n H=false) ∨ ∃ v,owns v p n
 valid: ∀ {v p n},owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
 unique: ∀ {v w p n},owns v p n → owns w p n → v=w
 rect: ∀ {v p n p' n'},owns v p n' → owns v p' n → owns v p n
structure bD (S:Finset Sig) (T:Sig) where
 inner:Finset Sig
 outer:Finset Sig
 pivot:Sig
 cover:inner ∪ outer = S
 apart:Disjoint inner outer
 inside:eu inner pivot
 outside:dq outer T pivot
def ta {S T} (D:eu S T) (h:Sig):dq S T h where
 owns:= D.owns
 total p n hp hn:= Or.inr (D.total p n hp hn)
 valid:= D.valid
 unique:= D.unique
 rect:= D.rect
def pI {S T h} (D:dq S T h):dq (S.erase h) T h where
 owns v p n:= v≠h ∧ D.owns v p n
 total:= by
   intro p n hp hn
   rcases D.total p n hp hn with yes | ⟨v,hv⟩
   · exact Or.inl yes
   · by_cases eq:v=h
     · exact Or.inl (eq ▸ (D.valid hv).2)
     · exact Or.inr ⟨v,eq,hv⟩
 valid:= by
   rintro v p n ⟨ne,hv⟩
   exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
 unique:= fun h1 h2 => D.unique h1.2 h2.2
 rect:= fun a b => ⟨a.1,D.rect a.2 b.2⟩
def oz {S T} (D:eu S T):bD S T where
 inner:= S
 outer:= ∅
 pivot:= T
 cover:= by simp
 apart:= by simp
 inside:= D
 outside:= {
   owns:= fun _ _ _ => False
   total:= fun p n hp hn => Or.inl ⟨hp,hn⟩
   valid:= fun h => h.elim
   unique:= fun h _ => h.elim
   rect:= fun h _ => h.elim}
def o1 {h:Sig} {U:Finset Sig} {T a b:Sig} {d:Nat} (d01:d=0 ∨ d=1)
   (ha:a∉U) (hb:b∉U) (hz:bin d a b∉U)
   (H:dq (insert (bin d a b) U) T h):dq (insert a (insert b U)) T h:= by
 let z:= bin d a b
 let sel:= fun p n:Row => if d=0 then (if bit n a then b else a)
   else (if bit p a then a else b)
 have pick (p n):sel p n=a ∨ sel p n=b:= by
   dsimp only [sel];split <;> split <;> simp
 have outside (p n):sel p n ∉ U:= by
   rcases pick p n with eq | eq
   · simpa only [eq] using ha
   · simpa only [eq] using hb
 have separates (p n) (hp:bit p z=true) (hn:bit n z=false):
     bit p (sel p n) = true ∧ bit n (sel p n) = false:= by
   have b0 (r:Row):bit r (bin 0 a b) = (bit r a && bit r b):= by simp [bin,bit]
   have b1 (r:Row):bit r (bin 1 a b) = (bit r a || bit r b):= by simp [bin,bit]
   rcases d01 with e | e <;> cases pA:bit p a <;> cases nA:bit n a <;>
     simp_all [sel,z]
 refine { owns:= fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
          total:= ?_
          valid:= ?_
          unique:= ?_
          rect:= ?_}
 · intro p n hp hn
   rcases H.total p n hp hn with closed | ⟨v,hv⟩
   · exact Or.inl closed
   right
   rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
   · have vz:v=z:= eq
     refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
     rw [←vz]
     exact hv
   · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
 · intro v p n h
   rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
   · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
   · subst v
     have inS:sel p n ∈ insert a (insert b U):= by
       rcases pick p n with eq | eq <;> simp [eq]
     exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
 · intro v w p n h1 h2
   rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
   · exact H.unique hv hw
   · apply False.elim
     apply hz
     change z∈U
     rw [←H.unique hv hw]
     exact vU
   · apply False.elim
     apply hz
     change z∈U
     rw [←H.unique hw hv]
     exact wU
   · exact ve.trans we.symm
 · intro v p n p' n' h1 h2
   rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
   · exact Or.inl ⟨vU,H.rect hv hw⟩
   · exact False.elim (outside p' n (we ▸ vU))
   · exact False.elim (outside p n' (ve ▸ wU))
   · refine Or.inr ⟨?_,H.rect hv hw⟩
     by_cases h:d=0
     · simpa only [sel,h,ite_true] using we
     · simpa only [sel,h,ite_false] using ve
lemma l5 {A B U:Finset Sig} {a b z:Sig}
   (e:A∪B=insert z U) (disj:Disjoint A B) (za:z∈A)
   (freshA:a∉insert z U) (freshB:b∉insert z U) (freshZ:z∉U):
   (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
   Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z:= by
 have hb:z∉B:= fun h => Finset.disjoint_left.mp disj za h
 have allmem (w:Sig):w∈A∨w∈B ↔ w=z∨w∈U:= by
   rw [←Finset.mem_union,←Finset.mem_insert,e]
 have aout:a∉A ∧ a∉B:= by
   have h:a∉A∪B:= by rw [e];exact freshA
   simpa using h
 have bout:b∉A ∧ b∉B:= by
   have h:b∉A∪B:= by rw [e];exact freshB
   simpa using h
 refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
 · ext w
   have m:= allmem w
   by_cases eq:w=z
   · subst w;simp [freshZ,hb]
   · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
     tauto
 · apply Finset.disjoint_left.mpr
   intro w hw hwB
   rcases Finset.mem_insert.mp hw with rfl | hw
   · exact aout.2 hwB
   rcases Finset.mem_insert.mp hw with rfl | hw
   · exact bout.2 hwB
   exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB
def oF {U T a b d} (hd:d=0 ∨ d=1)
   (freshA:a∉insert (bin d a b) U) (freshB:b∉insert (bin d a b) U)
   (freshZ:bin d a b∉U) (F:bD (insert (bin d a b) U) T):
   bD (insert a (insert b U)) T:= by
 classical
 let z:= bin d a b
 by_cases inn:z∈F.inner
 · obtain ⟨eq,apart,ha,hb⟩:= l5 F.cover F.apart inn freshA freshB freshZ
   have old:eu (insert z (F.inner.erase z)) F.pivot:= by
     rw [Finset.insert_erase inn];exact F.inside
   exact ⟨_,F.outer,F.pivot,eq,apart,uh hd ha hb (by simp [z]) old,F.outside⟩
 · have out:z∈F.outer:= by
     have m:z∈F.inner∪F.outer:= by rw [F.cover];exact Finset.mem_insert_self _ _
     exact (Finset.mem_union.mp m).resolve_left inn
   obtain ⟨eq,apart,ha,hb⟩:= l5 ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
   have old:dq (insert z (F.outer.erase z)) T F.pivot:= by
     rw [Finset.insert_erase out];exact F.outside
   exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
     o1 hd ha hb (by simp [z]) old⟩
def nh {U T a b d} (hd:d=0 ∨ d=1) (ab:a≠b) (hb:b∉U)
   (fresh:bin d a b∉insert a (insert b U)) (H:eu (insert (bin d a b) U) T):
   bD (insert a (insert b U)) T:= by
 let z:= bin d a b
 have za:z≠a:= by
   intro eq
   apply fresh
   exact Finset.mem_insert.mpr (Or.inl eq)
 have zU:z∉U:= fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
 have set0:(insert z U).erase a = insert z (U.erase a):= by
   ext v
   simp only [Finset.mem_erase,Finset.mem_insert]
   by_cases eq:v=z
   · subst v;simp [za]
   · tauto
 have H0:dq (insert z (U.erase a)) T a:= set0 ▸ pI (ta H a)
 have H1:= o1 hd (show a∉U.erase a by simp)
   (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
 have eq:insert a (insert b (U.erase a))=insert a (insert b U):= by
   ext v
   simp only [Finset.mem_insert,Finset.mem_erase]
   tauto
 have H1':dq (insert a (insert b U)) T a:= eq ▸ H1
 refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,qj a,pI H1'⟩
 · ext v;simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert];tauto
 · simp
lemma tu {T k S} (r:Live false T k S) (budget:k≤S.card):
   Nonempty (bD S T):= by
 induction k generalizing S with
 | zero =>
   obtain ⟨rfl,_⟩:= r
   exact ⟨oz (qj T)⟩
 | succ k ih =>
   obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩:= r
   let z:= bin d a b
   have zU:z∉U:= fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
   have size:= oP tail
   have zcard:(insert z U).card=U.card+1:= Finset.card_insert_of_notMem zU
   change (insert z U).card ≤ k+1 at size
   have hd01:d=0 ∨ d=1:= by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
   by_cases ain:a∈U
   · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain:a∈insert b U)] at budget
     by_cases bin':b∈U
     · rw [Finset.insert_eq_of_mem bin'] at budget;omega
     · rw [Finset.card_insert_of_notMem bin'] at budget
       obtain ⟨H⟩:= oY tail (by change (insert z U).card=k+1;omega)
       exact ⟨nh hd01 ab bin' fresh H⟩
   · by_cases bin':b∈U
     · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
       obtain ⟨H⟩:= oY tail (by change (insert z U).card=k+1;omega)
       have comm:bin d b a=z:= by
         rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
       have H':eu (insert (bin d b a) U) T:= by simpa only [comm] using H
       have fr:bin d b a∉insert b (insert a U):= by simpa only [comm,Finset.insert_comm] using fresh
       have F:= nh hd01 ab.symm ain fr H'
       exact ⟨by simpa only [Finset.insert_comm] using F⟩
     · have an:a∉insert b U:= by simp [ain,ab]
       rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
       obtain ⟨F⟩:= ih tail (by change k≤(insert z U).card;omega)
       have neA:a≠z:= fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
       have neB:b≠z:= fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
       have fa:a∉insert z U:= fun h => (Finset.mem_insert.mp h).elim neA ain
       have fb:b∉insert z U:= fun h => (Finset.mem_insert.mp h).elim neB bin'
       exact ⟨oF hd01 fa fb zU F⟩
lemma oS {S:Finset Sig} {T:Sig} (F:bD S T) (p n:Row)
   (hp:bit p T=true) (hn:bit n T=false)
   (none: ∀ v∈F.outer,bit p v=true → bit n v=false → False):
   bit p F.pivot=true ∧ bit n F.pivot=false:= by
 rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
 · exact h
 · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
lemma eD {S:Finset Sig} {T:Sig} (F:bD S T) {a p n} (ao:a∈F.outer)
   (one:bA S T a p n):F.outside.owns a p n:= by
 rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
 · obtain ⟨w,hw⟩:= F.inside.total p n hpivot.1 hpivot.2
   obtain ⟨wi,wp,wn⟩:= F.inside.valid hw
   have ws:w∈S:= F.cover ▸ Finset.mem_union_left _ wi
   have eq:= one.2.2 w ws wp wn
   rw [eq] at wi
   exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
 · obtain ⟨wo,wp,wn⟩:= F.outside.valid hw
   have ws:w∈S:= F.cover ▸ Finset.mem_union_right _ wo
   have eq:= one.2.2 w ws wp wn
   exact eq ▸ hw
lemma lV {S:Finset Sig} {T:Sig} (F:bD S T) {a b p n pa pb na nb}
   (aout:a∈F.outer) (bout:b∈F.outer)
   (different:a≠b) (A:bA S T a p na) (B:bA S T b p nb)
   (C:bA S T a pa n) (D:bA S T b pb n):False:=
 different (F.outside.unique (F.outside.rect (eD F aout A) (eD F aout C))
   (F.outside.rect (eD F bout B) (eD F bout D)))
lemma lR {S:Finset Sig} {T:Sig} (F:bD S T) {a b p n pa pb na nb}
   (different:a≠b) (A:bA F.inner F.pivot a p na) (B:bA F.inner F.pivot b p nb)
   (C:bA F.inner F.pivot a pa n) (D:bA F.inner F.pivot b pb n):False:=
 different (F.inside.unique (F.inside.rect (kwOwn F.inside A) (kwOwn F.inside C))
   (F.inside.rect (kwOwn F.inside B) (kwOwn F.inside D)))
lemma el {S:Finset Sig} {T:Sig} (F:bD S T) {v p n}
   (hv:v∈F.inner) (only:bA S T v p n):bA F.inner F.pivot v p n:= by
 have h:bit p F.pivot=true ∧ bit n F.pivot=false:= by
   apply oS F p n only.1 only.2.1
   intro w wo hp hn
   have ws:w∈S:= F.cover ▸ Finset.mem_union_right _ wo
   have eq:= only.2.2 w ws hp hn
   exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
 refine ⟨h.1,h.2,?_⟩
 intro w wi hp hn
 exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
lemma bB {S:Finset Sig} {T:Sig} (F:bD S T) {a b c p n pa na}
   (ar:bA S T a p na) (br:bA S T b pa n) (cr:bA S T c p n)
   (ia:a∈F.inner) (ib:b∈F.inner):c∈F.inner:= by
 have ah:= el F ia ar
 have bh:= el F ib br
 obtain ⟨w,hw⟩:= F.inside.total p n ah.1 bh.2.1
 obtain ⟨wi,wp,wn⟩:= F.inside.valid hw
 have ws:w∈S:= F.cover ▸ Finset.mem_union_left _ wi
 exact (cr.2.2 w ws wp wn) ▸ wi
lemma bN {S:Finset Sig} {T:Sig} (F:bD S T) {a b p n pa pb na nb}
   (hs:a∈S) (ht:b∈S) (ne:a≠b)
   (h1:bA S T a p na) (h2:bA S T b p nb)
   (h3:bA S T a pa n) (h4:bA S T b pb n):
   ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False:= by
 rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
 · exact lR F ne (el F ia h1) (el F ib h2)
     (el F ia h3) (el F ib h4)
 · rw [←F.cover,Finset.mem_union] at hs ht
   exact lV F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def it (ws:List Sig) (T v:Sig) (p n:Row):Bool:=
 bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
lemma ea {ws T v p n} (h:it ws T v p n=true):
   bA ws.toFinset T v p n:= by
 simp only [it,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
 refine ⟨h.1.1,h.1.2,?_⟩
 intro w hw hp hn
 simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
   h.2 w (List.mem_toFinset.mp hw)
def hV (xs q:Nat):Row:= Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def np (pos neg:Nat) (T:Sig) (ws:List Sig) (k value:Nat):Bool:=
 let field:= fun i => (value >>> (4*i)) &&& 15
 let a:= ws.getD (field 0) zero
 let b:= ws.getD (field 1) zero
 let p:= hV pos (field 2)
 let n:= hV neg (field 3)
 decide (k+1=ws.toFinset.card) && decide (a≠b) &&
   it ws T a p (hV neg (field 4)) && it ws T b p (hV neg (field 5)) &&
   it ws T a (hV pos (field 6)) n && it ws T b (hV pos (field 7)) n
lemma lh {pos neg T ws k v} (h:np pos neg T ws k v=true):az false T k ws.toFinset:= by
 simp only [np,Bool.and_eq_true,decide_eq_true_eq] at h
 exact un h.1.1.1.1.1 h.1.1.1.1.2 (ea h.1.1.1.2)
   (ea h.1.1.2) (ea h.1.2) (ea h.2)
def ba (g:aM) (k start n:Nat):Prop:=
 ∀ j,start≤j → j<start+n → cL g k j=true ∨ az g.mode (bo g) k (bT g k j).toFinset
lemma as (g:aM) (k a:Nat):ba g k a 0:= by
 intro j lo hi
 omega
lemma aH {g k a n} (h:block g k a n=true):ba g k a n:=
 fun j lo hi => Or.inl (mZ h j lo hi)
lemma ak {g k a x y} (first:ba g k a x) (last:ba g k (a+x) y):
   ba g k a (x+y):= by
 intro j lo hi
 by_cases e:j<a+x
 · exact first j lo e
 · exact last j (by omega) (by omega)
def sv (pos neg:Nat) (g:aM) (k a n:Nat) (data:Nat → Nat):=
 (List.range n).all (fun j => np pos neg (bo g) (bT g k (a+j)) k (bE data (32*j) 32))
lemma e9 {pos neg g k a n data} (mode:g.mode=false) (h:sv pos neg g k a n data=true):
   ba g k a n:= by
 intro j lo hi
 right
 rw [mode]
 have hh:= List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
 have sum:a+(j-a)=j:= by omega
 change np pos neg _ (bT g k (a+(j-a))) k _=true at hh
 rw [sum] at hh
 exact lh hh
def bS (g:aM) (top:Nat):= ∀ k ≤ top,ba g k 0 (g.levels k).1
lemma pK (g:aM) (top:Nat) (prior:Nat → Nat)
   (lower: ∀ q,Lower g.mode (varsX q) (au q) (prior q))
   (geometry:aV g prior=true) (rows:bS g top):
   ∀ k ≤ top,∀ i < (g.levels k).1,az g.mode (bo g) k (bT g k i).toFinset:= by
 simp only [aV,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
 intro k
 induction k with
 | zero =>
   intro hk i hi
   rcases rows 0 hk i (by omega) (by omega) with checked | done
   · exact cW g 0 i (hP geometry.1.1.1 geometry.1.1.2)
       (fun x hx => ig _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
   · exact done
 | succ k ih =>
   intro hk i hi
   rcases rows _ hk i (by omega) (by omega) with checked | done
   · exact cW g _ i (hP geometry.1.1.1 geometry.1.1.2)
       (fun x hx => ig _ prior lower (geometry.1.2 x hx)) geometry.2
       (fun _ => by simpa using ih (by omega)) checked
   · exact done
lemma ol {g top prior k i ws} (lower: ∀ q,Lower g.mode (varsX q) (au q) (prior q))
   (geom:aV g prior=true) (blocks:bS g top) (le:k≤top)
   (idx:eh g k i ws=true):az g.mode (bo g) k ws.toFinset:= by
 simp only [eh,Bool.and_eq_true,decide_eq_true_eq] at idx
 rw [←fj idx.2]
 exact pK g top prior lower geom blocks _ le i idx.1
abbrev ep:= Nat × Nat × Nat
def cQ (arity:Nat) (tags:List ep):Prop:=
 ∀ {S T},(F:bD S T) → (w:Nat → Sig) → (p n:Nat → Row) →
   (∀ i<arity,w i∈S) → (∀ i<arity,∀ j<arity,i≠j → w i≠w j) →
   (∀ t∈tags,bA S T (w t.1) (p t.2.1) (n t.2.2)) → False
structure mU where
 arity:Nat
 tags:List ep
 closed:cQ arity tags
def u8:List ep:= [(0,0,2),(1,1,2),(2,2,3),(3,3,3),(0,4,1),(1,4,3),(2,5,0),(3,5,1),(3,5,2)]
lemma wP (A0 A1 A2 A3:Prop):(((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A2 → A1) → (A0 → A3 → A1) → (A2 → A1 → A3) → False:= by tauto
lemma k5:cQ 4 u8:= by
 intro S T F w p n mem diff cells
 have c0:= cells (0,0,2) (by decide)
 have c1:= cells (1,1,2) (by decide)
 have c2:= cells (2,2,3) (by decide)
 have c3:= cells (3,3,3) (by decide)
 have c4:= cells (0,4,1) (by decide)
 have c5:= cells (1,4,3) (by decide)
 have c6:= cells (2,5,0) (by decide)
 have c7:= cells (3,5,1) (by decide)
 have c8:= cells (3,5,2) (by decide)
 have r0:= bN F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
 have r1:= bN F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
 have r2:= bB F c5 c7 c4
 have r3:= bB F c4 c2 c5
 have r4:= bB F c4 c3 c5
 have r5:= bB F c6 c1 c8
 exact wP (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def u9:List ep:= [(0,0,1),(1,1,3),(2,2,0),(1,2,2),(3,3,1),(2,3,3),(3,4,2),(0,4,3)]
lemma wQ (A0 A1 A2 A3:Prop):(((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A3 → A1) → (A2 → A0 → A3) → (A3 → A1 → A2) → (A0 → A1 → A3) → False:= by tauto
lemma k6:cQ 4 u9:= by
 intro S T F w p n mem diff cells
 have c0:= cells (0,0,1) (by decide)
 have c1:= cells (1,1,3) (by decide)
 have c2:= cells (2,2,0) (by decide)
 have c3:= cells (1,2,2) (by decide)
 have c4:= cells (3,3,1) (by decide)
 have c5:= cells (2,3,3) (by decide)
 have c6:= cells (3,4,2) (by decide)
 have c7:= cells (0,4,3) (by decide)
 have r0:= bN F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
 have r1:= bN F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c7 c6 c0 c4
 have r2:= bB F c2 c6 c3
 have r3:= bB F c5 c0 c4
 have r4:= bB F c4 c1 c5
 have r5:= bB F c7 c3 c6
 exact wQ (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def uA:List ep:= [(0,0,2),(1,1,1),(2,2,0),(1,2,2),(3,3,0),(0,3,1),(2,4,1),(3,4,2)]
lemma wR (A0 A1 A2 A3:Prop):(((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A2) → (A2 → A0 → A1) → False:= by tauto
lemma k7:cQ 4 uA:= by
 intro S T F w p n mem diff cells
 have c0:= cells (0,0,2) (by decide)
 have c1:= cells (1,1,1) (by decide)
 have c2:= cells (2,2,0) (by decide)
 have c3:= cells (1,2,2) (by decide)
 have c4:= cells (3,3,0) (by decide)
 have c5:= cells (0,3,1) (by decide)
 have c6:= cells (2,4,1) (by decide)
 have c7:= cells (3,4,2) (by decide)
 have r0:= bN F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c6
 have r1:= bN F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c5 c4 c0 c7
 have r2:= bN F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c7 c2 c4
 have r3:= bB F c3 c4 c2
 have r4:= bB F c2 c0 c3
 exact wR (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def uB:List ep:= [(0,0,0),(1,1,0),(2,2,3),(3,3,3),(2,4,1),(3,4,2),(1,5,1),(1,5,2),(0,5,3)]
lemma wS (A0 A1 A2 A3:Prop):(((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (A3 → A1 → A2) → (A2 → A1 → A3) → (A0 → A2 → A1) → (A0 → A3 → A1) → False:= by tauto
lemma k8:cQ 4 uB:= by
 intro S T F w p n mem diff cells
 have c0:= cells (0,0,0) (by decide)
 have c1:= cells (1,1,0) (by decide)
 have c2:= cells (2,2,3) (by decide)
 have c3:= cells (3,3,3) (by decide)
 have c4:= cells (2,4,1) (by decide)
 have c5:= cells (3,4,2) (by decide)
 have c6:= cells (1,5,1) (by decide)
 have c7:= cells (1,5,2) (by decide)
 have c8:= cells (0,5,3) (by decide)
 have r0:= bN F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c4 c5 c2 c3
 have r1:= bN F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c8 c7 c0 c1
 have r2:= bB F c5 c6 c4
 have r3:= bB F c4 c7 c5
 have r4:= bB F c8 c4 c6
 have r5:= bB F c8 c5 c7
 exact wS (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def uC:List ep:= [(0,0,3),(1,1,3),(2,2,3),(3,3,3),(0,4,1),(1,4,2),(2,5,0),(3,5,1),(3,5,2)]
lemma wT (A0 A1 A2 A3:Prop):(((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A3 → A1) → (A2 → A0 → A3) → (A2 → A1 → A3) → False:= by tauto
lemma k9:cQ 4 uC:= by
 intro S T F w p n mem diff cells
 have c0:= cells (0,0,3) (by decide)
 have c1:= cells (1,1,3) (by decide)
 have c2:= cells (2,2,3) (by decide)
 have c3:= cells (3,3,3) (by decide)
 have c4:= cells (0,4,1) (by decide)
 have c5:= cells (1,4,2) (by decide)
 have c6:= cells (2,5,0) (by decide)
 have c7:= cells (3,5,1) (by decide)
 have c8:= cells (3,5,2) (by decide)
 have r0:= bN F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
 have r1:= bN F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
 have r2:= bB F c5 c7 c4
 have r3:= bB F c4 c8 c5
 have r4:= bB F c6 c4 c7
 have r5:= bB F c6 c5 c8
 exact wT (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def uD:List ep:= [(0,0,2),(1,1,3),(2,2,0),(1,2,4),(3,3,1),(2,3,3),(0,3,4),(3,4,2),(4,4,3),(4,4,4)]
lemma wV (A0 A1 A2 A3 A4:Prop):(((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A0 → A1) → (A3 → A1 → A2) → (A0 → A1 → A2) → (A2 → A4 → A1) → (A3 → A2 → A4) → False:= by tauto
lemma kA:cQ 5 uD:= by
 intro S T F w p n mem diff cells
 have c0:= cells (0,0,2) (by decide)
 have c1:= cells (1,1,3) (by decide)
 have c2:= cells (2,2,0) (by decide)
 have c3:= cells (1,2,4) (by decide)
 have c4:= cells (3,3,1) (by decide)
 have c5:= cells (2,3,3) (by decide)
 have c6:= cells (0,3,4) (by decide)
 have c7:= cells (3,4,2) (by decide)
 have c8:= cells (4,4,3) (by decide)
 have c9:= cells (4,4,4) (by decide)
 have r0:= bN F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
 have r1:= bN F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c6 c4 c0 c7
 have r2:= bB F c2 c6 c3
 have r3:= bB F c4 c1 c5
 have r4:= bB F c6 c1 c5
 have r5:= bB F c2 c9 c3
 have r6:= bB F c7 c5 c8
 exact wV (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) (w 4∈F.inner) r0 r1 r2 r3 r4 r5 r6
def uE:List ep:= [(0,0,0),(1,1,0),(2,2,3),(2,3,1),(3,3,2),(1,4,2),(0,4,3),(1,5,1),(3,5,3)]
lemma wW (A0 A1 A2 A3:Prop):(((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A1 ∧ A3) ∨ (¬A1 ∧ ¬A3)) → False) → (A2 → A1 → A3) → (A0 → A3 → A1) → False:= by tauto
lemma kB:cQ 4 uE:= by
 intro S T F w p n mem diff cells
 have c0:= cells (0,0,0) (by decide)
 have c1:= cells (1,1,0) (by decide)
 have c2:= cells (2,2,3) (by decide)
 have c3:= cells (2,3,1) (by decide)
 have c4:= cells (3,3,2) (by decide)
 have c5:= cells (1,4,2) (by decide)
 have c6:= cells (0,4,3) (by decide)
 have c7:= cells (1,5,1) (by decide)
 have c8:= cells (3,5,3) (by decide)
 have r0:= bN F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c3 c4 c2 c8
 have r1:= bN F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c6 c5 c0 c1
 have r2:= bN F (mem 1 (by decide)) (mem 3 (by decide)) (diff 1 (by decide) 3 (by decide) (by decide)) c7 c8 c5 c4
 have r3:= bB F c3 c5 c4
 have r4:= bB F c6 c4 c5
 exact wW (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def uz:Nat → mU
 | 0 => ⟨4,u8,k5⟩
 | 1 => ⟨4,u9,k6⟩
 | 2 => ⟨4,uA,k7⟩
 | 3 => ⟨4,uB,k8⟩
 | 4 => ⟨4,uC,k9⟩
 | 5 => ⟨5,uD,kA⟩
 | _ => ⟨4,uE,kB⟩
def pV (arity:Nat) (ws:List Sig) (w:Nat→Sig):=
 (List.range arity).all (fun i => decide (w i∈ws) &&
   (List.range arity).all (fun j => (i==j) || decide (w i≠w j)))
def mW (pc:mU) (ws:List Sig) (T:Sig) (w:Nat→Sig) (p n:Nat→Row):=
 pV pc.arity ws w &&
   pc.tags.all (fun t => it ws T (w t.1) (p t.2.1) (n t.2.2))
lemma lC {a b:Bool} (h:(a && b)=true):a=true ∧ b=true:= by
 simpa only [Bool.and_eq_true] using h
lemma jy {pc ws T w p n} (F:bD (List.toFinset ws) T)
   (h:mW pc ws T w p n=true):False:= by
 have ij:= (lC h).1
 have hrow (i:Nat) (hi:i<pc.arity):= lC
   (List.all_eq_true.mp ij i (List.mem_range.mpr hi))
 apply pc.closed F w p n
 · intro i hi
   exact List.mem_toFinset.mpr (of_decide_eq_true (hrow i hi).1)
 · intro i hi j hj ne
   have one:= List.all_eq_true.mp (hrow i hi).2 j (List.mem_range.mpr hj)
   have diff:(i==j)=false:= beq_eq_false_iff_ne.mpr ne
   simpa only [diff,Bool.false_or,decide_eq_true_eq] using one
 · intro t ht
   exact ea (List.all_eq_true.mp (lC h).2 t ht)
def jf (pos neg:Nat) (ws:List Sig) (T:Sig) (k rec:Nat):=
 let field:= fun i => (rec >>> (4*i)) &&& 15
 decide (k≤ws.toFinset.card) && mW (uz (field 0)) ws T
   (fun i => ws.getD (field (1+i)) zero)
   (fun i => hV pos (field (6+i))) (fun i => hV neg (field (12+i)))
lemma iL {pos neg ws T k rec} (ok:jf pos neg ws T k rec=true):
   az false T k ws.toFinset:= by
 obtain ⟨bound,check⟩:= lC ok
 intro j hj live
 obtain ⟨F⟩:= tu live (hj.trans (of_decide_eq_true bound))
 exact jy F check
def f1:Nat:= 0x9050141084210842110c0300c03
def f0:Nat:= 0xc9606290568325147434114642a
def iJ (pos neg:Nat) (g:aM) (k start n:Nat) (data:Nat→Nat):=
 (List.range n).all (fun i => jf pos neg (bT g k (start+i)) (bo g) k (data i))
lemma ml {pos neg g k start n data} (mode:g.mode=false)
   (ok:iJ pos neg g k start n data=true):ba g k start n:= by
 intro j lo hi
 right
 rw [mode]
 have h:= List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
 have e:start+(j-start)=j:= by omega
 change jf pos neg (bT g k (start+(j-start))) (bo g) k _=true at h
 rw [e] at h
 exact iL h
def ic (pos neg:Nat) (g:aM) (k i:Nat) (kw panels:Nat→Nat) (tag:Nat):=
 if tag=0 then cL g k i else if tag<128 then
   np pos neg (bo g) (bT g k i) k (bE kw (32*(tag-1)) 32)
 else jf pos neg (bT g k i) (bo g) k (bE panels (68*(tag-128)) 68)
def jz (pos neg:Nat) (g:aM) (k start n:Nat) (kw panels:Nat→Nat) (data:Nat):=
 (List.range n).all fun j => ic pos neg g k (start+j) kw panels ((data >>> (8*j)) &&& 255)
lemma ac {pos neg g k start n kw panels data} (mode:g.mode=false)
   (h:jz pos neg g k start n kw panels data=true):ba g k start n:= by
 intro j lo hi
 have one:= List.all_eq_true.mp h (j-start) (List.mem_range.mpr (by omega))
 have eq:start+(j-start)=j:= by omega
 change ic pos neg g k (start+(j-start)) kw panels _=true at one
 rw [eq] at one
 unfold ic at one
 split at one
 · exact Or.inl one
 · right
   rw [mode]
   split at one
   · exact lh one
   · exact iL one
lemma aW {u} {g:aM} {m cap i:Nat} {prior:Nat → Nat} {ws:List Sig}
   (hm:g.mask=m) (hu:g.mode=u) (low: ∀ q,Lower u (varsX q) (au q) (prior q))
   (geom:aV g prior=true) (blocks:bS g cap)
   (idx:eh g cap i ws=true):az u (au m) cap ws.toFinset:= by
 subst hm
 subst hu
 exact ol low geom blocks (Nat.le_refl _) idx
lemma aG {g k start n} (arity rows depth:Nat)
   (proof:cells g k start n arity rows depth:= by
     simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
     repeat' apply And.intro
     all_goals decide +kernel):block g k start n = true:= bC proof
lemma aX {g:aM} {prior:Nat → Nat} (columns autos:Nat)
   (pos:(cU g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) = true:= by decide +kernel)
   (neg:(cU g.mask (fun j => (g.samples j).2) == 0) = true:= by decide +kernel)
   (col:cA (fun c => gm g.mask c prior) g.cols columns:= by
     simp only [cA]
     repeat' apply And.intro
     all_goals decide +kernel)
   (aut:cA (fun p => lU (bo g) (p.map cY)) g.autos autos:= by
     simp only [cA]
     repeat' apply And.intro
     all_goals decide +kernel):aV g prior = true:= by
 simp only [aV,Bool.and_eq_true]
 exact ⟨⟨⟨pos,neg⟩,df col⟩,df aut⟩
lemma af {u m q cap} (rows:List Nat)
   (plain:az u (au q) cap (vars q).toFinset)
   (mixed:az u (au q) cap (varsX m).toFinset)
   (essential:mE m rows = true:= by decide +kernel)
   (target:au m = au q:= by decide +kernel)
   (sources:vars m = vars q:= by decide +kernel):
   Lower u (varsX m) (au m) (cap+1):= pj essential target sources plain mixed
lemma aR {u m cap} {ws:List Sig} {es} (known:Known u es) (ci:aZ)
   (valid:gm m ci (aI es) = true:= by decide +kernel)
   (cut:(decide ws.Nodup && kz u (hQ ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (hO m ci)) ws) = true:= by decide +kernel):
   az u (au m) cap ws.toFinset:= tt (ag es known) ci valid cut
def w1:Array Nat:= #[
 0x2015947530075400,0x801264a130061400,0x6012142630021400,0x248a38642086430,0x6014142630021400,0x8214635a0030510,0x2016947530075400,
 0x250885a290083500,0x801264a130051300,0x801264a130050380,0x268a98675086750,0x2018b4a530085400,0x250885a290072480,0x6894b35842058430,
 0x8214635a0040610,0x32800865a2007610,0xa9462587b4032500,0xa502257890023500,0x2015947530064300,0x801264a130051400,0x850265a1900504a0,
 0x2018b4a530063280,0x1328a4b653086040,0x2045947530075400,0x801264a130041300,0x2018b4a130047160,0x2018b4a530074300,0x201a947530075400,
 0x32800865a2005480,0x65b2142630021400,0x6502152690021400,0x60b2142630021400,0x18202631a0028510,0x801264a130050390,0x892a36842068430,
 0xb624519420050210,0x9a5093b784057340,0xa230690a57016570,0x5890b39842058430,0x8257691a0068510,0x2015947530065400,0xb8262631a0032610,
 0x850265a190050490,0x862008a602042081,0x851264a130061400,0x6012142630021300,0x862008a602064011,0x2016947530064380,0x248a38642064210,
 0x801264a130049280,0xa230690a57005460,0x8257691a0072610,0x268a98675075640,0x80359a7b68064570,0x850265a190050480,0x250885a290069370,
 0x32800865a2007690,0x248a38642075320,0x250885a2900724a0,0x1628a1b620086210,0x85b264a130050380,0x6502152690021500,0x8214635a1040610,
 0x6012142630071300,0x201a947530069400,0x6014142630019300,0xba84519470050210,0x6308b08965063070,0x748a28674064170,0x35a27a2986016750,
 0x6308b08965074080,0x7b8106ab90046301,0x6502152690010390,0x2108b2a531074320,0x8214635a1040910,0x801364a130061400,0xa81413570040210,
 0x9102524b31005320,0x862008a6020640a1,0x2015947530064390,0x20169475300643a0,0x801264a130040280,0x205887a29107a620,0x248a38642079430,
 0x9a5093b784059340,0x5890b39842059430,0x628b1807a2001720,0x32800865a2008720,0x268a98675064530,0xa6020a827606a141,0x6894b35842047320,
 0x80359a7b68075680,0x206887a291083720,0x8244639a0038500,0x248a3b642086430,0x25b4945730057400,0x9230631a24016340,0x5a80b19870058210,
 0x43b60092163274655,0xba84519370025080,0xb64002b51056202,0x32800865a2004370,0x9a5093b784047230,0x7b44819a3067510,0x801264a130031200,
 0x6012142630071200,0x8214635a1080310,0x2051374291082570,0x621413520030710,0x851264a130041300,0x6512142630071300,0x8214635a0030410,
 0x8257691a0067510,0x6012142630081300,0x6012142630091200,0x201a947530058300,0x6b02152690021400,0x2015947530068400,0x6014142630019200,
 0x801264ab32027160,0x801264a130027160,0x32844b36a0015470,0x601bb48230048160,0x801264a130039170,0x801264a130020160,0x60b2142630021300,
 0x2016947530059400,0x2016947530065400,0x2016947530089400,0x628b1807a2001680,0x801264a130040270,0x80359a7b68042350,0x801264a130040870,
 0x253885a290059360,0xb624519420047100,0x801264a130080370,0x250885a290059260,0x2015947530053270,0x6a84b25670028070,0x63b40035069176825,
 0x630bb08965063090,0x64b0218a0017602,0x35a27a2986015640,0x35a27a2986015690,0x945759214050970,0x832008a602042081,0x628b1805a2017580,
 0x430b81a362057160,0x638006a82002451,0x32800865a2006580,0xba84519470047100,0xba84519370036100,0xba84519470049100,0x6a84b25a78036190,
 0x6012142630010380,0x268a98675068540,0x2814835a2040730,0x8351374892043620,0x9a5093b784056340,0x268a98675065840,0x2570945730048300,
 0x25b0945730058400,0x2570945730058400,0xb680519420050210,0xb684519420050210,0x628a18620068210,0x638006a85004681,0x95b264a190040870,
 0x85709ab768046570,0x2015947530085400,0xb426203741029010,0xb624519420040210,0x230881a562068120,0x2844865a2080630,0x810368a13b051370,
 0x8045947b35065400,0x8214635a1030410,0x2051374291032690,0x2018b4a53007a400,0x2051374291043720,0x8214635a1090510,0x2b40352490039400,
 0x2b10352490039400,0x6014142630021300,0x601414263001a300,0xa81413570030210,0x6014142630018300,0x6018b48530085400,0x9102524b31004210,
 0x8015947530064300,0x2015947530095400,0x8015947530095400,0x436b84a263061720,0x8200a6b50046a12,0x18202631a002a510,0x4986852a4b016730,
 0x801264a130040380,0x82b4631a0028400,0x80b264a130050390,0x2016947530064390,0x68b4b35842047320,0x25043542900324a0,0x250885a290079400,
 0x862008a602064191,0xa50225789001a390,0xa502257890012490,0x892a36b48057320,0x9a5093b784046230,0x8b40358490034500,0x892a36b48068430,
 0x896a36842068430,0x892a36b48057430,0x648b1807a2012830,0x9230631a24019340,0x892a36b48067430,0x9a6093b784059340,0x892a368420573a0,
 0x6018b48930074380,0x86a0027958016421,0x80359a7b68053460,0xa6020a8276069a41,0x26a0027950015391,0x6a84b25a78047290,0xa6020a827607a251,
 0x630bb08965063070,0x268a98675064590,0x205887a290061570,0x2308b0a562063070,0x832008a602064011,0x2308b1a56206a170,0x832008a6020641a1,
 0x628b1807a2019720,0x832008a602064091,0x628a18620075210,0x832008a602064191,0x638006a85004671,0x26a00279580153a1,0x26a0027958016421,
 0x6a84b25a78049120,0x8306907b650640a0,0xb8245693a0038400,0x32800865a20076a0,0x2015947530064380,0x80b264a130050380,0x892a36842057320,
 0x801a947b35075400,0x1368a4b653086040,0x8015947b35075400,0xb681519420050210,0x1328a4b653075830,0x250885a290068370,0x601bb48530074380,
 0x801364a130050380,0xb6040a8276083261,0x64b0218a0023812,0x2015947530064a00,0x2106927531064320,0x6890b35842047830,0xb9262637a1032610,
 0xb9452637a1032610,0x6012142630021900,0x6012142630021a00,0x90359a4b68084560,0xa9462587b4021380,0x95036ba198050470,0x5278006a84004671,
 0xa9462587b4019380,0x85b364a130050380,0x7b8006ab90046901,0xa9462587b4021480,0xa644639a0038500,0x7b8106ab90056401,0x6891b35842047320,
 0x2048b4a530085400,0x5628a18620076210,0x6512142630021400,0x8257692a0072610,0x8244635a0040610,0x8015947b30075400,0xb621519420050210,
 0x804a947530075400,0x5628a18620086210,0x4b8609b837058371,0x2054374291043720,0x80b264a130061400,0x2308b1a562079120,0x20b71ba576085213,
 0x7412079541054021,0x26ba98675078650,0x5a80b19870056210,0x62ba18620078210,0x2048b3a542065434,0xba635694a0050610,0x1a80813b70038210,
 0x2108b2a531085320,0x8b2a36842068430,0x862008a602086131,0x850265a190061500,0x18202631a0032610,0x9a6093b784057340,0x832008a602086131,
 0x26a0027958027531,0x90379a7b68075680,0x95046ba198061580,0x7b8006a830068311,0x7b8106ab90068511,0x85026ba098061580,0x86406b0a58016580,
 0x9260631a24016340,0x5896a36842068430,0x628a18620086210,0x59471b9867058123,0x76835894a3050834,0x4687b58294083506,0xa437528749032053,
 0x634ab48935085400]
def wX (codes i:Nat):Nat:=
 w1[(codes >>> (9*i)) &&& 511]?.getD 0
lemma aO {g k start n} (codes:Nat)
   (mode:g.mode = false:= by rfl)
   (proof:iJ f1 f0 g k start n (wX codes) = true:= by decide +kernel):
   ba g k start n:= ml mode proof
lemma cT {g k start n} (data:Nat)
   (mode:g.mode = false:= by rfl)
   (proof:sv f1 f0 g k start n (fun _ => data) = true:= by decide +kernel):
   ba g k start n:= e9 mode proof
def g0 (i:Nat):Nat:= 0xf
def g1:aC:= (1,0,1,0,0,0,0,g0)
def vS:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffffffffff3,0x62),(0xffffffffffffffffffffffffffffffffffffbf,0xffffffffffffffffffffffffffffffffffff99),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def vR:List aZ:= []
def tF:List (List Nat):= [[],[48,33]]
def x0:Nat → aC
 | 3 => g1
 | _ => bi
def tG:Nat → Nat → Option (Nat × Nat)
 | _ => fun _ => none
def fC:aM:= ⟨15,3,fun j => vS[j]?.getD (0,0),vR,tF,x0,tG⟩
set_option maxHeartbeats 0 in
lemma sS:aV fC (aI []) = true:= aX 0 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tA:block fC 3 0 1=true:=
 (by decide +kernel)
lemma x5:bP fC 3:= by
 intro k hk
 interval_cases k
 · exact (rfl:block fC 0 0 0 = true)
 · exact (rfl:block fC 1 0 0 = true)
 · exact (rfl:block fC 2 0 0 = true)
 · exact tA
def qC:Array (List Nat):= #[
 [],[101,66,16],[135,50,65],[133,117,101,33,48],[82,129,48],
 [50,65],[115,83,82,130,99,66,16],[130,50,81,115,98,65],[116,83,32],[113,97,82,32,65,48],
 [115,84,99],[128,64,116,81,96,49,32],[83,133,115,67,32,96],[128,16,64,100,80,113,33,48],[117,67,32],
 [135,101,50,33,16,64],[129,98,82,16,66,49,112],[133,117,16,64,49,32],[114,81,98,50,65],[83,114,99,33,16,64],
 [130,50,98,82,115,33,65],[128,100,49,112],[99,132,84,48,33,112],[129,82,97,48],[118,133,33,48],
 [116,100,83,32],[132,65,48,80,113,32],[67,80,100,131,112,32,16],[129,82,113,48],[130,114,98,81],
 [66,114,132,49,32,81,96],[50,117,131,49,32,65,96],[50,33,16,64],[114,33,97,82,50,65],[130,33,113,99,82,65],
 [130,33,50,113,99,82,16,64],[115,67,100,83],[131,115,65,50,98,81],[131,115,100,50,33,16,80],[117,101,67,32],
 [80,84,132,49,113,96],[117,80,66,96,16],[114,83,48,33,97,64],[129,33,97,81,16,114,49,64],[134,81,114,50,65],
 [64,132,49,96],[115,82,98,131,66,16],[98,118,81,130,50,65],[128,80,84,66,16,114,97,48],[132,116,84,48,33,96],
 [132,116,65,48,80,97,32],[66,114,50,132,99,32,80,16],[82,48],[84,115],[80,132,99,112,32,16],
 [131,67,99,116,50,33,16,80],[132,67,100,84,48,33,112],[130,50,97,115,82,16,64],[128,97,65,49,33,112],[129,80,48,50,114,97,64],
 [114,67,84,48,33,97,128],[66,16],[99,83,64,32,16],[115,50,98,83,66,16],[114,98,83,33,16,64],
 [130,114,98,49,32,81,64],[131,50,66,116,99,82],[130,50,116,49,32,97,80],[101,50,33,16,64],[83,82,114,99,66,16],
 [128,81,67,112,97,32],[83,80,132,115,96,32,16],[115,83,67],[101,117,50,33,16,64],[82,98,115,66,16],
 [128,80,117,32,16,98,65,48],[82,50,133,98,49,32,113,64],[49,50,83,48,130,113,64],[113,129,97,82,32,65,48],[99,81,115,130,65],
 [128,64,116,49,96],[131,84,115,98],[130,114,98,33,81],[82,133,99,49,32,65,112],[128,84,66,16,98,113,48],
 [131,65,50,114,81],[130,33,113,98,66,16,80],[128,80,81,67,96,113,32],[84,117,80,132,96,48,32,16],[118,130,81],
 [80,48,50,114,129,64],[100,131,82,16],[100,131,116,50,33,16,80],[33,80,112,97,130,49,64],[117,80,66,130,96,16],
 [84,131,98],[64,48,32,16],[80,64,48,32,16],[32,82,64,16],[96,80,64],
 [48,96,83,64,32,16],[115,99,83,67],[112,96,48,50,33,81,64],[114,50,99,48,33,81,64],[115,99,82,64,16],
 [115,96,83,64],[131,115,99,50,82,65],[131,115,50,98,83,66,16],[131,115,99,82,64,16],[130,114,49,98,81,64],
 [131,115,98,83,66],[131,115,98,83,32,64],[130,114,97,82,16,64],[130,50,115,98,49,32,81,64],[130,50,115,49,98,81,64],
 [48,128,115,96,50,33,81,64],[129,33,115,48,98,81,64],[32,50,128,115,98,81,64],[82,98,66,16],[131,67,116,99,82,16],
 [131,115,99,67,82,16],[128,112,96,49,64],[131,115,83,67,98],[129,113,82,65,48],[80,81,129,114,50,65,96],
 [81,33,80,128,97,114,49,64],[98,99,81,131,114,65],[48,84,100,49,129,112],[33,32,65,48],[16,64,49,32],
 [113,16,96,81,49,64],[129,113,33,98,81,48],[130,114,99,49,32,65,80],[129,113,98,16,66,49,80],[129,50,114,48,66,97,80],
 [129,116,50,97,80],[115,50,32,83,66,96,16],[112,48,50,33,97,64],[99,115,83,48,33,64],[83,80,96,115,64,32,16],
 [81,80,48,50,130,113,64],[117,101,33,32,65,48],[129,113,82,97,48],[129,33,114,82,16,66,49,96],[132,67,84,48,33,113,96],
 [128,16,113,65,49,33,96],[82,50,133,115,49,32,65,96],[81,80,128,113,98,49,64],[82,48,66,112],[83,114,64],
 [117,130,99,32,64,16],[116,100,49,81,32],[115,83,133,99,50,66,16],[84,100,49,128,113,32],[131,100,115,82,16],
 [134,117,33,32,65,48],[84,133,80,66,114,96,16],[82,48,66,129,112],[67,132,99,82,16],[117,99,49,32,65,128],
 [100,49,128],[118,101,133,50,33,16,64],[98,82,16,66,49,128],[84,66,16,98,129,48],[80,81,114,66,50,129,96],
 [116,50,129,80],[116,100,49,32,81,128]]
def aq (old:List (Nat × Nat)) (bound:Nat) (entries:List (Nat × Nat)):=
 l8 old bound (entries.map fun p => (p.1,qC[p.2]?.getD []))
def qH:= aq [] 4 [(15,0),(23,96),(27,61),(29,5),(30,32),(39,97),(57,98),(78,99),(83,62),(99,100),(135,101),(156,102),(163,63),(165,33),(166,64),(172,103),(177,104),(198,105),(281,106),(291,107),(300,65),(305,108),(312,109),(323,110),(326,111),(330,112),(332,113),(344,114),(353,34),(354,35),(396,115),(424,116),(480,117)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma uF:Known true qH:= aw (m:=15) oo
   (cu (hints:=8449) (by decide +kernel) (ed (g:=fC) (i:=0) rfl rfl (ag [] oo) sS x5 (by decide +kernel))) (by decide +kernel)
def g4 (i:Nat):Nat:= 0x11a20bf
def g9:aC:= (1,0,3,0,0,0,0,g4)
def g6 (i:Nat):Nat:= 0x30be670208000065000016357504004755c084
def g3 (i:Nat):Nat:= 0x40828fd20fd10
def g8:aC:= (2,1,3,0,0,3,0,g3)
def g5 (i:Nat):Nat:= 0x300
def g2 (i:Nat):Nat:= 0x5dd4520
def g7:aC:= (1,2,3,0,0,0,0,g2)
def vX:Array (Bits × Bits):= #[(0x2e44,0x2c52),(0x5a8a,0x5208),(0xffffffffffffffffffffffffffffffffffb4f7,0xffffffffffffffffffffffffffffffffffa0c7),(0xffffffffffffffffffffffffffffffffffcf79,0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def vW:List aZ:= [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def wH:List (List Nat):= [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x3:Nat → aC
 | 6 => g9
 | 5 => g8
 | 4 => g7
 | _ => bi
def tH:Nat → Nat → Option (Nat × Nat)
 | 6 => aL 5 15 3 9 1 4 g6
 | 5 => aL 1 3 1 9 1 4 g5
 | _ => fun _ => none
def sF:aM:= ⟨31,6,fun j => vX[j]?.getD (0,0),vW,wH,x3,tH⟩
set_option maxHeartbeats 0 in
lemma sT:aV sF (aI qH) = true:= aX 0 1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tD:block sF 6 0 1=true:=
 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tC:block sF 5 0 2=true:=
 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tB:block sF 4 0 1=true:=
 (by decide +kernel)
lemma x6:bP sF 6:= by
 intro k hk
 interval_cases k
 · exact (rfl:block sF 0 0 0 = true)
 · exact (rfl:block sF 1 0 0 = true)
 · exact (rfl:block sF 2 0 0 = true)
 · exact (rfl:block sF 3 0 0 = true)
 · exact tB
 · exact tC
 · exact tD
def u5:= aq qH 7 [(31,0),(167,36),(313,37),(334,38),(355,66),(428,67)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma uG:Known true u5:= aw (m:=31) uF
   (cu (hints:=8449) (by decide +kernel) (ed (g:=sF) (i:=0) rfl rfl (ag qH uF) sT x6 (by decide +kernel))) (by decide +kernel)
def u6:= aq u5 5 [(61,5),(91,1),(94,68),(181,18),(227,69),(230,19)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma uH:Known true u6:= aw (m:=47) uG
   (cu (hints:=8449) (by decide +kernel) (aR uG (8,0,39,0,4))) (by decide +kernel)
def u7:= aq u6 5 [(55,0),(59,5),(103,118)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma uI:Known true u7:= aw (m:=55) uH
   (cu (hints:=257) (by decide +kernel) (aR uH (16,0,39,0,4))) (by decide +kernel)
def qI:= aq u7 8 [(63,0),(95,1),(159,39),(359,119),(377,70),(462,12),(483,71),(492,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma uJ:Known true qI:= aw (m:=63) uI
   (cu (hints:=8449) (by decide +kernel) (aR uI (32,0,31,0,7))) (by decide +kernel)
def f8 (i:Nat):Nat:= 0x7213f
def fB:aC:= (1,0,2,0,0,0,0,f8)
def f9 (i:Nat):Nat:= 0x8000
def f7 (i:Nat):Nat:= 0x17e51
def fA:aC:= (1,1,2,0,0,0,0,f7)
def wC:Array (Bits × Bits):= #[(0xffffffffffffffffffffffffffffffffffed93,0x2d12),(0xffffffffffffffffffffffffffffffffff9467,0xffffffffffffffffffffffffffffffffff9025),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]
def wB:List aZ:= [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def uY:List (List Nat):= [[],[32,83]]
def vQ:Nat → aC
 | 6 => fB
 | 5 => fA
 | _ => bi
def uZ:Nat → Nat → Option (Nat × Nat)
 | 6 => aL 1 3 1 6 1 1 f9
 | _ => fun _ => none
def j9:aM:= ⟨111,6,fun j => wC[j]?.getD (0,0),wB,uY,vQ,uZ⟩
set_option maxHeartbeats 0 in
lemma tI:aV j9 (aI qI) = true:= aX 0 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uN:block j9 6 0 1=true:=
 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uM:block j9 5 0 1=true:=
 (by decide +kernel)
lemma y1:bP j9 6:= by
 intro k hk
 interval_cases k
 · exact (rfl:block j9 0 0 0 = true)
 · exact (rfl:block j9 1 0 0 = true)
 · exact (rfl:block j9 2 0 0 = true)
 · exact (rfl:block j9 3 0 0 = true)
 · exact (rfl:block j9 4 0 0 = true)
 · exact uM
 · exact uN
def q9:= aq qI 7 [(111,0),(123,1),(187,41),(190,42),(215,72),(222,73),(238,19),(243,74),(311,120),(318,121),(343,122),(349,75),(365,123),(378,43),(437,44),(455,12),(476,76),(485,124),(490,125),(497,126),(504,77)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma v0:Known true q9:= aw (m:=111) uJ
   (cu (hints:=16785665) (by decide +kernel) (ed (g:=j9) (i:=0) rfl rfl (ag qI uJ) tI y1 (by decide +kernel))) (by decide +kernel)
def fF (i:Nat):Nat:= 0x163441bf
def fK:aC:= (1,0,3,0,0,0,0,fF)
def fH (i:Nat):Nat:= 0x42f9f28c08140000000020f801630c00d0
def fE (i:Nat):Nat:= 0x420a3fa41fd10
def fJ:aC:= (2,1,3,0,0,3,0,fE)
def fG (i:Nat):Nat:= 0x18000
def fD (i:Nat):Nat:= 0xb7d8d20
def fI:aC:= (1,2,3,0,0,0,0,fD)
def wE:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffffff55417,0xfffffffffffffffffffffffffffffffff46453),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffc60f7,0x44076),(0xfffffffffffffffffffffffffffffffff0bbcb,0xfffffffffffffffffffffffffffffffff03a89),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]
def wD:List aZ:= [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def jA:List (List Nat):= [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def vT:Nat → aC
 | 7 => fK
 | 6 => fJ
 | 5 => fI
 | _ => bi
def x1:Nat → Nat → Option (Nat × Nat)
 | 7 => aL 9 13 2 9 1 4 fH
 | 6 => aL 1 3 1 9 1 4 fG
 | _ => fun _ => none
def qJ:aM:= ⟨189,7,fun j => wE[j]?.getD (0,0),wD,jA,vT,x1⟩
set_option maxHeartbeats 0 in
lemma tJ:aV qJ (aI q9) = true:= aX 1 2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uQ:block qJ 7 0 1=true:=
 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uP:block qJ 6 0 2=true:=
 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uO:block qJ 5 0 1=true:=
 (by decide +kernel)
lemma y2:bP qJ 7:= by
 intro k hk
 interval_cases k
 · exact (rfl:block qJ 0 0 0 = true)
 · exact (rfl:block qJ 1 0 0 = true)
 · exact (rfl:block qJ 2 0 0 = true)
 · exact (rfl:block qJ 3 0 0 = true)
 · exact (rfl:block qJ 4 0 0 = true)
 · exact uO
 · exact uP
 · exact uQ
def wL:= aq q9 8 [(189,0),(303,2),(347,20),(486,6)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma v2:Known true wL:= aw (m:=189) v0
   (cu (hints:=536879876) (by decide +kernel) (ed (g:=qJ) (i:=0) rfl rfl (ag q9 v0) tJ y2 (by decide +kernel))) (by decide +kernel)
def qA:= aq wL 9 [(127,0),(382,21),(478,22),(508,127)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma v1:Known true qA:= aw (m:=127) v2
   (cu (hints:=16785665) (by decide +kernel) (aR v2 (32,0,95,0,8))) (by decide +kernel)
def sG (i:Nat):Nat:= 0x8201ff
def sI:aC:= (1,0,5,0,0,0,0,sG)
def sH (i:Nat):Nat:= 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def fO (i:Nat):Nat:= 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def fV:aC:= (12,1,5,0,0,10,0,fO)
def fR (i:Nat):Nat:= 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def fN (j:Nat):Nat:= 0x1f80354899e077b024a9159a24b911ac077e0465c892708574212ef090d670221e053c214e043b8235cc808a67d091c046f022c0a32623f7049522d15433a6477b08ce033e84719314e04222c097484381b79046f2083ea431f521b80ae446e02b90c91ffb0022ff500273ff780227d009160ad1a2b008a388648213e1129ec123701bbc02b6031f108e812788527a1372fef00a370177821af58220f98488d80ed11b79e031029f81224fe00116e08ea457911b013808784866ffa009e7c49103fc0098ee0495c8319f848269f5444bf2292df046e02b7ba00a2fc6c027b211cfe48667a04ad80ec912592247ef00ae68147aaa443fce6009d00860143e0495227c608ef0062ec24c9e99123806bc62448287a25ec8251c78110a11258898fc215345209610e8c3700843000414019102020c60a121c5c5ec5844fc4543ec3542cc25c1bc12409bfebf43e8be1bd8bcf3c73b9bae3a7b9eb9838f383b7d373369b6035934fb46b3ab3432bb24b1b311b072fcaf62edae72dc2ce2bf2b02a2294a8da83a7ca70a66a5ea54a4d24423c233a2aa192102069fa9ed9e61de9d29cd1c09b21aa1a399a99498e18397416815a14f94493712b11e91590f1000f10e88dd8d18ca0c08b70ab8a209508407d87606b86505b85104203883182501880d00042a470a82c2e250b1c428051315c2a4b0980c2c730b01c220f0b9942c37098142e430883428431b894240f098cc2a090881424370b12c240d090ac4e43090cc6e650994426530b0d44651090d4242f0b98c2a490b0242c570b1542c490b02c2408c3891ae246b94ba4107b92b6e24e8849aeb66b881ee82a983aa6486b951ae707b831ae0c6bad364307b893a2047b92324287b8ba6e867bb19ae0e6bb51ee2a7b909ae2c6ba49aed66b9c9ae607b8b1ee088a159ae50e9811ee4ea9821eea8c98c2a60c6b921ae086b8b9ee467bb29ee62e9849ae346b8d9ee647baa9ee0e6b993a4146b8caa64e6ba41eea67b89b2a286b959ae4e7bb216e242b9c86e87ffff7f7efefbfdf6ef6f902308821058d53501314c12044020
def fU:aC:= (113,2,5,589836,68,12,1057,fN)
def fQ (i:Nat):Nat:= 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def fM (i:Nat):Nat:= 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def fT:aC:= (116,3,5,0,0,11,0,fM)
def fP (i:Nat):Nat:= 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def fL (i:Nat):Nat:= 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def fS:aC:= (12,4,5,0,0,6,0,fL)
def wG:Array (Bits × Bits):= #[(0xfffffffffffffffda8e81df4649a4aea03f353,0x1a8209cc44085084a802052),(0xfffffffffffffffe550627bdd1589ea381610f,0xfffffffffffffffe550c023b884896b1415109),(0xb876f0435535c500a8ea8c,0x2872300045166108a00a84),(0x2669d0fd182653b341a80c0,0x2428c0bdd82211a84129140),(0x1554172223bd2f53d4f48e0,0x15416022395ae5314d4aa0),(0x253ba08288d622045549630,0x2509e022805626105509220),(0x0,0x0),(0x38f01c59fba0814d3746c20,0x18701c597ba0892d2056500),(0x0,0x0)]
def wF:List aZ:= ew 32 (fun x => (aU x 0 8,aU x 8 8,aU x 16 8,aU x 24 4,aU x 28 4)) 21 0x401700a840a6001940270098401d00a24039008640a5001a40870038409c002340b1000e40a3081440a61009401e208150370088401b802470be000170bb000469a6100040ac001380bd000270a70018701f00a0
def qE:List (List Nat):= [[],[115,84],[32,67,117],[32,83,116]]
def vV:Nat → aC
 | 10 => sI
 | 9 => fV
 | 8 => fU
 | 7 => fT
 | 6 => fS
 | _ => bi
def x2:Nat → Nat → Option (Nat × Nat)
 | 10 => aL 16 41 5 10 4 2 sH
 | 9 => aL 67 277 6 13 7 2 fR
 | 8 => aL 100 251 6 13 7 2 fQ
 | 7 => aL 4 19 2 10 4 2 fP
 | _ => fun _ => none
def zX:aM:= ⟨191,10,fun j => wG[j]?.getD (0,0),wF,qE,vV,x2⟩
set_option maxHeartbeats 0 in
lemma tK:aV zX (aI qA) = true:= aX 3 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma vM:block zX 10 0 1=true:=
 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uU:block zX 9 0 12=true:=
 (aG 8 0 2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uT:block zX 8 0 113=true:=
 (@aT zX 8 0 106 7 (@aT zX 8 0 70 36 (@aT zX 8 0 39 31 (@aT zX 8 0 3 36
 (by decide +kernel)
 (aG 8 0 3))
 (aG 8 0 3))
 (aG 9 0 3))
 (aG 9 0 1))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uS:block zX 7 0 116=true:=
 (@aT zX 7 0 85 31 (@aT zX 7 0 49 36 (@aT zX 7 0 13 36
 (aG 7 0 2)
 (aG 8 0 3))
 (aG 8 0 3))
 (aG 8 0 3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uR:block zX 6 0 12=true:=
 (aG 7 0 2)
lemma y3:bP zX 10:= by
 intro k hk
 interval_cases k
 · exact (rfl:block zX 0 0 0 = true)
 · exact (rfl:block zX 1 0 0 = true)
 · exact (rfl:block zX 2 0 0 = true)
 · exact (rfl:block zX 3 0 0 = true)
 · exact (rfl:block zX 4 0 0 = true)
 · exact (rfl:block zX 5 0 0 = true)
 · exact uR
 · exact uS
 · exact uT
 · exact uU
 · exact vM
def wM:= aq qA 11 [(191,0),(319,2),(351,3),(367,13),(379,7),(431,78),(445,23),(487,6),(494,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma v3:Known true wM:= aw (m:=191) v1
   (cu (hints:=536879361) (by decide +kernel) (ed (g:=zX) (i:=0) rfl rfl (ag qA v1) tK y3 (by decide +kernel))) (by decide +kernel)
def wN:= aq wM 8 [(251,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma v4:Known true wN:= aw (m:=251) v3
   (cu (hints:=1358970881) (by decide +kernel) (aR v3 (128,0,123,0,7))) (by decide +kernel)
def qB:= aq wN 12 [(255,0),(479,24),(503,46),(507,79),(509,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma v5:Known true qB:= aw (m:=255) v4
   (cu (hints:=553656577) (by decide +kernel) (aR v4 (64,0,191,0,11))) (by decide +kernel)
def sL (i:Nat):Nat:= 0x1840804ff
def sR:aC:= (1,0,6,0,0,0,0,sL)
def sO (i:Nat):Nat:= 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def sK (i:Nat):Nat:= 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def sQ:aC:= (6,1,6,0,0,9,0,sK)
def sN (i:Nat):Nat:= 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def sJ (j:Nat):Nat:= 0x2ff45022545810b0ebed2a0a0caa9a4a646170118bba1216fab28127d3e208a4fd3025756808373fd0139d909a4f77fc6205153e0263c3e095f7f520157b044d77c804c7e9c8080acf700959fa41af7f15139e7a243e4b049e3e72549ef82c4149a9b213cd771046be348414dff0820a1d72484df882050f8046fdd00eb5019eb3818801d311052ae460a7bcd01029a02900f738439afc1100200b730408c90182a2e28830c2c20863024850e8b0a261b081c11808f861e128c0d842217820e140a0933257c918e31461a4187eaf6de1ba2708d81a3b2d618bd16c2b1532a053124b45a834f71d2366648b895627049c860f91c23445d09f1081b43084b06209c0e800eb8beb9aeb83eb98e398eb9cf41aeb8df389e982e39ce41af982fc0bf40bf38de98ce98df39cf18dec0beb89e389fc1af98cec1ae40bfb8dbc23cb858c1a8c0d8c188c1d8c0c8c098c3dcb839c0b8c1c9c1a54180c316c156c104c183c23ffffefbeffbeef7bbebf8c2104c1100c010
def sP:aC:= (47,2,6,524294,51,11,1060,sJ)
def sM (i:Nat):Nat:= 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def fY (j:Nat):Nat:= (if j<1 then 0x90c4083f321d6cc55f504646019c44204dfc10cf28937f0432053910ce223b02400980bbc34c65818045e5f095406f016f31822b00f789912c221f5c0114f24249ce0e08c5fc120656c06b2083990d70859f22264171411812e90b633045ad93564ac98ac1927756b1df4473c74045ae40c7bc4213fdaa08c1dec4c97b82425ed04f3d690c2f0864391ec72208d390a7d7c922807c0191010fa1911e02bfb8240e4c43990d011c06bd692267e463b811dee091ec041cc873e3c9046de215e623de216f1097a08640ab2623f9804abea9226f20245bf630932fde02207c2399086b88877f60496e239ac50c021f5491180a7108bc843247a20643ec231f50022efe0c114fda0958225a38918c18c308840c70fd088c0683056b01e8ec1e8cc2c288d0b416286c21c0109148e1a828738784a282029c20384833040b05c2684e0814120e020441e0b05549d41d33d27d1c513d084fe4f74f14e5cdecd84d14ca4c34bccb4cab49f497c8747fc77c70c66c60c57c51442437c2fc26c1ec1440dc02bf9beb3e4bddbd73cc3c23b73b1ba83a139739238c37fb78b73b6635fb58b4ab44338331322317307af72efae7ade2d5ac72bcab6aae2a129328a280a74a6ba5d251a49237a29a1f211a061fb9f29e39dc1cc9be1b89ac1a519918f98618097996c96115894e14513b92b1229191109080fd8f80ef0e18d48c70b88aa8a109788d88187906e06905c05604e04083302901a80c00049718e4c0b36e11290e6d2997424c0b9261cf970e52b97315cb95261d8532e4ab97614cb9ca65cf532e6a997744cc1735c271330008982c5cc02266041130937948c5c8c8266017b0528b970cfc91846550c2628b983612c82e3e58513308c2711a9cabe265d58302aba833c4cc325e51382e23159451dc19c266176322389989d3c83c2e5cc7ce6137946d3c830e65c3372688b976da48ace60cf232a4259095ec14c2662673060a5900054c162a612172f0bd97886cb3afa462c1268bd9189c4b86f5cc2173103d8201fb9848644e7b050369159bc8acde1134322bd78445bc222c61857b271159411bc2251e61f1f2d03d829e140aac6188772e19f924dcc19226608830280998704cb8c2e6194b213c5837e0c0bc2e5c62f2853784553c8182661d7306eb784512c83aca4477f2460998808ca9a4654e3f24c3a970dec13d8cc513f24f0b9815f4bc574c555b0f009973ddc194de1106b22b0998943c9180e51b07291ff6febfbff77deefdbff7f6fddf7bdf77ebfcff7feff5fdbf77def7ddfb7f3fe7dcefdc6309c6308c63061e3060e3060a30606305c6305c2304c630cc6109ce1060e10606105ce104c6101ce10e1130e0530a0530605305c5305c13020530e0d10cc110a0d1060d105cd104c11020d109c43061830604305c4301c43060c10608105cc101cc10 else 0x23fc480cb7845bfa208a1e04c73d81137085d8158ef1090e22602dc5c887112c08e223888e2258134029f023bd8325d2859f446065d28576447019d81200235c08603afc001907c8877046f6022e212f4)
def k3:aC:= (136,3,6,1638440,86,12,1083,fY)
def k0 (i:Nat):Nat:= 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def fX (i:Nat):Nat:= 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def k2:aC:= (53,4,6,0,0,9,0,fX)
def fZ (i:Nat):Nat:= 0x834601a000
def fW (i:Nat):Nat:= 0xa295fdb2e3ca3070852bfb65c79460e30
def k1:aC:= (2,5,6,0,0,3,0,fW)
def wJ:Array (Bits × Bits):= #[(0xffffffffffffffd8fd630dda8e8aa61c90014d,0xffffffffffffffd8d42304082801a102900145),(0x2762dfc636db2d3474067090,0x2120d82a34960818c4045090),(0x3ec100918c681557416c0816,0x1ec100818829154701680800),(0x19cee55353e34c9ba0a86e6,0xeea5424062a80ba0284c6),(0x3721940b48c0c06e80091ef8,0x2721140b40c0c04e00091a38),(0x30e98f28487160298718700,0x30a98f08487160298418600),(0xffffffffffffffcace0a51892172a62383f801,0xace02d1892132a62281a800),(0x0,0x0),(0xfffffffffffffffc3135226350618b47fd9801,0xfffffffffffffff43105024250c159053c1001)]
def wI:List aZ:= ew 27 (fun x => (aU x 0 9,([0,8,2,1,256,32,64,4,16]:List Nat).getD (aU x 9 4) 0,aU x 13 9,([0,48]:List Nat).getD (aU x 22 1) 0,aU x 23 4)) 38 0x10270ac42b602445300668b0b869146814a09cb1175b4024a1b8521d37024203ad2284bc0a082704c5131725383e16040e5a0c80f2d05d7a002a2c401d414c2588ac009d0174343a7c0414530c648a300e5b4c30138f610444e088a8318c5112c029bac601c859c03123f8401d390233a9c031b5bc0216bd8012d3f0205abe020
def jB:List (List Nat):= [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def vY:Nat → aC
 | 12 => sR
 | 11 => sQ
 | 10 => sP
 | 9 => k3
 | 8 => k2
 | 7 => k1
 | _ => bi
def x4:Nat → Nat → Option (Nat × Nat)
 | 12 => aL 8 37 4 10 3 3 sO
 | 11 => aL 48 123 4 13 6 3 sN
 | 10 => aL 79 299 8 15 8 3 sM
 | 9 => aL 39 99 5 13 6 3 k0
 | 8 => aL 1 5 1 8 1 3 fZ
 | _ => fun _ => none
def zV:aM:= ⟨383,12,fun j => wJ[j]?.getD (0,0),wI,jB,vY,x4⟩
set_option maxHeartbeats 0 in
lemma tL:aV zV (aI qB) = true:= aX 3 1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma vP:block zV 12 0 1=true:=
 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma vO:block zV 11 0 6=true:=
 (aG 9 0 1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma vN:block zV 10 0 47=true:=
 (@aT zV 10 0 19 28 (@aT zV 10 0 6 13
 (aG 8 0 1)
 (aG 9 0 2))
 (aG 10 0 3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uX:block zV 9 0 136=true:=
 (@aT zV 9 0 119 17 (@aT zV 9 0 111 8 (@aT zV 9 0 75 36 (@aT zV 9 0 39 36 (@aT zV 9 0 3 36
 (by decide +kernel)
 (aG 9 0 3))
 (aG 9 0 3))
 (aG 9 0 3))
 (aG 9 0 1))
 (aG 10 0 2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uW:block zV 8 0 53=true:=
 (@aT zV 8 0 44 9 (@aT zV 8 0 36 8
 (aG 8 0 3)
 (aG 8 0 1))
 (aG 9 0 1))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma uV:block zV 7 0 2=true:=
 (by decide +kernel)
lemma y4:bP zV 12:= by
 intro k hk
 interval_cases k
 · exact (rfl:block zV 0 0 0 = true)
 · exact (rfl:block zV 1 0 0 = true)
 · exact (rfl:block zV 2 0 0 = true)
 · exact (rfl:block zV 3 0 0 = true)
 · exact (rfl:block zV 4 0 0 = true)
 · exact (rfl:block zV 5 0 0 = true)
 · exact (rfl:block zV 6 0 0 = true)
 · exact uV
 · exact uW
 · exact uX
 · exact vN
 · exact vO
 · exact vP
def zT:= aq qB 13 [(383,0),(447,47),(495,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma s1:Known true zT:= aw (m:=383) v5
   (cu (hints:=12901687553) (by decide +kernel) (ed (g:=zV) (i:=0) rfl rfl (ag qB v5) tL y4 (by decide +kernel))) (by decide +kernel)
lemma oH:Known false zT:= pX s1
def gT (i:Nat):Nat:= 0x1a230180fd10fc20
def gW:aC:= (2,1,2,0,0,4,0,gT)
def gU (i:Nat):Nat:= 0x104451000a0200202082101c0c0071400
def gS (i:Nat):Nat:= 0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def gV:aC:= (5,2,2,0,0,5,0,gS)
def yZ:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffffffffc47,0xa86),(0xfffffffffffffffffffffffffffffffffff09b,0xfffffffffffffffffffffffffffffffffff531),(0x29c,0x8cc),(0xfffffffffffffffffffffffffffffffffff327,0xfffffffffffffffffffffffffffffffffff303),(0xd78,0x478),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def yY:List aZ:= [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def s4:List (List Nat):= wH
def t3:Nat → aC
 | 6 => gW
 | 5 => gV
 | _ => bi
def s5:Nat → Nat → Option (Nat × Nat)
 | 6 => aL 8 11 1 11 3 4 gU
 | _ => fun _ => none
def s3:aM:= ⟨1055,6,fun j => yZ[j]?.getD (0,0),yY,s4,t3,s5⟩
set_option maxHeartbeats 0 in
lemma u3:aV s3 (aI zT) = true:= aX 0 1
def nK:Nat:= 0x110c0300c03
def nJ:Nat:= 0x14090281205
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sV:ba s3 6 0 2:=
 (aH (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sU:ba s3 5 0 5:=
 (e9 (pos:=nK) (neg:=nJ) (data:=fun _ => 0x4224033220301121141340101413401031423232) rfl (by decide +kernel))
lemma jY:bS s3 6:= by
 intro k hk
 interval_cases k
 · exact as s3 0 0
 · exact as s3 1 0
 · exact as s3 2 0
 · exact as s3 3 0
 · exact as s3 4 0
 · exact sU
 · exact sV
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma gN:az false (au 1055) 6 (vars 1055).toFinset:= iB (q:=31) (prior:=aI zT) (ag zT oH) (by decide +kernel)
def jG:= aq zT 7 [(1567,0),(2079,5),(6687,32),(7199,61),(1703,36),(4263,33),(7847,63),(12455,9),(2361,37),(6990,38),(4963,34),(9571,35)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xB:Known false jG:= aw (m:=1567) oH
   (af (q:=1055) [2,1,2,4,1] gN
     (aW (g:=s3) (i:=0) rfl rfl (ag zT oH) u3 jY (by decide +kernel))) (by decide +kernel)
def zL:= aq jG 7 [(42527,0),(44063,5),(47647,32),(52767,128),(57887,129),(42663,36),(44711,33),(47783,64),(54951,9),(68775,130),(44345,37),(60217,131),(53070,132),(60238,133),(42851,66),(44899,34),(50019,35),(53164,67),(60332,134),(69548,135)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma q1:Known false zL:= aw (m:=42527) xB
   (af (q:=1055) [2,1,2,4,1] gN
     (aW (g:=s3) (i:=1) rfl rfl (ag zT oH) u3 jY (by decide +kernel))) (by decide +kernel)
def kD (i:Nat):Nat:= 0x1040a3fa21fd51
def kG:aC:= (2,1,1,0,0,3,0,kD)
def kE (i:Nat):Nat:= 0x40000
def kC (i:Nat):Nat:= 0x102de54110
def kF:aC:= (1,2,1,0,0,0,0,kC)
def v7:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffffffff9b5,0xe94),(0xfffffffffffffffffffffffffffffffffff0db,0xfffffffffffffffffffffffffffffffffff10b),(0x602,0xa80),(0x614,0x514),(0x0,0x0),(0x964,0x160),(0x78,0xef0),(0x0,0x0),(0x0,0x0)]
def v6:List aZ:= [(96,0,15,0,4),(1,32,78,0,4)]
def xR:List (List Nat):= [[],[32,83]]
def yS:Nat → aC
 | 6 => kG
 | 5 => kF
 | _ => bi
def xS:Nat → Nat → Option (Nat × Nat)
 | 6 => aL 1 3 1 6 1 1 kE
 | _ => fun _ => none
def j6:aM:= ⟨1135,6,fun j => v7[j]?.getD (0,0),v6,xR,yS,xS⟩
set_option maxHeartbeats 0 in
lemma wK:aV j6 (aI zL) = true:= aX 0 0
def f4:Nat:= 0x42108300c03
def f3:Nat:= 0x68321248a2a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tQ:ba j6 6 0 2:=
 (e9 (pos:=f4) (neg:=f3) (data:=fun _ => 0x2401212143203010) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tP:ba j6 5 0 1:=
 (e9 (pos:=f4) (neg:=f3) (data:=fun _ => 0x24012110) rfl (by decide +kernel))
lemma j4:bS j6 6:= by
 intro k hk
 interval_cases k
 · exact as j6 0 0
 · exact as j6 1 0
 · exact as j6 2 0
 · exact as j6 3 0
 · exact as j6 4 0
 · exact tP
 · exact tQ
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma f2:az false (au 1135) 6 (vars 1135).toFinset:= iB (q:=111) (prior:=aI zL) (ag zL q1) (by decide +kernel)
def qX:= aq zL 7 [(42683,41),(47806,42),(69498,43),(69557,44)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yL:Known false qX:= aw (m:=49775) q1
   (af (q:=1135) [2,64,2,4,1,2] f2
     (aW (g:=j6) (i:=0) rfl rfl (ag zL q1) wK j4 (by decide +kernel))) (by decide +kernel)
def zM:= aq qX 7 [(44155,62),(44219,136),(44731,41),(52926,42),(54974,137),(42711,72),(47838,73),(52958,138),(42739,74),(44787,139),(53054,65),(60253,75),(60282,43),(44981,44),(48071,12),(53212,76),(60408,77),(69624,140)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zC:Known false zM:= aw (m:=42607) yL
   (af (q:=1135) [2,1,2,4,1,2] f2
     (aW (g:=j6) (i:=1) rfl rfl (ag zL q1) wK j4 (by decide +kernel))) (by decide +kernel)
def n0 (i:Nat):Nat:= 0x344640ac3f865fc10
def n7:aC:= (2,1,2,0,0,4,0,n0)
def n3 (i:Nat):Nat:= 0x1520079d85d46b7171000680020c0000f391436008009b010
def gZ (i:Nat):Nat:= 0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def n6:aC:= (12,2,2,0,0,7,0,gZ)
def n2 (i:Nat):Nat:= 0x24f9400060ba8030352
def gY (i:Nat):Nat:= 0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def n5:aC:= (6,3,2,0,0,6,0,gY)
def n1 (i:Nat):Nat:= 0x20034000
def gX (i:Nat):Nat:= 0x3b04813058432
def n4:aC:= (1,4,2,0,0,0,0,gX)
def u2:Array (Bits × Bits):= #[(0xffffffffffffffffffffffffffffffffff209f,0xd8096),(0xfffffffffffffffffffffffffffffffff19c61,0xfffffffffffffffffffffffffffffffff03861),(0x97be,0x2c69c),(0xfffffffffffffffffffffffffffffffff04b47,0xfffffffffffffffffffffffffffffffffd3903),(0x44c78,0x24468),(0xa2f80,0x27f00),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def u1:List aZ:= [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def s6:List (List Nat):= [[],[65,50]]
def t6:Nat → aC
 | 7 => n7
 | 6 => n6
 | 5 => n5
 | 4 => n4
 | _ => bi
def s7:Nat → Nat → Option (Nat × Nat)
 | 7 => aL 7 21 2 9 4 1 n3
 | 6 => aL 2 9 1 8 3 1 n2
 | 5 => aL 1 5 1 6 1 1 n1
 | _ => fun _ => none
def t9:aM:= ⟨1087,7,fun j => u2[j]?.getD (0,0),u1,s6,t6,s7⟩
set_option maxHeartbeats 0 in
lemma u4:aV t9 (aI zM) = true:= aX 0 0
def uK (j:Nat):Nat:= 0x3514243035142420351320403142355431423232203411211512401013243543
def qD (j:Nat):Nat:= 0x3120043210043201024300234510350210243002345103402102430023451023051024300234010340210210341352003510002103413520030210
def rM:Nat:= 0x42110c0300c03
def rL:Nat:= 0x34190a81205
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma dT:ba t9 4 0 1:=
 (ac (pos:=rM) (neg:=rL) (kw:=uK) (panels:=qD) (data:=0x1) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma dU:ba t9 5 0 6:=
 (ac (pos:=rM) (neg:=rL) (kw:=uK) (panels:=qD) (data:=0x50008000607) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma dV:ba t9 6 0 12:=
 (ac (pos:=rM) (neg:=rL) (kw:=uK) (panels:=qD) (data:=0x803020482818600838580) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma dW:ba t9 7 0 2:=
 (ac (pos:=rM) (neg:=rL) (kw:=uK) (panels:=qD) (data:=0x84) rfl (by decide +kernel))
lemma jZ:bS t9 7:= by
 intro k hk
 interval_cases k
 · exact as t9 0 0
 · exact as t9 1 0
 · exact as t9 2 0
 · exact as t9 3 0
 · exact dT
 · exact dU
 · exact dV
 · exact dW
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma y0:az false (au 1087) 7 (vars 1087).toFinset:= iB (q:=63) (prior:=aI zM) (ag zM zC) (by decide +kernel)
def jT:= aq zM 8 [(2143,1),(2425,48)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xO:Known false jT:= aw (m:=6719) zC
   (af (q:=1087) [2,1,2,4,1,1] y0
     (aR zC (6688,0,6687,0,7))) (by decide +kernel)
def jC:= aq jT 8 [(1087,0),(2623,5),(1119,1),(6303,39),(11423,141),(6319,25),(13487,9),(1207,10),(3255,18),(1255,69),(18749,142),(11614,49),(18782,143),(18798,80),(1395,81),(18809,48),(11708,144),(3555,71)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma x7:Known false jC:= aw (m:=1087) xO
   (af (q:=1087) [16,4,2,4,1,1] y0
     (aW (g:=t9) (i:=0) rfl rfl (ag zM zC) u4 jZ (by decide +kernel))) (by decide +kernel)
def qK:= aq jC 8 [(2719,39),(13495,10),(3389,50),(8542,49)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma y8:Known false qK:= aw (m:=11327) x7
   (af (q:=1087) [2,1,2,16,1,1] y0
     (aW (g:=t9) (i:=1) rfl rfl (ag zM zC) u4 jZ (by decide +kernel))) (by decide +kernel)
def jH:= aq qK 8 [(1599,0),(12463,9),(1719,10),(2365,50),(9582,145),(4979,7)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xC:Known false jH:= aw (m:=1599) y8
   (af (q:=1087) [2,1,2,4,1,1] y0
     (aR zC (1568,0,1567,0,7))) (by decide +kernel)
def qW:= aq jH 8 [(47679,0),(44127,1),(52831,68),(42671,25),(68783,9),(47799,10),(68791,18),(44349,50),(60366,146)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yK:Known false qW:= aw (m:=47679) xC
   (af (q:=1087) [2,4,2,4,1,1] y0
     (aR zC (47648,0,47647,0,7))) (by decide +kernel)
def qO:= aq qW 8 [(42559,0),(42591,1),(47791,25),(54959,9),(42679,10),(44727,18),(60270,80),(60281,48),(69497,70),(48078,12),(69603,147)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yC:Known false qO:= aw (m:=42559) yK
   (af (q:=1087) [2,1,2,4,1,1] y0
     (aR zC (42528,0,42527,0,7))) (by decide +kernel)
def z9:= aq qO 8 [(44719,25),(54967,10),(60239,38),(50014,49)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zO:Known false z9:= aw (m:=52799) yC
   (af (q:=1087) [2,1,8,4,1,1] y0
     (aR zC (52768,0,52767,0,7))) (by decide +kernel)
def kO (i:Nat):Nat:= 0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def kT:aC:= (5,1,3,0,0,7,0,kO)
def kQ (i:Nat):Nat:= 0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def kN (i:Nat):Nat:= 0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def kS:aC:= (10,2,3,0,0,7,0,kN)
def kP (i:Nat):Nat:= 0x700009040000000000ddd0800002
def kM (i:Nat):Nat:= 0x104208141ba541620c36698ac4186f15058430
def kR:aC:= (3,3,3,0,0,5,0,kM)
def vB:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffffff1880f,0xfffffffffffffffffffffffffffffffffe600d),(0x0,0x0),(0xfffffffffffffffffffffffffffffffff2619f,0x2a10e),(0xfffffffffffffffffffffffffffffffff60271,0xfffffffffffffffffffffffffffffffffc5851),(0x507e6,0x187a2),(0x89c78,0x9870),(0x0,0x0),(0x87780,0xd4680),(0x0,0x0)]
def vA:List aZ:= [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def xV:List (List Nat):= jA
def yU:Nat → aC
 | 7 => kT
 | 6 => kS
 | 5 => kR
 | _ => bi
def xW:Nat → Nat → Option (Nat × Nat)
 | 7 => aL 23 29 4 12 4 4 kQ
 | 6 => aL 2 11 1 10 2 4 kP
 | _ => fun _ => none
def q4:aM:= ⟨1213,7,fun j => vB[j]?.getD (0,0),vA,xV,yU,xW⟩
set_option maxHeartbeats 0 in
lemma q2:aV q4 (aI z9) = true:= aX 1 2
def f6:Nat:= 0x1408410844300c
def f5:Nat:= 0x90448d05005
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tV:ba q4 7 0 5:=
 (aH (aG 7 0 0))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tU:ba q4 6 0 10:=
 (@ak q4 6 0 3 7
 (aH (by decide +kernel))
 (e9 (pos:=f6) (neg:=f5) (data:=fun _ => 0x25234363203201322034013214234010432405431423402114234021) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tT:ba q4 5 0 3:=
 (e9 (pos:=f6) (neg:=f5) (data:=fun _ => 0x242340404324053241324040) rfl (by decide +kernel))
lemma zW:bS q4 7:= by
 intro k hk
 interval_cases k
 · exact as q4 0 0
 · exact as q4 1 0
 · exact as q4 2 0
 · exact as q4 3 0
 · exact as q4 4 0
 · exact tT
 · exact tU
 · exact tV
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma wY:az false (au 1213) 7 (vars 1213).toFinset:= iB (q:=189) (prior:=aI z9) (ag z9 zO) (by decide +kernel)
def jM:= aq z9 8 [(2237,0),(18109,148),(2395,82),(12774,51)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xH:Known false jM:= aw (m:=2237) zO
   (af (q:=1213) [16,8,4,1,1,4] wY
     (aW (g:=q4) (i:=0) rfl rfl (ag z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def jI:= aq jM 8 [(1725,0),(17085,52)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xD:Known false jI:= aw (m:=1725) xH
   (af (q:=1213) [16,8,4,1,1,4] wY
     (aW (g:=q4) (i:=1) rfl rfl (ag z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def jQ:= aq jI 8 [(2749,0),(11453,14),(1371,20),(6630,6),(13798,51)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xL:Known false jQ:= aw (m:=2749) xD
   (af (q:=1213) [32,8,4,8,1,4] wY
     (aW (g:=q4) (i:=2) rfl rfl (ag z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def qQ:= aq jQ 8 [(43197,0),(58557,52),(64189,149),(43823,2),(46427,20),(48475,15),(49638,6),(55782,150)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yE:Known false qQ:= aw (m:=43197) xL
   (af (q:=1213) [20,9,4,1,1,4] wY
     (aW (g:=q4) (i:=3) rfl rfl (ag z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def zP:= aq qQ 8 [(44221,0),(44733,53),(52925,14),(54973,8),(58045,52),(60207,26),(42843,20),(44379,82),(58203,3),(48102,6),(55270,51),(69606,54)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma q8:Known false zP:= aw (m:=44221) yE
   (af (q:=1213) [16,8,4,1,1,4] wY
     (aW (g:=q4) (i:=4) rfl rfl (ag z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def d8 (i:Nat):Nat:= 0x60bfd31
def d9:aC:= (1,1,1,0,0,0,0,d8)
def vF:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffffffffc91,0xfffffffffffffffffffffffffffffffffffc01),(0xe,0x2ee),(0x0,0x0),(0x64,0x2a4),(0x72,0x152),(0xffffffffffffffffffffffffffffffffffff8d,0x1ac),(0x16,0x110),(0x318,0x250),(0x0,0x0)]
def vE:List aZ:= [(88,0,163,0,4),(8,0,243,0,7)]
def xZ:List (List Nat):= [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def yW:Nat → aC
 | 7 => d9
 | _ => bi
def t0:Nat → Nat → Option (Nat × Nat)
 | _ => fun _ => none
def j7:aM:= ⟨1275,7,fun j => vF[j]?.getD (0,0),vE,xZ,yW,t0⟩
set_option maxHeartbeats 0 in
lemma tN:aV j7 (aI zP) = true:= aX 0 1
def gR:Nat:= 0x14042108443003
def gQ:Nat:= 0x68325248a381a0642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tW:ba j7 7 0 1:=
 (e9 (pos:=gR) (neg:=gQ) (data:=fun _ => 0x50634340) rfl (by decide +kernel))
lemma y6:bS j7 7:= by
 intro k hk
 interval_cases k
 · exact as j7 0 0
 · exact as j7 1 0
 · exact as j7 2 0
 · exact as j7 3 0
 · exact as j7 4 0
 · exact as j7 5 0
 · exact as j7 6 0
 · exact tW
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma gM:az false (au 1275) 7 (vars 1275).toFinset:= iB (q:=251) (prior:=aI zP) (ag zP q8) (by decide +kernel)
def zR:= aq zP 8 [(59646,151),(43479,152),(55773,22),(46581,27),(58874,153)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zH:Known false zR:= aw (m:=48891) q8
   (af (q:=1275) [2,80,16,10,1,2,32] gM
     (aW (g:=j7) (i:=0) rfl rfl (ag zP q8) tN y6 (by decide +kernel))) (by decide +kernel)
def kI (i:Nat):Nat:= 0x1948817fd30
def kL:aC:= (1,1,3,0,0,0,0,kI)
def kJ (i:Nat):Nat:= 0x8e80
def kH (i:Nat):Nat:= 0x24c269243a037eb0261df54530
def kK:aC:= (2,2,3,0,0,5,0,kH)
def v9:Array (Bits × Bits):= #[(0xffffffffffffffffffffffffffffffffff22a7,0xffffffffffffffffffffffffffffffffffa027),(0xffffffffffffffffffffffffffffffffff4759,0x4258),(0x942e,0x8424),(0xffffffffffffffffffffffffffffffffff99d3,0xffffffffffffffffffffffffffffffffff3bd3),(0x81c,0x4408),(0x21a0,0x5f80),(0x41c0,0xbd80),(0x0,0x0),(0x0,0x0)]
def v8:List aZ:= [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def xT:List (List Nat):= [[],[16,66,101]]
def yT:Nat → aC
 | 8 => kL
 | 7 => kK
 | _ => bi
def xU:Nat → Nat → Option (Nat × Nat)
 | 8 => aL 1 3 1 6 1 1 kJ
 | _ => fun _ => none
def qG:aM:= ⟨1151,8,fun j => v9[j]?.getD (0,0),v8,xT,yT,xU⟩
set_option maxHeartbeats 0 in
lemma tM:aV qG (aI zR) = true:= aX 1 0
def gP:Nat:= 0x10842110c0300c03
def gO:Nat:= 0xe86824914642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tS:ba qG 8 0 1:=
 (aH (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tR:ba qG 7 0 2:=
 (e9 (pos:=gP) (neg:=gO) (data:=fun _ => 0x2615312126154121) rfl (by decide +kernel))
lemma y5:bS qG 8:= by
 intro k hk
 interval_cases k
 · exact as qG 0 0
 · exact as qG 1 0
 · exact as qG 2 0
 · exact as qG 3 0
 · exact as qG 4 0
 · exact as qG 5 0
 · exact as qG 6 0
 · exact tR
 · exact tS
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma jW:az false (au 1151) 8 (vars 1151).toFinset:= iB (q:=127) (prior:=aI zR) (ag zR zH) (by decide +kernel)
def jL:= aq zR 9 [(2429,28),(7038,16),(9598,21)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xG:Known false jL:= aw (m:=2175) zH
   (af (q:=1151) [2,1,2,4,1,1,2] jW
     (aR zH (2080,0,2143,0,8))) (by decide +kernel)
def jD:= aq jL 9 [(18814,16),(11742,83)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma x8:Known false jD:= aw (m:=1151) xG
   (af (q:=1151) [16,4,2,4,1,1,2] jW
     (aR zH (1056,0,1119,0,8))) (by decide +kernel)
def qY:= aq jD 9 [(44925,28),(50046,16)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yM:Known false qY:= aw (m:=52863) x8
   (af (q:=1151) [2,1,8,4,1,1,2] jW
     (aR zH (52768,0,52831,0,8))) (by decide +kernel)
def qT:= aq qY 9 [(44159,0),(47743,1),(69501,84),(74110,21),(48094,83)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yH:Known false qT:= aw (m:=44159) yM
   (af (q:=1151) [16,1,2,4,1,1,2] jW
     (aR zH (44064,0,44127,0,8))) (by decide +kernel)
def qR:= aq qT 9 [(43647,0),(46455,81),(51063,154),(43901,28),(46461,84),(48510,16),(51070,21),(43423,155),(58811,156),(59900,157)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yF:Known false qR:= aw (m:=43647) yH
   (af (q:=1151) [10,1,2,5,1,1,2] jW
     (aW (g:=qG) (i:=0) rfl rfl (ag zR zH) tM y5 (by decide +kernel))) (by decide +kernel)
def z3:= aq qR 9 [(42623,0),(60285,28),(60286,16)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma z4:Known false z3:= aw (m:=42623) yF
   (af (q:=1151) [2,1,2,4,1,1,2] jW
     (aR zH (42528,0,42591,0,8))) (by decide +kernel)
def sW (i:Nat):Nat:= 0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def sY:aC:= (10,1,7,0,0,9,0,sW)
def sX (i:Nat):Nat:= 0xa49b3289cfee0003c11e62e10c1e4000235000513996000090c91cf0a000013a78dac3f26c00039c5cb8000000000204a000000452c001633e0e551fc80b152f0f95a89a255e23881a8be81b938018248c665c070000000000b3bc9a800000031700028c3072b06ecfafc98375010470c01e16716e074d6b0bf948ee3ac9600036e0054814054a5d5892c4d40b354401d8907a8d086167486866b2610135be1dd11650170cee09f0f01bcb5800000010d202243f318eef1419c646e0a9a0079430db52928c52c5193c564cb39a6900028ec0012280375062865214c24898f806a2a5df5d43e1d42ba11a4fe586827629805dd992be81c8003761a6d0ec800000000072b8000c8986beae00000018581727cae660c1200068bc0011c561f0148000b8c0000001cb4c5e711000138985d121316f8741ed000000000000000009074020000004d29b7e000c0d671818d8a3e1049165c75b693b0000000c7511c313d41fc131606bb107a0d043607013300102070000030000000461000006da150300000025000000000210610700003013010000000a0020130090060020020100100240030000015000100100020072001010001104000000010000400000000001011
def kY (j:Nat):Nat:= (if j<1 then 0x4670b12533d10c75e8c8b58478714c78518d7ffe317a00012a9ac91478d191b210c32553e54c93f89481224ccae8c8db6fde254791fe4e848fbc887bfd7bf91489036fde2547dcf8012e849566e24b9fb14c8811a0e059e352b5153447cbd4232d7f49221033d272641407a231b409789c248c37effc18880013340f091678851c118ebe79ab9993d531d8dc499a05bd0c116be4b20866cfc8181973f508195bdbb50994f7c60a504f0c8428b9e9121c0ac4fc46a1120e04a60f4453fb885004944e5f860055bc6ff42c4127799d428024a1e7ce7ac1704adc7e20451ffc4244651f5f0228486f4f0a1954c1e8977ea4a053be12443c9c3c6580589afe03afe94c94489efffa830090fdb8d0417f449000ce5f928a32dffc2d0614d27f807b0a67cf1f4d91f647d4208fbfe3700101096bf0781268499f1f02000903ffe01040482fca44652ffe289a4fc122aff8d4941804bdf23604101297c7e2140124af7ee811a7f861011d78f7002c80953e381127d8e0211e7f299142fbf18650920df8cb8019cf270f30e0547938798702a5ebf9031120250f9f5818890128f270f30e05400fe351d6404a258208d1b924507a3c1d8e86f1d841349848218d86b128212494478f110820c0a8e62006815047c230948a42161f9088a0318c9c0a1707c9404221c0c881288b0503b15130a240108fc04381b1a0844030838cc0801088b84e07148944900150b4582b1787c010b2846416a08101e7fcbfa1f92fab7c5bddde64f0b778bb55d82e9e73db929c58e0c6f43739b5ad886b9b591a7ed1d68533b5996cb263d319988cc2b606af8d78aba05bcad9566ab10570ab25534a8d52fa8ed41e9ef4eba72935296e4a92505254906477a3591928ae444219908c8224009f80f6c78e3c09da0e727113711ad0d0066031e1840bdc5d52d89660ad254f29413e49b64b1247919c87c4161f88ef472036519c0c605f42df15609f849e22e105076437c19a0bf054424c0f9066025c0c4035000524114a83d264f4b885240f4b93d2a234983d2a4f4bb3d2e6f4b24d2813498352c034b1852c6d4902d242d4b93524094884d284d4aa3d26334a0bd2a614b0bd2c13498852eaf490352c734b1bd2a274b13d0e4f4b01d24134a13d2403499352e334b09d2407498b522014a8c52e2f4b08d2c114a84d26134ba4d2e8d4aa3528334b9b52e61498052c054384d0e4d4a0352a434a9152a474b84d282d4a8bd2c0f498bd24014a002ae4cab8c32846eb1caae10ab883282eab84aae22a393ca40cabb0c282cab91aae4aa3932ae0aab8caae2aab982aea4abb128e132983aaea6ab913a610ab8a3a612aba32ae6cabb1aae26abac2ae4eab822ae42caa3aaea2ababaae048b8a1ae462ba9a2e260bb192e660bb0ffffdfdfbfbeff7dbdddebf3f54d435011018c53100310c020 else 0x2a514f996be52268663fe3f325000b13ca8643f53090a16b2b1c08e6b231fc5008b7c382938e31a32317b310ffc6068f40910413efe1f6c01485ee44d9b654c87a249bf13a091bbf9e4f32ae0e4e3d3a92ab09fe26af3c9e651e04e8247ae7089a62f4408edf4ca44663e5120b04991818324)
def d7:aC:= (122,2,7,720906,68,13,1115,kY)
def d2 (i:Nat):Nat:= (if i<1 then 0x8d2114ec42d555274bd2a00000161bc698a2be56e421c83e4eb400028745174e28a00000000000286640b140300000000000000029000001258a89ff00992fe0002b3da039c601254b5a7f81c0000a2dd89140da00006de2a4c59326092843a17450c9f98641eb8a6b0f032194d57899800010e20001c2208b800000002805000000000000000585b4e2b828d9a9b073f668000000008cd0000ca8dc8ad2baca4800000006ec3000060efc281810153c0000000217ef0d083fe87f00000001a1b8000781ec09a000246b324e0000a18c00039010001415c9baeb4c41fa947800010ac718343a800b516940168a70089713c725c00019a69eb0a0e0430e88f585868e0660223a8000a20e09dc8435154e1a3a209844215f52428c1cc67013432ca00034b5802270ffe195659f02531b064907608000e55761ca05e994bc50c000024e80003a02817f18688f76221a3d7d8af0df90eba87909b1876f302c105aa780000000000000060c0e190431ed5c5ec7000063d08b774286a09c1800006874a10ac3148761ac93451490187128de904f03084bb0000a1760000000300806afc2d7193f6fb0001841047b1299605400e8ea3fab29decc4b4cb3f14996518be8037c8c662106570000523a41e200014bda0cb8046d9e082a6aa400000259c4890f3613a227b440214710bd222cc55f95a52ee000384b99090001f43ac0db05dc2c380b606a4018e2c7c29000020e0b2c1c36d592581d405720e2070800051e58148179e57ec06e29fd94ff1596e576499887e93d52040000000000000000000000795500018280000403f0001612c0000000d17805980000000115f98a2c6b8000311dd8c356120d5b0c303bf0199866f08fe41a48e86705255e23385c8000b199fa7000050bf517da340801104c12de04508900000b134e067c961c1421cdc609488c1179277c579c8b767531636558089d347628365a2ca9e67f39dc94eff59cd5e90d481580b63f30a091557c001e97ce0ab2092d9b9923c13184648424ae092a2000251800e365b6ec4f892fb1b00c5dc12c482812e2f0e3ac0000000dd56a4e1cbce14af06045e8559b8202a28aa3599f78a280094d6254a491b0a46e5c4126684e456a0000c079b020000034f4b950b30000428604a800000012236482a88a00000000000000050ee000255e0000d1f600034aeaabb506cd2c00000502a8681003000e00140330401a0204c8b1a0000181040800456140030441602023011024280ba0254000865c1840010380140418f100c0150e04008001d0071a100802810081021810300000813204004060008e000c00e000c78710080080004291040029d2a44b0600006020a004820600003002c0042e002800c1808804104021e0c1810804080000440006000881824381004010402081091e001882208203 else 0x1b4a50500001d9fb975a15d240d09f665ca19400010148000d1120470000302ea103812ad92800041b8000000718e4000169580000000ec7a54fe07d532f9ea60000000191fd235ab94000005ceede82b68ac114331d200000002c309023e0d6a8e255930f60000c3e469200000000000300c89e400018b2000032dae49dca328dd0000a33c802b87e00000002020487dc8f05b1242c8cbf3068ec0c87758a5e2ae00033b16092dd50a395c36506b110702c1017c118ae2964af86cfc2179248c7f843873f929c843749a8d53e0a64b7917a78aa300f619f11a0a6c8001a2da47e4e380c952035c3c914c125e79dcb032d7fa52532f204a38c452e64523c2d6831f0269d1e3b6000046b502a1432594f8042e11bfb571400000a50987ce83cb1f0000031980004d6a0001094d53200010bf800016ed000074c40006015000000021b6800000000a15c1ea832e2e1639ec13384f000000004985c7752fb3484c94632b82150298cb54f6700000000000084291da000200d009f000000010a20000000144eac4c90ba0127cce6836cb09b02f9c9c5737045411fc4dc83c51313029e144400d939d939a26f84e6069a63962ca054f61f393ca2d000fd)
def kX (j:Nat):Nat:= (if j<1 then 0x6525d9a24904d89415292e2f4660a546a02949804e92e6012580e3841401982aa92a4d525c84a4901d496028e285512442340a129793064f2c6e9261e3aea93e49204ef2a521754a9a4b94249760e92407125d43a4bb2b5160ad12a2b066119c4a8b94954511aa4e1c508d249035714182e282f524812a4b9398d2068910f412482ca4b09d49727c92a44de58dc44409749204d1ac0e125825c4b0d4714236e2a8d866008a4c28e79317092e42925d820cc2b55d52a91ac2e1e4c2a24ba8349730292e8cd25d4224a8b6496366330539261d244a8ad8d845292e6cd248118cc2b4198224a2c03125ca7c6900b49406692e4f622063a4b954498244330ce125465bc982c4971871a60a52614a24a0598d2071110341e4c27a4b0351983511102dc6619a3cb1d44976583306a525c8424b88279537092407dc551724b0cb19855e92e42dc502a46c1a98d2034f2615d2614e82c1220487860b0e18161e182c33629523e090efd5551e8243be05821e0b06a0e5cc30243d75952a27ac274e480f36aa380580b20b0ec98212890b09039730a230754e20e282c14d05836682c270d50a6b4a0c20581408a4094160a314a94d05870a4302408585002c22821602c0b0ad8e4c260ac0b105802ceaa6e1048119ec01d05823e53047ca54878243b94572707b0a74858081c985904879e7ac0741604f9ca89e3d72328ae6a5b505c02c3ba40818a52c27ce548f02c14e21524042c0801605b20a0a861429052a538121e81aa12005849c130d38121d91aa11c4d63aaaaa50016013bea12935423eeac6e1654ab34a0ae21514082a2d0a480fba98504171307ae429a505c9cb1d805859882c0701606702c3835954ac52a23c848081cb09e05818c6ae500e580f20b8830487a6824070e4c268243ad41863882a471358ebb4a12f5554a70a82a41604810c0a005822a0b0ef0d5c9db2a117418538090ec0854483a904804878452a27c360600243b121204042a441d4c5c20b88929813e72e60ca580f9ea89d29522a8a40881604796a11e1d4240030d389508f98a11cffbfdff3fbfebf7fdbeffbbedfafe7f7fd7f3fbfedf7fdfb7ddef77dbf6dd9f5fd3f3fcbeffbf6f7bbebf9fe3f5c5535c1535915358d535815350553501534c5534c15348153441531c1535d5435c5435c14358143545434c143481435d5405c94058d405894058540581405514054940545405414050940505404c9404c5404c140481401c9405d1105cd105c91058d10551105091050510501104c9104c5104c11048510481101c9105c8635c4635c063480635c4535c053480535d8405d4405cc405c8405c44058440580405484054440480405d8315d4315c8315c03158031548315d8305d4305c8305c43058430580305483054430480305cc2058c2054c20500204c4204c0204802044020 else (if j<2 then 0x91681d011002a0fd070f4380c4270111f8940107c110cc0787d000a6000b8000b02b0bc2deb07517a69d25e8cf4179efcdae64f2cf94fc90e4271bb8b3c3fe1870a3833c0bdfe6fc77c5bd4ddceeb7743b8ddc2ede76c1b4bd966c7761faf6d6ceb0f569a9fd4aea174f7a6ad2de93b47ba2fd10e8273fb9e3ce566b3333987cbc65b32bb94cc9c64b72258fac6fe34f1898b1c4f625b101868c27e10b06d81fc065fdefc77d5be45ecaf3178dbbcddaeebb73eb925c2edf36ecb70db42d836b3b53da62cff673b2ed93ac8962fb0ad80ebe75dbae756d2b41595abed5d6adb553a9dd482a0b4eea6552be94f491a3cd19a883430a12503e8013f39f44f627953ac9cace1a6f135a99fccce63b30d97a4b9a5a52c29554a7650f27d934c97a49923a912c8624051e38e3c6ba34518e8c2c5b22b514289d448220b0f486b43261830ae84b421e0e506282b410e06701d807400dff6fee7f03f55f8efb77d5be7df2af827b83d89e9af367943c55e14efc7773b51d8ceb97513a4dcfce7272f3941c8ae39711b855c12df26f5377dba2dc56dd3689b18d776b5b579aa4d4769a34a1a2cd0a67933999a4cb6655b27190ec6c62f312186cc186052ffd7cebd25e12ec5740b8d5b62d3566ab28586ac0d5e8ae456a2af5556a9a53ca98d480a26503a7cd3cc9da4e026c534c98c4bf25b92b894749ea4892068ee46a231d1688a744821d90cc85341c20910207f43ef1f1cf5e79b3bd1d80e8c7383901c34df46db3659ad0d3869033f19acc94637311981cbe85d42dc16b8b445922be1574aa654229a9450a024ee26992dc94e494242117c87c42e2098fe07c43cf1d20e507043611a38ce864e31c1830bb05a42bd1508a0c4e425e12788fc456212101079c3a21b20d206342f81680aa84d424a10b079839016c08e03080cc00033031d25c9fc4b0bb71429292e21a3481924c3a1198262a2c111261e824b88549208c92ead525c6ba4904c71425e92403d2618e38a1188d20aa9304963481aa490228d2062f26142254578cc336198086910518660670cc32c71422ef2415925c8c0cc10c492096f24121248104440a45161831a413d2486324bb038d4253110284660d9a4b881498366330269c549dc4a8d249765a92e22925cd48cc22971418712a2ac6605224b09f493066baa501e4c24a4b94171423292c07466050a4b013893154e284c62204438a0c449529692e4dd25d5a0cc2b689525ee240edc551ca4bb2e1980191a4129754a4a4ba8289515d1a41046608da4b88b4920b092e22125ca224a9b35d529f12a20e25059bc9932198074930c4de4c5d46a8b849709e3305246601946902d49765e92e4312548a28b09a79609033012525cd50cc2ba89516a92e46521ca324c30d49202092c13125d8138904081207e3303112549a44408189516892e2 else 0x340a25a5322c508f112816314116c3de54064dca108c686c049ec18d808de0829e121cf18c88708802c913c053686908722a6065d5041b011814e2218030127c898cde1045fae0190e111e05df2863ef912326700c746877788680cc210053a42a3435615f2106c359147a03199093c85065f40630ff70992f091d6cc53108c84e116c50b5450d0144be0640f4a63c9700c86421c8b2da1d9923005f190e3e018ddc2106b41602dfc0867848d7a886ba887591588b5e282f71020d80ad4a19e0559147cba06417d1a0f6f8489bc215585808f90aad09a45a83b90a7f0488c046f0415a234057a887dfd531a78c4bc06dec8c6e021b3e9127810e9087b431800047f00c7de40c60f0020f47e8220fd0436fdb422651f810880159731d7a031d65625ffab00233cc0d8084f486748b682409780cb036fe60190bc0319c22c6073a780648790506c05730922f2153c2a0cb619e0431942af60636810f5886012d7219028958b78421d6a1d5867f443cfe000c8bfd44885f4a63302cf06200c7ca18cf2238fe26300e70020d7d79221ec0f3a78064581005af232f2863a703ba14336236020e0c4c7433e221eb8140400d02388980dc450684604c040147262de108b61677416403630d86eb91d21ac8ab222fc898de02581278463a3433d243d41da143b88a90981133c492c0a8147286300a43ec0a81521cf6663e2e18d7c486a05b415026026708d80bb262602ef806360213a43af362642048e06e1848ef10a0ee22a4c495ba625fd0811550340590e2c735843be223b11e6989f6022fe810118edf1613b79231b00efcc312a023810f888f88a78e219c84766235fd020232f848796c3d05967c0844edb498cb6e848c034039f021107021024fc218de029a42be08e62a86016d509453b7c584f35843ce68191c057109120798c18cbf80639a424ecc590e8190cb090cb0923c10193b3263ce48c75e24c72c904bfa04046ce68192fc402678083e018ee2121fa230fe404c97845b65511bc218cc0b78424ecc49dbe08655bc09b50863c8508bd0d8b035c91977fa0910023023e03ada98cedf16138047e0370147d309195f6021f023c8740c85fa44c97c44fb010b8133ca8100ccbfa0404698428f448c990e81917c2434ecc45fb1482819e690ad5245fd0202367340c96223e446808af9249f021127c08449ac21d72923227ca48c8bc4232c24ac467c0679c46be80443e039f5a089b2b221f790c26780b3a1319b810cb092f91187e1d0321f01b7ec0c7b59288708829e5ff3e22a9c6fd08248df7fcca0824053cbfe7c454be30c6f1a092a21088340e91013c2805841913414844b4961d8042140842076168d1128a002041230830042241c581bc54308404e071228552789d4186d154a02409604480450c))
def d6:aC:= (387,3,7,2359386,103,13,1105,kX)
def d1 (i:Nat):Nat:= 0x4048000b050c190000427c0b6c0ae0f8000000104ef11dc59702504c0002c1800020759179d2161bfc05f1f9c566d19c76b1d2c3080d1a07c04df1a00000003098000c08207790bc000d109d3bd0a68070018000312ec6ee1e603900c583a64be435318e5361509868521b480d14000061f544fe9a2085606fc212022422905f08741ac0000003c0b40dd01e10ec84011cbc52b0e0f51a123465808c85a1c0444660f4c1561b5c0ce444000812a82800f105b000286710ca054a1b085800014600000000307c483404304d4074c330000000c1ff0841038000484ec36f1c287a81ef449f20986a315ec62200000070b948101a6f5f2222844000041c0000000500a40d0002025706b864214c0000002043000145c203f51d0003c61000342b211600150a8000000000011e000081cc00059ff03f0001b45b17c01611c5424e00c00014dc05d0000b5a6c4444144b2c2c0147c7cb0440007013866515700a404048b3520eb08aa5695d0a755101400104110500d38b50100a080
def kW (j:Nat):Nat:= (if j<1 then 0xcf10e13bf579aec5c2b756a2cd588b015e2b6560ab1536a0d39a634a690d19a21422804f49c9362684c39772ce52c8d8f91d23645c8a911e1d42e84d06608c057f4fc9f53da7a4f1ddfbb775ee8dcab8d6f6dadb1b4f684cdd9331961ac05792e65acb0d5baaf538a293f2744d09812aa464768bd13a0d40a7d4ef1cf38e6fcd91a933863cc39772de570aa1422684908e10b1f43c86f8d71922d85309b1242183e8710d0170268420660940d00f0001330942649c6ca0b0c541874ac3246645536a94785422c1330a026430ea90069c914e9a40da95064209034752033292241b508ce49842a9637a7930252481b8cc8a5119128790335f508906c899c930be52a544f206b8ccc250991c3ba413cf245206c91ad9417cfa844e250869e40a6d94158510f54e21ec0ccba19d601211318dc244b7098566d423052a54195806b2b08b85421213235e250829e48a9199501128433450821443dd6d4238c92274264a284c9533c984a1324d21480f4e48a38d510312e219f5088c4a0b128878cb28475b508dbea1145161327ae22275457b6ba8715911d324039c545ccc903919921b12c3136505704c95c6d422e2b243cf545598a11b7d730faa40d46644588c915454195192245b508b70984189710e2b303d9244164a0bfe52066bac251858471e40a230876ab2847cf206cc89857b154787b0eea2508518aa408942123930b784c26489014b952a942c983348192aa11dbd209c01300c1261290a952b520b6013080921f134a116348396f284470505d9643daad30bd028427fc7f4fe5fb3f57e9fd1f9bf2fe4fc5f6be97cef8dedbd6f87ef9debbcf76eebdb7b5f69ecfd8faf75de9fd2f9ef3be6fcbf95f1fdf9beb76e7ecfb9df3ae6fccf97f1be1fbf95f6bdd77abf1fe3ec3f4817154d635915321d6454d5458d535014154d54501535494054c87501535493054c844c15361d2054d304815321d2054c81481535491054d204415321d1054d861c1536107054d811c1535493050d424c14361d2050c8148143205725018158d405056250161581405c954501525454021d5150172505404c532501544c54054531500874c54058d30501614c14058130501524c1404c5305008148140549734408758d106095444181551105095444087551105494144142505105d94044184481105cd20441424811050520441404811060c72441541c9106017218d205c4634817018d87480634817114d825c0534817014d87480532052014d525d84054576101425d84048176101825d44060575101615d44058175101525d44054575101205d44058573101605cc4054973101515cc4048173101805c84058572101605c84061971101855c44058171101525c4404817110182584405096110142580405c5511008148040549760c1205d8305cd31081714c420 else 0x2a743e6105ac2095c0d7b8c6c040101078c50c0aaf41113c18a9815e610c03b2626c097a420000b213210020464200000000000100005023e22502001a0800026c21860c6f60300003e2200701380b50401682016424080000f88801808000004a0c3020152b14d2100078314584812e909c056432837488c866108be314a080073625f90ac8501b2100205748980990802c7a4880134853f090ee910000548802e02701004e210003762005e9093613e2200dd2168d08034c218058442710cec0e90804c8402c04016023244c04c91260748690992206610100a2784ed04271200030d019507a0004620e00c830008f90124ec020b004a828120fd1662d4548002c43e0b80002905e0ad0002dd73ac74e689ced99f28e46c7d8)
def d5:aC:= (137,4,7,3801188,103,11,1064,kW)
def d0 (i:Nat):Nat:= 0x247800a1c00085000a0de22d610c00000272000f1bc2ec1b90725c1d40191e0508b44d01001a1400000c080000000000042841210
def kV (i:Nat):Nat:= 0x2c08168400e410815871042002c08000003504205c102f02d800181687ab67230efab6722e19d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d4255110f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc40fe0509302052050f9a542261205c440f2950891481761039d1302048748153f625092058173103d6151481525cd10b0729d645516354e07ca9549861c153
def d4:aC:= (19,5,7,0,0,8,0,kV)
def kZ (i:Nat):Nat:= 0x81900
def kU (i:Nat):Nat:= 0xa3390a134a4c28290221e50549302048748153
def d3:aC:= (2,6,7,0,0,3,0,kU)
def vD:Array (Bits × Bits):= #[(0x9017721c30,0x14b5bd0008),(0x500e080936,0x634240ff36),(0xffffffffffffffffffffffffffff4ca8886101,0xffffffffffffffffffffffffffff8c0d9a00c9),(0xdc001a04a,0x12b065ab12),(0xffffffffffffffffffffffffffff815101844f,0xffffffffffffffffffffffffffffe94a0254e5),(0x2200761284,0xca4842b0f4),(0x0,0x0),(0xffffffffffffffffffffffffffff2220844287,0x31b2254f02),(0x0,0x0)]
def vC:List aZ:= ew 39 (fun x => (aU x 0 17,([0,16,32,128,8]:List Nat).getD (aU x 17 3) 0,aU x 20 17,0,([7,8,4]:List Nat).getD (aU x 37 2) 0)) 80 0x800360014900074002890c4f80c10204b7004088004e001302baec2b8105d0f85d50218af018104087e009000429c04062000b8005420cb700c084695e068203387c33a81054f8051040039000861ad7c1ac02b3af43380a00528000d22c9f02c202194e218300c29c0c0600f5380f0c40087000385f57a1f404c32dc430211a5b81a040acbb0ac04801620001d00298000645d5f05d008a6bb0a60480147000290006d80092000f20040c00ac000138014c40012002ec00012004e00011aacbd0ac021583e1594035a9c358605d5385d0c0aea70ae185c57a1c4043887c38a81725e872010a61f0a6a014d4e14c300187c01a8003538030c30caf10c105ad5e1ac20aeabc2e8415757857082a6af0a6104615e0602082af402809051f805402d6b70d60855d6e15c10822f402008005f000008081f008a05756e17410a9adc29821035b80304242bd042025747e17500a98fc29a01031f80340246bd046020003e00140b5af435809575e857012a8bd0a80240d7a00c040687c06a81005e80001000a700018
def xX:List (List Nat):= qE
def yV:Nat → aC
 | 10 => sY
 | 9 => d7
 | 8 => d6
 | 7 => d5
 | 6 => d4
 | 5 => d3
 | _ => bi
def xY:Nat → Nat → Option (Nat × Nat)
 | 10 => aL 177 223 4 13 7 2 sX
 | 9 => aL 185 697 7 15 9 2 d2
 | 8 => aL 39 199 6 14 8 2 d1
 | 7 => aL 11 35 3 11 5 2 d0
 | 6 => aL 1 3 1 7 1 2 kZ
 | _ => fun _ => none
def zB:aM:= ⟨1215,10,fun j => vD[j]?.getD (0,0),vC,xX,yV,xY⟩
set_option maxHeartbeats 0 in
lemma zK:aV zB (aI z3) = true:= aX 4 0
def z6 (j:Nat):Nat:= 0x764260437506145074436550744365407443653074436254734362657236165272361651723616317236163071362652713626427136264170435540704355307042554070415550704155407003547070035450672465416714653065360765653607546536074360634121606341106060416160604121605341216050412160134121566307635663075453641483531322715313227053132261531022715310225051643070516430505135227147145542463462604606417142560343425603324256032142530343425303324246037342460371424603434246033242430376374316743743167337431663374316623743164337401475374014633734657337346572363562323635622136356210363462323634622135461480354614403546143035461420313522823135225231352232313522213134223231342221313122723131223231312221310522323101223231012221304656652434038317632675154630701546306015463050154630101545307015453010154230101541307015063460150630601506301014463010135322521313228213132275072455740724555207145574071455640606418106064161060541810605417103645676036456650364566403645483
def z1 (j:Nat):Nat:= 0x6453043210043201064500432100432010641306357005416106410043210043201064025174200502100640251742004610006402517420040210064025174200401700640251732003610006401517420050210064015174200301500640103457203042106324067501054021063200675010540210630120364103201006042537420030270052345207130072600523452071300523005234520713004270052344207130052400523052071300623005230520713005230052305207130042600523052071300412005046010432010421040351306420124300403113064201632004031130642012430040311306420123500315406417200162003120021053021061031200210530210310312002105301602103120021043021031030420315240103600304203152401034003041031524010340030410315240102300254064170302604002460057610056201024600576100341010241004321004320102036001674012501020340016740126010203400167400146101450057630012561014500576200451010145005761005620101450057610045201014500576100342010145005761003415101450057610012031014064135200402100140641352003021001402413520040210014024135200302100140241352003017001324023401034021013200234010630210132002340103402101304607241072010013046072410620100062435247003640000624352470034500006243524700273000062007561005620200620075610034102005123542700435000051235427003240000461735642056434004517156020561200045171460207412000412314602037120003247065140651000032470641202506000264362471037520002643624710365200026436247103462000214726531065320002147264310473200014236427104362000142364271043520001423642710325600014236427103251000134746530065400001257465300654000012474653006540000124746530054360001247465300543000012473654206543400124736542054324
def zE:Nat:= 0x5021042110c0300c03
def zD:Nat:= 0x24914891a0c85405
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rO:ba zB 5 0 2:=
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x7570) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rP:ba zB 6 0 19:=
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x6f311660000238033954395f3a36481e4dbfb1) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rQ:ba zB 7 0 137:=
 (@ak zB 7 0 64 73 (@ak zB 7 0 32 32
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0xf456a7442354b2f19185c5c34004fc7ad00d8a4cf9f00a4be00d000a7a99000) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x6900281b446259441f4e1a250b186118056a663a0718715c536b661845495029) rfl (by decide +kernel))) (@ak zB 7 64 32 41
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x5b4500305300182327273c18131712683b18185d1118451800442b005c472337) rfl (by decide +kernel)) (@ak zB 7 96 32 9
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x1604440027000044006c5a5d511a583269584a182f1a180d1418491866454010) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x1818403d3232183c18) rfl (by decide +kernel)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rR:ba zB 8 0 387:=
 (@ak zB 8 0 192 195 (@ak zB 8 0 96 96 (@ak zB 8 0 32 64
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x930097c585d69c0000848a00a4008f0000b6a88700820088b6808a0000000000) rfl (by decide +kernel)) (@ak zB 8 32 32 32
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0xb0d2a0cbd7a2000000b5b2a3bd008a84ca8981c4848e00829d00aa84c3bac898) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0xd5b5bfaaa4c00000b583a884d3c6bc84bbd984ac009fb400cc9e84cd92b8c100) rfl (by decide +kernel)))) (@ak zB 8 96 32 64
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x8484a997a3a5d48484c3ce9ac58084a18497c5d1bfa4aa00a6a88080b6b9b6d1) rfl (by decide +kernel)) (@ak zB 8 128 32 32
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x2d5646645b00582828462842005b188684a4d6a4b9848b8a8484a3bf009600ae) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x181846063e5846581828564518155d28555b2863180a18185d00585b563e582a) rfl (by decide +kernel))))) (@ak zB 8 192 96 99 (@ak zB 8 192 32 64
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x282846734500004626235b5d465a5b27671815186e18185823092a2d5e181828) rfl (by decide +kernel)) (@ak zB 8 224 32 32
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x16582818181846464667581c5818462346241826185e18585b2c586d334c0046) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x58115842284618285b18211808181828465b5b410e732045082358005d15183e) rfl (by decide +kernel)))) (@ak zB 8 288 64 35 (@ak zB 8 288 32 32
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x2c6a4572183f581822416e585801235b083e182843461818232c0856575b1d6d) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x465d00452852112d0c4558461858232c56234658330818285b182a5b1846185b) rfl (by decide +kernel))) (@ak zB 8 352 32 3
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x2e2d5246235b43283f18185e6546286a01574546000027181818282d5d004618) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x181827) rfl (by decide +kernel))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rS:ba zB 9 0 122:=
 (@ak zB 9 0 64 58 (@ak zB 9 0 32 32
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x0) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x8494bf9d84d6b6b6bba48c8dbfb381d600000000000000000000000000000000) rfl (by decide +kernel))) (@ak zB 9 64 32 26
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0xa49bc284d681a4d600d6d60000918184bdc5008484b4d697daa4ab9d8400c984) rfl (by decide +kernel))
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x8cbf8495d68a94b7d6d6c9af94bfa4a481848481a499ccb48c) rfl (by decide +kernel))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma s9:ba zB 10 0 10:=
 (ac (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x0) rfl (by decide +kernel))
lemma zA:bS zB 10:= by
 intro k hk
 interval_cases k
 · exact as zB 0 0
 · exact as zB 1 0
 · exact as zB 2 0
 · exact as zB 3 0
 · exact as zB 4 0
 · exact rO
 · exact rP
 · exact rQ
 · exact rR
 · exact rS
 · exact s9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma q6:az false (au 1215) 10 (vars 1215).toFinset:= iB (q:=191) (prior:=aI z3) (ag z3 z4) (by decide +kernel)
def jU:= aq z3 11 [(6847,0),(1887,3),(14175,55),(8059,11),(17275,29),(17390,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xP:Known false jU:= aw (m:=6847) z4
   (af (q:=1215) [2,1,2,4,1,1,4] q6
     (aW (g:=zB) (i:=0) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def qN:= aq jU 11 [(14143,2)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yB:Known false qN:= aw (m:=18111) xP
   (af (q:=1215) [2,1,2,4,1,1,4] q6
     (aW (g:=zB) (i:=1) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def qL:= aq qN 11 [(17087,0),(9535,17),(4959,3),(2415,13)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma y9:Known false qL:= aw (m:=17087) yB
   (af (q:=1215) [2,1,2,4,1,1,4] q6
     (aW (g:=zB) (i:=2) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def jN:= aq qL 11 [(2239,0),(4927,85),(6975,17),(2399,3),(9567,55),(4975,13),(7023,86),(2427,29),(9595,11),(9703,158),(12782,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xI:Known false jN:= aw (m:=2239) y9
   (af (q:=1215) [2,1,2,4,1,1,4] q6
     (aW (g:=zB) (i:=3) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def jR:= aq jN 11 [(2751,0),(1343,2),(18751,26),(1375,15),(18783,56),(1391,57),(18799,58),(1403,7),(18811,87),(28135,54),(6638,31),(28142,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xM:Known false jR:= aw (m:=2751) xI
   (af (q:=1215) [2,1,2,4,8,1,4] q6
     (aW (g:=zB) (i:=4) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def jJ:= aq jR 11 [(1727,0),(2367,2),(7007,15),(9583,57),(4987,7),(17341,23),(14318,31)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xE:Known false jJ:= aw (m:=1727) xM
   (af (q:=1215) [2,1,2,4,1,1,4] q6
     (aW (g:=zB) (i:=5) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def qP:= aq jJ 11 [(42687,0),(44351,2),(47967,15),(53087,3),(44923,7),(69499,11),(60349,23),(69565,59),(42983,6),(45031,88),(53230,31),(60398,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yD:Known false qP:= aw (m:=42687) xE
   (af (q:=1215) [2,1,2,4,1,1,4] q6
     (aW (g:=zB) (i:=6) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def j2:= aq qP 11 [(58559,0),(64191,14),(51007,17),(54079,2),(46431,3),(43887,13),(54127,58),(48507,11),(43951,78),(43453,23),(64445,59),(49646,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yQ:Known false j2:= aw (m:=58559) yD
   (af (q:=1215) [2,1,2,36,1,9,4] q6
     (aW (g:=zB) (i:=7) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def j0:= aq j2 11 [(58047,0),(47935,17),(69439,26),(44383,3),(74079,56),(50043,11),(58235,29),(69102,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yO:Known false j0:= aw (m:=58047) yQ
   (af (q:=1215) [2,1,2,16,8,1,4] q6
     (aW (g:=zB) (i:=8) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def zQ:= aq j0 11 [(44223,0),(44735,53),(52927,14),(54975,8),(42815,2),(44863,85),(53055,17),(60223,26),(42847,15),(50015,55),(58207,3),(60255,56),(42863,57),(47983,86),(60271,58),(69487,13),(42875,7),(44411,29),(60283,87),(74107,11),(44989,59),(69095,88),(69607,54),(48110,31),(55278,30),(69614,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma z5:Known false zQ:= aw (m:=44223) yO
   (af (q:=1215) [16,1,2,4,1,1,4] q6
     (aW (g:=zB) (i:=9) rfl rfl (ag z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def r7 (i:Nat):Nat:= 0x4c88f1a284060808057fc10
def rB:aC:= (1,1,6,0,0,0,0,r7)
def r9 (i:Nat):Nat:= 0x83800e3000c4814a28004c8280a80000001288072170108490827828b80af
def sZ (i:Nat):Nat:= 0x45e30d8a0c818140206a241064060040e1d00022e2050212800011103640685c1c10c04820d80802c260c58342c08544800504d78c021e1c0400087480d0b4609048382010050c640685848241c10080283c30342c27180a0c10040161a18161413918d06080200bbeabda425b7f9a15910f2e85d003ff5cc10ffd30043ff55010ffd42042ff60810bfd83042ff61010afd86042fb60810bbd84042f760c10
def rA:aC:= (11,2,6,0,0,10,0,sZ)
def r8 (i:Nat):Nat:= 0x202000000380606397c47943e48901800297152608243b403c8700800082947f118001c3285b90ec41920000002c8c93c003182c4b157140c72130003050003410000003d1e537c6746e01704d44505c06907602c00110950282796c162857834001c1c40e912986200108200000514a043340004082000000144000
def dB (j:Nat):Nat:= 0x5e531855aca28df80d3485b10aff144a303b08ac2279015e40503fc243f74904e6f88cfe84131fd4095e405a6492532492f60487f42099e4055ba01ef5025bee9209cfec0916e8073ee9209c7a808879e449669080ff091d4057d0116e807bd81208116988c51b8c1680a003e0241874390b410783414020482f090886c0001070642100bd2d8b0ab2a8e8a9f66f9864f8f625819f3761bf6b59860d6e54d414ad153dcdf324ab2487719c4f0f42b054002c92cc12c983ca94cb84cc11eb80cca3ca134aa60cad8a94ab9b89846b856a15aaa38cbc0cbc4a168b846cad4986aa134b9e6c95a9836b9d0c958b9c8a146a956aa58aa46985aca3ffdbff7def7ddfafeffcff618106101060c10608105cc10550104c010
def dE:aC:= (36,3,6,524295,51,10,1055,dB)
def dC (i:Nat):Nat:= 0x4200118060050390014553e041769a0
def dA (i:Nat):Nat:= 0x190040e18320081c3064010386000418002029b9673502d1e1900abf6897361810afb6a57360810ebe5c13061810efa5c13060810eee5c13061010cfb649825cc10aef68973610108f72a54260c10
def dD:aC:= (8,4,6,0,0,8,0,dA)
def vJ:Array (Bits × Bits):= #[(0xffffffffffffffffffffffffffffffa8c12191,0x7c002100),(0x100d1cae,0x38d1cac),(0xffffffffffffffffffffffffffffffc4146207,0xffffffffffffffffffffffffffffffec000203),(0x5308cf8,0x139088f0),(0xffffffffffffffffffffffffffffffa160574f,0xffffffffffffffffffffffffffffff806f560f),(0xa82987e,0x390807e),(0x1008e070,0x7c72e050),(0x4202ff80,0x106f7d80),(0x0,0x0)]
def vI:List aZ:= ew 40 (fun x => (aU x 0 16,([64,0,32,16,8,128]:List Nat).getD (aU x 16 3) 0,aU x 19 16,([0,36]:List Nat).getD (aU x 35 1) 0,aU x 36 4)) 33 0x7802dd000076b5f1d64140051c0054400529005a4000f200c1400589004e7675f1ce418747f1e80186b5e8d60240027100b1700799000c8002f900a040031c00948025b9044840063300294000e800a2400533004987d5e8fa0240027200918725e8e4028715e8e2028675e8ce028165e82c028545e8a802b7d5f9fa40b725f9e440b6b5f9d640b675f9ce4070077100118022f904a080273904187006f100218005e80002
def t1:List (List Nat):= qE
def yX:Nat → aC
 | 11 => rB
 | 10 => rA
 | 9 => dE
 | 8 => dD
 | _ => bi
def t2:Nat → Nat → Option (Nat × Nat)
 | 11 => aL 5 23 3 10 4 2 r9
 | 10 => aL 27 69 6 12 6 2 r8
 | 9 => aL 2 13 4 9 3 2 dC
 | _ => fun _ => none
def q5:aM:= ⟨1279,11,fun j => vJ[j]?.getD (0,0),vI,t1,yX,t2⟩
set_option maxHeartbeats 0 in
lemma tO:aV q5 (aI zQ) = true:= aX 3 0
def j8 (j:Nat):Nat:= 0x847465507548287565753010647580103578044026643171266431212664311026523060
def zZ (j:Nat):Nat:= 0x760215268407140007602152684021500076021526800214000756214263002130007502157680021400075021526800214000724013674201273007012142630021400070121426300213000641207854107502106412078541065021064120785410640710641207854106402106412078501064021041620746810017200405707468100162002305817562075120023058175620651200230581756206417002305817562064120007214135200402100041202345103702100412023401073021
def vH:Nat:= 0xa04210842110c0300c03
def vG:Nat:= 0xd064a49147434114642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rT:ba q5 8 0 8:=
 (ac (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=0x304020102040392) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rU:ba q5 9 0 36:=
 (@ak q5 9 0 32 4
 (ac (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=0x60002090900008096919089008e8f8c9300858b82898494888e8a810087838b) rfl (by decide +kernel))
 (ac (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=0x3050807) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sA:ba q5 10 0 11:=
 (ac (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=0x9586008d00000000000000) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sB:ba q5 11 0 1:=
 (ac (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=0x0) rfl (by decide +kernel))
lemma y7:bS q5 11:= by
 intro k hk
 interval_cases k
 · exact as q5 0 0
 · exact as q5 1 0
 · exact as q5 2 0
 · exact as q5 3 0
 · exact as q5 4 0
 · exact as q5 5 0
 · exact as q5 6 0
 · exact as q5 7 0
 · exact rT
 · exact rU
 · exact sA
 · exact sB
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma q7:az false (au 1279) 11 (vars 1279).toFinset:= iB (q:=255) (prior:=aI zQ) (ag zQ z5) (by decide +kernel)
def jO:= aq zQ 12 [(27127,27)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xJ:Known false jO:= aw (m:=2303) z5
   (af (q:=1279) [2,1,2,4,1,1,2,4] q7
     (aR z5 (2112,0,2239,0,11))) (by decide +kernel)
def qM:= aq jO 12 [(17151,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yA:Known false qM:= aw (m:=17151) xJ
   (af (q:=1279) [2,1,2,4,1,1,2,4] q7
     (aR z5 (16960,0,17087,0,11))) (by decide +kernel)
def jS:= aq qM 12 [(18911,22),(28151,27)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xN:Known false jS:= aw (m:=2815) yA
   (af (q:=1279) [2,1,2,4,8,1,2,4] q7
     (aR z5 (2624,0,2751,0,11))) (by decide +kernel)
def jV:= aq jS 12 [(17403,89)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xQ:Known false jV:= aw (m:=6911) xN
   (af (q:=1279) [2,1,2,4,1,1,2,4] q7
     (aR z5 (6720,0,6847,0,11))) (by decide +kernel)
def jK:= aq jV 12 [(17405,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xF:Known false jK:= aw (m:=1791) xQ
   (af (q:=1279) [2,1,2,4,1,1,2,4] q7
     (aR z5 (1600,0,1727,0,11))) (by decide +kernel)
def jE:= aq jK 12 [(3579,79),(18941,4),(11774,159),(18942,160)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma x9:Known false jE:= aw (m:=1279) xF
   (af (q:=1279) [16,4,2,4,1,1,2,4] q7
     (aW (g:=q5) (i:=0) rfl rfl (ag zQ z5) tO y7 (by decide +kernel))) (by decide +kernel)
def j3:= aq jE 12 [(58623,0),(46559,24),(43517,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yR:Known false j3:= aw (m:=58623) x9
   (af (q:=1279) [2,1,2,36,1,9,2,4] q7
     (aR z5 (58432,0,58559,0,11))) (by decide +kernel)
def j1:= aq j3 12 [(68863,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yP:Known false j1:= aw (m:=58111) yR
   (af (q:=1279) [2,1,2,16,8,1,2,4] q7
     (aR z5 (57920,0,58047,0,11))) (by decide +kernel)
def qU:= aq j1 12 [(44799,53),(42975,161),(58335,24),(60383,22),(48119,46),(69623,27),(45053,90),(58365,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yI:Known false qU:= aw (m:=44287) yP
   (af (q:=1279) [16,1,2,4,1,1,2,4] q7
     (aR z5 (44096,0,44223,0,11))) (by decide +kernel)
def z7:= aq qU 12 [(42751,0),(47871,14),(42999,46),(60413,4),(69629,90)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zG:Known false z7:= aw (m:=42751) yI
   (af (q:=1279) [2,1,2,4,1,1,2,4] q7
     (aR z5 (42560,0,42687,0,11))) (by decide +kernel)
def rE (i:Nat):Nat:= 0x5a2c1286c92b8843c484150a450271300c12251208c44210334401f0f074381b0d06430170b05402080a04c24110803c1c0d065c160a048200e063014080301004006f6f1294761d803fe887fd30ffa81ff54bfe087fc30
def rK:aC:= (6,1,8,0,0,9,0,rE)
def rH (i:Nat):Nat:= 0x146100000004baed31538440c1ffdeb0f6183e06000a8c0b07e49b14e320002839810909504c00050a76d4868c1000068bfa4c000000000083709a00000028a800190dc14911063a64efd100000000007aed45560ed2b90b0000000c289281131c40021b72000000000000020b2031241808c49c032807502389b83e000b92e08c0009128422147ccdc24b299c6cd4889ec33b15a259e00915b38a81356660ac43d82820ca83712145fe1b30b939f002000f12fa0743b0039c1d0b445d640f035b1000194c0000001045e02d07502ddb960a713a47c0008c3e89f81470c20450413471001400820430050b11c35410032cc082000283
def rD (j:Nat):Nat:= 0x6ffff64904012a7fcc020224b7f64e130f024d2bfafe40a032481e0294604de32d22ffc68564541281bff0144081a63d8b819409fff785350254fffe02f017139c88000001547ebf703c5804a327e1f3e4c0082f1cf1be89c1b0004ec7062909778125ffe0ca5ec0085e09fb70ef058a20000dc5fff81aae0670005ffd7000400fcfea2002aaffec8001025157aa85702d1ae1e9c8400000003ff3fc7f8990414d7fe7f00184005c15620000af597d0ca8a688f6fe300022685f554114bff14d63033dff85f00ccb9c800caef024afe865044340378275f91338fb400f3f404a0073c6fbb0870004c004ff0178007139c9224a93c6a8dbca09400dffea8819f3f0e0085a338ff5f0360058d98227afe40ec8c00004fe7ff61784cbbc09000001f000000138ffe14e3f504e40cc185538033003cfc0464a86819c66172268a04d84e148820c8404551112469184211b10d424450f4fc3981c641855454d52428511404f1394b0a82900c2809c090941f0c00486a170520e0086017c5e16e06490464743a41c6518c6289d565552c42c2487612872188442d0320f8340b1303c1762a1695855d3d4084844d304b51c082018260882e2d96540436024cd324c51488e038120a0bd2b11e2c86d204404a88a210da2550438caf100d43b0f8371270f0b8348900001c0697a94f9158e38c58a386e83a81a7e378274c7106d06b169b6616155e45835535255044aa44941c3e83ca39b3563403132e32b02a526c2151e51b618713f11d0dc0c607204902300090414ae2e57352b8391cd48e6253032c3c90c14ae12560729829619cae3248352c189609ca632570329859605cae2647132a8b9589cb06a48172c0994c04a40d98306c1a32059b060c8126c3c36199b0251862641a8481c2e0d5418ec107482830c498202c18ffffefeff7fbfbfbfefbbdebf549404c1100c010
def rJ:aC:= (48,2,8,655366,67,12,1166,rD)
def rG (i:Nat):Nat:= (if i<1 then 0x46d2ef6d0e6207b000048f90000000054c6c4bb48ca6097d01f000000000000000000000000000000000c5ec8a4109c785902e500e5a00a0101c8f8501720d3781340b4e400a0ec00008421a0f450b500000000000000fe0000e073000050bcc298100850520000700e000020f098d1782814190000208e000062400000d60b0000b0321898c03bd8fe000072fc2033a028302eb0e1687968e540e720fca88a06d5d26d8087ea25b007a092e05b2009000000d5000008cb789a508ad0a1146feefc007882b700cd901988f070b8b0b9e0e320cb00d9e02a02cd80f500009039d00b0000000000003018c0eac65e48cd88655081d242041520ed982788a5fc223a4bc702a3026cd5d06d3084b0a4205624eb3ec6220b200110e47053b0d4d0ef8e90501120aec0756088e429327e20294067fa66306cc042f0f26098e03754c58ced6068122500437409000090bed0c8609500a9701428e870bf207fa08b00007072c0c790c3606a22c5a2e2d825a090d0e8da83f0699884f07a0000a0890000e047000000000000904d000000000000f071e05700000000361a000048375015302d30201025d010f410b8d8006240fab0ac0000000031020000b03e000014ca280300008079a8bec065d016e013104a000084180000dec50000385a000020abc8c6705050e0d87c282e5658a038d0a030dbe866b816ec277c0eb026303500e92005bed2d02356216076e0042d00b08f92226427686228b3e03a70307609e226a02f80d040aaca6c00baeac5064d065c528fe25c205de0b00000e0120849a027e09a204ba836c0589830486896dbb0550000000068a30000001d0000602c00000000000000000000f0bd9618b04e5021b083208d10700000f6960000000060cf0000206e000000000000f0c4589e9692e0b6f05aa0c0c8b1c886d2d792212a9b0415c004021000008902a0400000000c20c000a01b00000c0130001800000c40000c33002800420000000001c014000500000000004000008000000b00130e1800000060060820015021c00802000002810040000000004000120000000c10000000000000c03070000010000002400000002800800c70006810000440520401810000000020001c00030000800020c00010830040420001800002040c10010800800440000802800000c10010490c900000004000004000100000000000000b00000000d00000700108410000000d1400000010020000050400c00030000c00800000000030800c000a0800000000000800000010000cd00000000000100000c0020000080800030400000000000010000000800000040020071000010020000000031400000840000000000000000000060000002000800000000000000010802000000000000400020000000001c00000000030410000010000c0000000000 else 0xc2d40000e85f900d000010d80000a0d684eec100e44c70cef0de20021022603fd43900000000809908f2000000000000000000003811109f82992cda18eb909bb49b00a764c760c6304f0000c29400000000d47a00008875220e5622802ba8a0ec6c489f80bb08350000f0a5a60fc01a40df507d26e70a21b0c9e03d820c882df0f800000000000000000000e09e2091c2acc060c6f87031929ca074f422e0630cd022391e9be01ef05ffe6fe490bc9280820a90e890040b84d760d7e041f8f3383da210100fe252de2c9049a8316096d0fb70f644fc28531502da98a6da24e7f8b4a0f3540190cc407e5048b05e50d2429090347405206f000000000000000080fd0000804c229b70cabeeb80c5dcf8c05c40dc1287b84b2860626600001894a897407c9c2168da2000000010240000e0f1e8faa0f9d0ff0059fae56054b09314e2c0a3f0e24afc08f12b00e0ddb0c140a64061e09d0000600c886fd08508d65094d8c1e0ebd82140f7f682e06b1040682ca869c0af64205876442c203c60662086b08038290000d0b2cc83701b808c30ad00a2841e0000783300000000204420b1c077f8d500000000000000007e21dacd0000e8f49006b8920000b858000000000000000080ee401c203600000000a8f70000e885e046285120c280b3b045205120da8064000000000000760e70d15848000020b7f0a810031)
def rC (j:Nat):Nat:= (if j<1 then 0x53d58f2b3c28eb83a90e78393ce293768dc436c0d91359cd2233fccd432b8c9b31e8c563090c122ff0be22e5cb622d3cb392c18ada2a50a812994a3427f09d626f4992261496024dc8fa233c89b218c82b20607d21e947751d3c7121bb86c21a9467a198461f17d85bc162455014a050a13844ce128c480117842b0fd83d40e4037d0d102f70b4c29309a022507f01d106b417a053c118039c0da031c0b40284066016404600cc020003400095304255c6295717a5661894973e525d195317a5661095313e55c9595714e564629597725641695724a561d695654e55c4f94875a52618959072564df95718254c5595987e554d394918a55c5c95935255cd195515a55c9495315e565d4959872560569531825589795985a5641f95716a5662295656a55c0e9487565641894874652610949772558d394937da61d9688739a5cd169970da26102d9034b6622716559f4c5d698305a4c602d983645897698724b65d12d974a45c0f69516e45c012d9179a6055698744b261691604cb64cb68970cb641c91874e154d568972634c21716356164d490985da24e0688746364e17d9775a661669814da261f2d977235c9391206da649b699181a65d169811a154da91935da609490815da5c112d976a4605791725cb65cc7d7174b659391706da6608912060b655291315e45c1a698750b2614689744b65ce68816da65c969875a45c132d926da21d985313db5c5e689862324992d9649a605a7d4179a615369534a465d32d9169a61da698159a262269916da481b688169a6622689871a6155699381a4c112d987244857697180b646068874a154d3698121a604769706e421d3698569a24602d9189f64dd69816da21da8d718646593698704b644f69826e35c962d916cb64927d4181a6095698559a245b69874e35c9a90814e365e191514da66182d9131a61c769985245953716555a61c391814c465d11198004261035870c4660421932d765c21098604660d259784465c519954a04c571197384660f3d861cf604a81534c464d23d8618464e015963196053618120f644a59900d665c3119548a640d89724ca640051877595c1b5d8205625c3259235760805d820c42614119039764c23d8621d54611d9411e4c5d49850c465d2893085461017553844649b119820f244a59700d26141119180466223d86049648b019715061434d8408c61c305954816545458508264d2398609560830d9217ffffeff7febfbff6fdffb7edfbfeffbff7f6fddf7bdf79eefdd7b7f6ded7d7faef3fe77bff7fafddf7bdf77edfcff9f73de6fc7f4c1524815261d405c5405c140505404c5406193060930605305c5305c130589305813054530481302053060d105cd104c11020d101cd100c1100411061830604305c4305c0304c030204301c43060c10608104c0101cc10 else (if j<2 then 0x294b87d9e18125a4c0d94ff1102129ffd080042d275fc88cc7d08e32d5a4ca1d3e240ca037fc0042243d78c55d1318fe00895fff0e105d3009081b01d1fd4e20010e7b410dc82500e01ff0000d08c5060b310c019f4978ffef011359ed040b978a3df8cc2818025730485f341944407c3d214551e90632fde35400ce503bbfd64a14479ebd08198bf837d44a8044d40dfc218819dbe3fb489689a11fd4cfa8410a203b8c33a15081a8f482827f7a6d123c1044da94fef4220672ff8fda88267aebe1881981af92c46490191206189cd483f27d448490174c4a3c749363910d1e90630ef8780361ff911abdb383b610b5f13eba1b0203547ec9e824206907fb855000c14449c5d78852e1c8ad47cc58b8f0853da088ff1343221a0f764452011fdd10858604791431a4bbe9cd63940d22e1078c2057cbebd8aa49a3359ed0427c0af2080034400017c0bbe142f9501b60af51a91d3e015c308f48d5aaf7fb0e401527fcb0c8f4880466b0029f743c2871a470e26782bd46a479fea3fe0240932f282e30219bffe705d071346fc66140c0128a067b410f6821ed040efce05fa1e10d25033da087b410f6821ed04281c0e41a23c2e3080f21c82d0944b4cc4ab92ce2024c969130ec472814036174444546487c211c18800fa1ed3c6140189d9240742621c03786b6b0562abd2aa65822014464402444813026719d05a6686b1984442810b1861861dc22c9108c4700420840a0a125175b8d0fa8491844c10c39881a022281e0f2a006d41e96524896817824458500ca4084731d22819a8e88710c116154208188740800f0dc18d0622c43623134400c041dc3ab410e64af12e2d12b4c795a0211a4c89017184ac703384681383b00e220c8188a0d08a490d1a151cc378b28a70f0bc1ea0a42d09180e0385108e88686e0fc0813f0686165689024b11a661a3108784014819060ac461ff0584347c17695a070700e43604a0d216e0307c8499649f2066215043f30f06e0d2881070d40f81d83606a0bc2683ac4801c0004c00c0ba6cd9a72682994e633984a5e997565c39642569950a523942e4f4936a4c0925246e917643e908e4048f223ad8e4e3788d5a32f8c462db8aca27f895e23f88aa204874a1ba866e175854e13484520f9833a0b682ba09281f205780ae00f7fc9fd57ecdf9e7e21f357c11ef47b11ea87959e2c7871dfa7741da57601d607501d0e73d1ccf728dc83718dc4870b9c0b6f8db9f6dfdb596ccdb046b9dac76aa1a8a69c1a3267699c26695979652991363e18c86259878611981b5fd17d85eb57775d2d7275c216be5a8567e598962858455e256a558f559d51e53ad4d2529d49851f1456510541650013d74ead37c4d3d3384c4d2ee4b052a149c5249489120c47b91ce46bd18e455112744210ea430108b413901e402cfe43efcf8 else 0x2f02307bc14abdfc307b7cc69f38145081a23fe881901ef881084fe013a08547682bc08c9d1ec34420438ffa252847172f00810a97f7d114b9618fbd23190f884c4f4813469ff92003369f84009499a625fde088bd9571903cb803233ffc88b000204443891835f70913be00324f1dc2c8dded86c01980f500a327ffc4d185021e1eaea8810aefea20a20021c3a7c2c0199718110f88498f25040429bfca5410010e5d2cc70e2c3a137e3d9104747e100211bfe003255f98051aff1044a87d89218cffb7184019ca08c87321269f5983a927e8501b41251f09a0f6b1888a174c4a3578cfd210bcc0c3ed2197fffc5a3080e0854206d53f4482041535911d8fe7e60441647c503243e1da8c958204200811a1fe7da913334029feb118511ff95848330f73e7400488bfa10023cf83f022cfaa80230379971f140d0bd62a22ffcc0411b7fe140a09234f15091b7a4be1159fe903cc780896fed48a13dfa9b0021400d7b0dd44fa02228de1002133aacb806633f2003a90193ffd31033c7db499213760a107c56322af8e408a3437a247fe881e00c000d411ff87d00ad07f708804df7f90499f420643be040300a502e0cffc28cfdb7f8547a889a4efe012ede01555805373f061200010e3fa8822a3a7aa090010e1ff850001986fd2c68238d7c222ebfff2a428517fc9ba8410a1f71f44c041257e97c411b32a943297ffffd6190000804d75e700646fe1268cb5ff104ccfcff9208000445cd025064fff4c40ce5fc1be9a60a06959f41125d9df21a1483f1fded08000440da5ff84202501a17fb00de7c02061295c0253e904197a409b4cc798240ffe02840cc6e4128bfc82002175fe9da0021adfcfcc2a1437bfa24010219fec02de721f20a0b1e1050cc027924e7086cfd42065dbea0a2100a657b3a1c08577de82042d61ab1a8fe008b97fa808bb9e8091a5dd54108077c7d86cc024403fc56420a194fc88518f58c28b9e184a8033f3ff4214410a1e9ff6e9016358512bd7c54440093b110c3e3680033698595029012ff94541840888b876c06054c5fe564c819b9f40090801ff67a58611f58220371f4120e0af50952483fd0610217de28040850fffc0150dba624048da7c412d9a924df302a3bbec500))
def rI:aC:= (259,3,8,2490403,102,14,1251,rC)
def rF (i:Nat):Nat:= (if i<1 then 0xa087405c06c402f82ba83696c9af3800020581025c55122e2801908bb4a8000000010279141156dc2ea0bbe97b882043dd877c927e075027bc12c0b20000c016c9d214d30d80000000707200000000814000000000000000d18472f34d40000000141af8c80100a06ee07884c906413302cbad3f3a040001ae40000402d0000804382d35bc90b84270000000000000000000681fc17870980000000bb43422000000000000a2dfe230820e832a09a03edc80b169224400040122194e0c0000287fd0fc00000000000c2fc0066246c696615920d2807000080e051ead5198540000e26380880000000413941e80006b680002444e038214461a9a16103679540003456d853a85c0003c8b402b30923252c21f87c50cc00030140000615e41db244ea872034000083a461b0000000361c800000017177c2d8000713ba28f13bb09e00016c989b88095c8fb40600003132000000000004c17112c62370304c35b963604cc50a20cf77192b6d10e82a50f0631740ab2950001006d63651b4110921c40000000f2980000000000010742430000604d10a3d0b69457501415540fb0317108901300f1ca26ba6b88be0286581671518f8301a3a00000000f1eec2f0000804902c4e42645e5148000044038c3e0620eec85cb8165902a0d5e1c12bbd05e0184c438cb87943ad3ec2048a828787ab3655c4281941faef8ada8b374840002503606e46fd880104d7081c13778dcc2648bd60afae8f62d08a90000850800014517189001e8024846210400000007c65112471b40000000000000000347bc2107f6240000782c299202d9807d850c16ac016aa2590a10aa000000000000000000000000000000a08c449853210ebbae1437c85278ed02f9847369f1019400433e11227d0d60a563100bab4d2307d4428041e866819fd861848f089b0acc252897c044e037053e073a08b90a64000079818df30e02fa09fe0b0531d0591863ad48015abd1424360e4221b80e38a5b0ca72a4841bc7520f4801bc1df04718c7412d064b8c8000142fc44550ab00000003518383346af14c70608008d96be4c4639a02e0003040800000001001810020000001450c61532010002800261020800c000824d0002030000000c00430c020200600000000000108500038300004000100000000000810000000e04004100010d0801800c20000400400000041430010000001400000000010090000020000000010400020c000000000000000b0040020000010000000000000400000001030400010000000000430000000410060001000030870000000000800000000000400c6080080000040002040005082000080001000200000000042040040005080080080001000000040000000041000000040000001080006000001000001000000000000000000001000000000000000 else 0x2d08034fba781186efec4a1842490a80c8847a92012c1)
def dJ (j:Nat):Nat:= (if j<1 then 0x5a2c6b4e344b82353242352c282e4709b5145eb04a292e47c9b4afc2152e1f2e2a66aa76942a4e8cb494622e2e0cb491c9950529240a0c34b454330e5eae4cc9b511e6aa4717ae4989b4ed1a346149b4f20f341467a633e32a2c54130ed41512c234ebe2ae0e9632a5c9b4748215244f344d8f34cd8f152ddeae490e342ca7a831e12e485eae50cab46ad634460f34e654130a02352b89b517142604941317e12e300e344409b4375432ea54b2e5cf150dd62ca9cf34a69a302c4f34c68234c9dc30f354130d669536692e474f34268e344a89b4751b2a2d1c30f30234e9d41517d41312c9b42fdeb4e0e5aa7709b4af57b245cf150e423525e3ac079eae48dda635692e48272a27c13524c13449c1344e811503c135255ba63384b4d544b4e341353110b4662626160e942981352d013475d394318894318d34665332e1c19526c134380db44686349516a832933440863483049522d594060bb4a644b4e390b2b112350290b2a588344547b470972616d0aa69c8344f4834021ca630982e01a1ae2e0834424bb4ad90aa38252a271e241764aa47013509891511552a69c5b4b04b34761ba8320134c9d534661d263145b4a259ae01592e238db4464a34ed81352cc135314134e9cd342705b4af90aca9daae0105b4b0a0ae289e2a48de2e48c934154115359032a0202e2e001522c0b4408fb0c292b040642a470734024334a346b44243b4834534a244344342b4e351328011b0807ff3febfdbfcffb7f7bf6ff6bf5ff5bf4ff4befbe7fdfbdf7df3defdebdd3bfbbf7befbebbdfbdbbd7bbfbb7b7fb7baffafbaf79ff9fb7ef7eb7b777f77b75f5ff3ff3f73ef3eb3bf3bb3af37f36f2beffaff2feefeafdafbef7ef7af6eefedfabfebfabf6beebdebdabcebbeb7eb5eafeaeeabea7e8fe7fe7fa3fe3ee2fd984c15264530549714c15226130548914c15265d20549714815254d205495148152645875013161d4024d875009161d4064d71500985c54024d71501715c1405057050187505405c541501315054065d31501904c5405c531500984c54025d3150192619305c1864c15161930481864c09161930205864c1726093021d824c0816093021d814c1985c530641714c0985c530589704c1315c130485704c0815c13061d624c18558930605624c17258930595624c15158930261624c08758930615604c18258130595604c08758130609514c17254530261514c1964813061d204c18548130605204c172481305c5204c17048130595204c16348130581204c15348130545204c08748130205204c195205305c8814c1532053021c814c17360d105c183440985cd105c530440974c11065c834419161830245860c09760430619710c1941c43025d83041976081064d82041874c01061930041854c01060930041981cc1064073041821cc10 else 0x36285bf610c3eb16a0f78313259a16018b360a9f1020ef08ac84e1493586087710ef811806dc08f490f0c6a2601ae5091c1046648f7d2431b843c342afe64645d2134087bd144b9847522ee8c4dc189c047018f390d40b2e8594b1081edd0b3e0241dec472b4246af906806788830d068cb760514584df0120f2e850c1058f0f0212ae845fa09e01cca15e22d910c023488b22f7a20b6b88720e689161514304a0dbca8c60e8e20d8076910fd81107a90d80738421704153cc4838e04c75c018cfa233c22ea4d147229c443187434d85e01bbdd050c0a029f98a7213bd9053f810ce11201bc030704135d0af090ef113809617a19e1120378896350dbae58d7e021a7f93416538447e035025020fac5622cfe9244cb3f121cd550c7b8864c89013b01d795318f350dd01ba037a03b66826fc0477920b7f311117f8218f421cb2d5070ea9419d9157940032cf021d52c5bc14368113221798506e80d0127f446265d68920dec0680a3e0631c422051e818c991172c18eb8031da118bc40835e821bf00c4f086ce0733429aa12fec110fc119028f818f734260200e30411f80c9b234047fc04859147c0c63a843c721a0e384719239fc10ce05bef922003ffe3641203e90c6650ff58992bf5c4c93f1c110003813ff024e7f081932f1432f4d18f39aa643fe2240373ed140dcfb45df7c91013c18dcad880270dc441c26b480c20266c458909250d2e0e8874ac26092b88420217891a0d54742281b6482c81d0747281a198119450c3dc381a4a5e26c27825823e0d20001d02301746741d4c4443144021780780c17119a25e1755c6c3c25749010c0d501824c2079640e40f813e19f0901b344081825016c0035060181340e81fc01801f8901f81f01a81300bc0bbe2fdd3d87d57ce7cabc77c23bb3b73b43af3aa3a53a079e39a79538fb8c788382f7e378b73b6fb68b6476135ab55f52b4df49345f4273d33a335f3172e72a72371ef1ab13f10f0d304eff6fc2f52f0eebee42e02db2d76d36cfacb2c8ac52c1abc2b6eb0eab6a529ee98294e9168b286282e7ea79672a6ce67262a5ea59655a50a4ba4824463ee3b638e3423062ae2522161e61aa1561160c2086051ff5fb5f8df51f01ea1e45db9d7dd39d09cd9c8dc59bcdb75b21acda91a65a259c59719358f98b98698197c17516f56a563d5d55955154c547d4293f53b934d3112e52591f11ad1811290e90bd061024fc0f64f24eb8e64e20dccd8cd48d04ca0c54c28bd0b88b58b34ae4aa0a58a2c9cc99493c8e888083c7f87a076c7046505c85504dc4703b43402e82802181b81400c80600002353797ae57d433049fb027d634c6141314d634e609b4cf68ae2729ae26deae4b142e3814130f1eae4d18ae0ea2263428952709b4efa924178c34b714152d49b4cfdeae4949b4355b14ad)
def dS:aC:= (203,4,8,5505121,119,12,1118,dJ)
def dN (i:Nat):Nat:= 0x23520a6010e441400000002b21a46000182e001301e1c617a1e0013ac000000208000000001c3062c000c03a1862803620c233810023c068ec35400191ca2600020efa5404820000a12000000224001208c05149e1
def dI (i:Nat):Nat:= 0x178405e10350405c07c1001805c203f01a84000004004c083a83e24100bc3d2400300b8604c035080fc02f1013005c200233ae2400300b8804d00300bc7d2402600b87e2401708002f0170a33be2400300b88006017080981adaa4a4a73952358c21e86607809e3745a561967521434f905364ad238891a83104800bcdb6c54aa6902a5fd24c0a954d2054bfa4a9a40b92a2985779b72819520530cebaa6d3930a8a61e795c971609514c2bbc5caa2b2a40986bb5a7504984c540cfe152b8aa290261f78545715c9204c2f6cdb152a9a40987dd1315c0985c530afd172902e4a8a61ad754da12613054bfa4982a6b8a40a96adda64c49361d40fec2e2982a2902a58eb691a2660730431b6cab4443902985739b42819520530aeb172a8aa690261ed254d202613054a3bc5cb4a40ae098636da5689981cc108f736854aa29026155e6dca0654814c2bb4d9140ca902986f49526855348130
def dR:aC:= (28,5,8,0,0,10,0,dI)
def dM (i:Nat):Nat:= 0x2022120a00481835bb4200000707b100030
def dH (i:Nat):Nat:= 0x390805c1eb5c2b99303f5054d515c57248130e5e1722a571545204c3792549b62a553481309739c42e551595204c35d254cb9481725453083b8c86d0a9545204c31c654db42a55148130
def dQ:aC:= (7,6,8,0,0,6,0,dH)
def dL (i:Nat):Nat:= 0x78001b2d178400008
def dG (i:Nat):Nat:= 0x3507340795054d722a571545204c22671b0e2172a8aca902614748da54cb94817254530
def dP:aC:= (3,7,8,0,0,5,0,dG)
def dK (i:Nat):Nat:= 0x1e0
def dF (i:Nat):Nat:= 0xd41d1505c4da54cb94817254530
def dO:aC:= (1,8,8,0,0,0,0,dF)
def vL:Array (Bits × Bits):= #[(0x840a108bec0006,0xd3584ac0e0a004),(0xffffffffffffffffffffffff24640550c50029,0xffffffffffffffffffffffff2c85b1021f1821),(0xffffffffffffffffffffffff61200154008957,0x503a0ef580c546),(0x4301e824009e18,0x874541086a3a18),(0xffffffffffffffffffffffff000b70212005e1,0xffffffffffffffffffffffff28a2b4371545e1),(0xffffffffffffffffffffffff8880028a0a427f,0xffffffffffffffffffffffff04a7252e0a5a3b),(0x105404001123be,0xd362442c60629e),(0x0,0x0),(0x1a908a001273c0,0x28189ad1958540)]
def vK:List aZ:= ew 41 (fun x => (aU x 0 17,([0,1,16,2,8,256,32,4,64]:List Nat).getD (aU x 17 4) 0,aU x 21 17,0,([7,11,9,8,4,5]:List Nat).getD (aU x 38 3) 0)) 159 0x4001c800519834f401885000c60011c6495e02410c009180017200074002c5002620004e6043f002a0400138005620014c0025900232000660015700014257be82b809b0d7818442186c60c21ca003b000a20759c83a9183ad381d462000f600104a00670008c009b18048718b57805842c26e60120c6eb7907503324bc81201a0051880052974fe0bb002bb6f05d08310af008084024e40108cc025e00050801617000d4000ec00489824f4010850009cc01110017a00002867a70338c6005300006615a720ac468004e000988560f82b580001bc0022100294000356ab2f055284009c00011c925ec09008d5a7a0ac420cf3e06720857b182b870005b40002500073001060eb7a07502c0098b8012a000798028214c3e0a7606493d024213022f8014812f5f817802a1efa10e024eb7d0750125abe82d00806d3803462c4adc024116eb6e07508b24b7012045815cc008180027c000418012c00029a563f82b400805bc0002061e7e10e402eb3f075201579f82b900924fc0908044a7e0244021b3f00d201099f804901485f824002986fc0c201001370002420dbf0068060005d400d1000c6801142257b0120225abb82d0212a9fc1560098eee0c6084097d004010040f8025800958c04838642be120200015d00011161af830880b1cfc18c805767e0ba402373f01b200000f800580b3cfc19c8094cfe0a7000a7630530e4009c180116005180007284afc024014c77e06300a75bf03a805125f809002956fa0aa023217b09002175bd83a810b0dec18408426f6012048016220006c00a60800c8a9dec14c0854e7e0a6402013f00020175b783a840925bc0902044ade0241021b6f00d08109b7804840a9dbc14c20556de0aa102ad5f05610156bd82b010ab4fc1588057af60bc042437b0210210fbd807810bad7c1d44056abe0b4202a75f05310124af8120808dd7c06c4044abe0242021b5f00d10109af80488081d7c00c4061ef610e042af7b05702167af833880aed7c17440402f6000042015f00010169b7834840b4cfc1a480c02b6000242057b002021029f801100815bc0082040abe004200013900023000a70000c5005f800002412f6008042096f004081049f8021008257c01040002c60001c
def t4:List (List Nat):= jB
def u0:Nat → aC
 | 12 => rK
 | 11 => rJ
 | 10 => rI
 | 9 => dS
 | 8 => dR
 | 7 => dQ
 | 6 => dP
 | 5 => dO
 | _ => bi
def t5:Nat → Nat → Option (Nat × Nat)
 | 12 => aL 35 135 6 13 6 3 rH
 | 11 => aL 470 589 6 16 9 3 rG
 | 10 => aL 338 423 6 15 8 3 rF
 | 9 => aL 9 55 5 12 5 3 dN
 | 8 => aL 3 13 3 10 3 3 dM
 | 7 => aL 4 7 1 9 2 3 dL
 | 6 => aL 1 3 1 8 1 3 dK
 | _ => fun _ => none
def zF:aM:= ⟨1407,12,fun j => vL[j]?.getD (0,0),vK,t4,u0,t5⟩
set_option maxHeartbeats 0 in
lemma zY:aV zF (aI z7) = true:= aX 4 1
def z8 (j:Nat):Nat:= 0x965808769465755094657540946575309461755092462752855829948558298485582975855829648558295485582153824627738246275382462752823627738206276281756661817566518175664181756640817566206567401065614010656040106557417565574153655141856537501065374070653740106530401056854187568541655685314356784170567640705675419056754180567541705675316056752150560640805606407056064060560640405603408049568574495685734847668442482343424823324247233242452343424523324176809041768070318412323154128526783191267831212678311026763191267631212675412126184171261841612618412126083191260541812453237314678090146780101461801014608070146080501460801013451272
def z2 (j:Nat):Nat:= 0x82306318240152300810252493100532008015021683021531076255694810653000762326318002751007620569180038400076202691800762000750208924604653107361519420050210070352810670142300703228196702845006783004321004311067136584900463000670365849004830006350690857005460063406918570054600634069185700485006340691857004350063200786120761310632007861206502106320078612057021063200786120541810632007861205402106320078612043021063200786020850210632007860207502106320078602065191063200786020650210630531470204312006012648130040260054077183620671200540771836205217005267091485008530042654735820407300426007658201073004260076582010630042600765820096200426007658200862004260076582007510041730756930017300370208612004017103407907562037050031569275130642300307214263002140003016947530075400030121426300214000301214263001830002765068950056411027600689500564010276006895004530102713352490039400027133524900384000271335249003450002710352490034500025800543290032410240691856207512002406918562065120024069185620641800240671856204716002106928531075320021069285310642800210692853105726002106928531053260020569485300754000205694853006840002056948530064380020569485300643000205694853005320002036012780029611020360127800236110201694853007540002016948530068400020169485300674000201694853006540002016948530064800020169485300643000201694853005730002016948530053260016720598600576010167205986004650101620263180032610015360168920045110132681962007621001326819620068210013268196200651000123683962005428000765826713056230007628269170451200067283674206743000621463581040610006214635800305100054601687200346100346006875004571003284135200402100032681962007621000326817620076210003268176200659100032681762006521000321413520040210002674730820407300025683764207643000256837642065320
def zJ:Nat:= 0x241408410842110c0300c03
def zI:Nat:= 0x11489414e86824914642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rV:ba zF 5 0 1:=
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x43) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rW:ba zF 6 0 3:=
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x2c1125) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rX:ba zF 7 0 7:=
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x342d2111268edc) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rY:ba zF 8 0 28:=
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0xc392711360349312e3522002836140833a799cededfcfa894bde2bc) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rZ:ba zF 9 0 203:=
 (@ak zF 9 0 96 107 (@ak zF 9 0 32 64
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0xb7bfcd9fa6b889a5b8cfa50098c8918700000000000000000000000000000000) rfl (by decide +kernel)) (@ak zF 9 32 32 32
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0xcfd59c9d84b89aa3c5b89ae1a2cc009acf9e00e0aba6a4dba5c6d89fd0009ed1) rfl (by decide +kernel))
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x36441a4c3a409f9f9f9f9fd992839fb88a009f9fa3a3d48b009fb4b290a99bb0) rfl (by decide +kernel)))) (@ak zF 9 96 64 43 (@ak zF 9 96 32 32
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x363638481036363624122438242f15383b2b1f1332194c3638301c3c0b383624) rfl (by decide +kernel))
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x638384d0d45381230171d41023836003c060f242016183e4b4718120b241c36) rfl (by decide +kernel))) (@ak zF 9 160 32 11
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x5363715073a361e0b38361b1538123606363b060923361204013606004c3829) rfl (by decide +kernel))
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x3838382a1238123800000a) rfl (by decide +kernel)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sC:ba zF 10 0 259:=
 (@ak zF 10 0 128 131 (@ak zF 10 0 64 64 (@ak zF 10 0 32 32
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel))
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel))) (@ak zF 10 64 32 32
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0xa6af00009fa60086c3b3c49fa68db6d6e500b09f9581c0a08cc0000000000000) rfl (by decide +kernel))
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x86e381b8d786889fc3a681a686beaa93868600b1869fcbb000c9b5a6b19fbb86) rfl (by decide +kernel)))) (@ak zF 10 128 64 67 (@ak zF 10 128 32 32
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x84ca81d29586ca00b8b200cab000d300ca82d39fb8a6b9c3ca869f00dae485ae) rfl (by decide +kernel))
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0xca81d286aa9f86009f9f86c0a19facadc7ca939f808fa68db0ddb6c1a6939f00) rfl (by decide +kernel))) (@ak zF 10 192 32 35
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x364d3f36060036360f12000f0f4d4606ba9fb8b8b8879fc29686979f00b09f00) rfl (by decide +kernel)) (@ak zF 10 224 32 3
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0xf0f000f4e4600364d423d36420036004a060646063d0b4d0e0f4200000e4d) rfl (by decide +kernel))
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0xf0006) rfl (by decide +kernel))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sD:ba zF 11 0 48:=
 (@ak zF 11 0 32 16
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel))
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sE:ba zF 12 0 6:=
 (ac (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel))
lemma zS:bS zF 12:= by
 intro k hk
 interval_cases k
 · exact as zF 0 0
 · exact as zF 1 0
 · exact as zF 2 0
 · exact as zF 3 0
 · exact as zF 4 0
 · exact rV
 · exact rW
 · exact rX
 · exact rY
 · exact rZ
 · exact sC
 · exact sD
 · exact sE
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma jX:az false (au 1407) 12 (vars 1407).toFinset:= iB (q:=383) (prior:=aI z7) (ag z7 zG) (by decide +kernel)
def jP:= aq z7 13 [(9599,91),(17343,60),(9711,92)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xK:Known false jP:= aw (m:=2431) zG
   (af (q:=1407) [2,1,2,4,1,1,2,8] jX
     (aW (g:=zF) (i:=0) rfl rfl (ag z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def jF:= aq jP 13 [(28143,93)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma xA:Known false jF:= aw (m:=1407) xK
   (af (q:=1407) [16,4,2,4,1,1,2,8] jX
     (aW (g:=zF) (i:=1) rfl rfl (ag z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def qZ:= aq jF 13 [(54143,0),(64447,94),(44015,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yN:Known false qZ:= aw (m:=54143) xA
   (af (q:=1407) [2,1,34,4,1,5,2,8] jX
     (aW (g:=zF) (i:=2) rfl rfl (ag z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def qV:= aq qZ 13 [(44927,95),(47999,1),(53119,162),(58239,4),(69503,163),(58303,24),(60351,60),(69567,94),(42991,19),(60399,164),(69103,165)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yJ:Known false qV:= aw (m:=44415) yN
   (af (q:=1407) [16,1,2,4,1,1,2,8] jX
     (aW (g:=zF) (i:=3) rfl rfl (ag z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def qS:= aq qV 13 [(43903,0),(46463,95),(48511,1),(51071,91),(43455,47),(43967,89),(54207,166),(58815,60),(49647,19),(51183,92),(54255,8),(55791,12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma yG:Known false qS:= aw (m:=43903) yJ
   (af (q:=1407) [10,1,2,5,1,1,2,8] jX
     (aW (g:=zF) (i:=4) rfl rfl (ag z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def q0:= aq qS 13 [(42879,0),(60287,4),(44991,47),(69615,93)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma j5:Known false q0:= aw (m:=42879) yG
   (af (q:=1407) [2,1,2,4,1,1,2,8] jX
     (aW (g:=zF) (i:=5) rfl rfl (ag z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def n8 (i:Nat):Nat:= 0x16ad2728c1ee6b16a4a0e629062082fff
def n9:aC:= (1,0,5,0,0,0,0,n8)
def t8:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffff8278ca9,0xfffffffffffffffffffffffffffffffe078829),(0x8c5796,0x1884792),(0xfffffffffffffffffffffffffffffff819b865,0x31b824),(0xfffffffffffffffffffffffffffffffe1200db,0xfffffffffffffffffffffffffffffffec400d9),(0x4205b12,0x1385302),(0x140617c,0xf06154),(0x808260,0x6740060),(0x430380,0x70e0280),(0x303fc00,0x10b9c00)]
def t7:List aZ:= ew 38 (fun x => (aU x 0 17,0,aU x 17 17,0,aU x 34 4)) 23 0x35cb7ee440d54dfaa1035b3ded810d60f7b004361eff0e80d75bfbaa035a6fed280d67bfb3a0358efec680d5ebfaf203576feba80d5abfad20355efeae80d55bfaaa0354efea680c00fd80012c03dc0011c007f80403003fa0002c00ef800834037e0040d00f780043402fe0080
def uL:List (List Nat):= [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def s8:Nat → aC
 | 14 => n9
 | _ => bi
def rN:Nat → Nat → Option (Nat × Nat)
 | _ => fun _ => none
def xd:aM:= ⟨1535,14,fun j => t8[j]?.getD (0,0),t7,uL,s8,rN⟩
set_option maxHeartbeats 0 in
lemma k4:aV xd (aI q0) = true:= aX 3 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma tZ:block xd 14 0 1=true:= by decide +kernel
lemma tE:block xd 14 0 1=true:= tZ
lemma s0:bP xd 14:= by
 intro k hk
 interval_cases k
 · exact (rfl:block xd 0 0 0 = true)
 · exact (rfl:block xd 1 0 0 = true)
 · exact (rfl:block xd 2 0 0 = true)
 · exact (rfl:block xd 3 0 0 = true)
 · exact (rfl:block xd 4 0 0 = true)
 · exact (rfl:block xd 5 0 0 = true)
 · exact (rfl:block xd 6 0 0 = true)
 · exact (rfl:block xd 7 0 0 = true)
 · exact (rfl:block xd 8 0 0 = true)
 · exact (rfl:block xd 9 0 0 = true)
 · exact (rfl:block xd 10 0 0 = true)
 · exact (rfl:block xd 11 0 0 = true)
 · exact (rfl:block xd 12 0 0 = true)
 · exact (rfl:block xd 13 0 0 = true)
 · exact tE
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma vi:az false (au 511) 14 (vars 511).toFinset:= by
 have h:az false (au 1535) 14 (vars 1535).toFinset:=
   ed (g:=xd) (i:=0) rfl rfl (ag q0 j5) k4 s0 (by decide +kernel)
 have e1:au 1535=au 511:= by decide +kernel
 have e2:vars 1535=vars 511:= by decide +kernel
 rw [e1,e2] at h
 exact h
def wO:= aq q0 15 [(511,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma s2:Known false wO:= aw (m:=511) j5
   (cu (hints:=13438558465) (by decide +kernel) vi) (by decide +kernel)
def l9 (i:Fin 9):Nat:= [4,2,1,2,3,0,1,2,3].getD i.val 0
def fu (i:Fin 9):Row:= Fin.ofNat 512 (1 <<< l9 i)
def eY (i:Fin 9):Row:= Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< l9 i))
set_option maxHeartbeats 1000000 in
lemma hB:
   (∀ i:Fin 9,bit (fu i) graph ≠ bit (eY i) graph) ∧
   (∀ i j:Fin 9,i ≠ j →
     bit (fu i) (inputs.getD j.val zero) =
     bit (eY i) (inputs.getD j.val zero)):= by decide +kernel
abbrev eC:= Nat × Nat × Nat × List Nat
def qF (rows:List eC) (base:List (Nat × Nat)):=
 rows.map (fun e => (e.1,e.2.1)) ++ base
def q3 (base:List (Nat × Nat)) (e:eC):=
 (aI base e.2.2.1 == e.2.1) && mB e.1 e.2.2.1 e.2.2.2
lemma vZ {u base rows} (h:Known u base)
   (cert:rows.all (q3 base) = true):Known u (qF rows base):= by
 intro e he
 rcases List.mem_append.mp he with hm | hb
 · obtain ⟨r,hr,rfl⟩:= List.mem_map.mp hm
   have hh:= List.all_eq_true.mp cert r hr
   simp only [q3,Bool.and_eq_true,beq_iff_eq] at hh
   exact pe hh.2 (hh.1 ▸ ag base h r.2.2.1)
 · exact h e hb
def wZ:List eC:= ew 30 (fun x => (aU x 0 17,([5,9,8,12,13,11,7]:List Nat).getD (aU x 17 3) 0,([94,91,478,127,251,95,255,3579,28143,18911,17405,4927,17343,17403,17151,9599,2239,1375,1343,11742,1725,6847,1119,1727,2751,2237,18814,2079,2367,2429,27127,7038,11453,48094,42679,42591,44927,42683,44799,46455,58335,58239,68863,42711,42751,42623,42879,58623,43479,58047,54143,43647,44925,44223,44733,64447,44221,64191,44155]:List Nat).getD (aU x 20 6) 0,([[48,33,133,118],[81,130,118],[32,49,128,81,116,100],[80,16,33,50,116,131,100],[32,83,116],[16,82,131,100],[128,49,100],[48,129,82],[16,32,48,128,100,80,116],[128,81,32,49,100,116],[80,129,50,116]]:List (List Nat)).getD (aU x 26 4) [])) 187 0x228721fe8a6487bdb5b21ee9eb487a9b8521e62e6c7fb979b1fe7699c3ff86130ffc9b1c3fede130ff39af43fc6a250fb96a9c37f92870df73e143798a990dbfad6c36f4778f97f6b1baffa666ebfb284bafe5a24ebeca84baf79abcebdc0d93ad6c272e5be9a9b8fedf5ae3bd4a9b8bfd6f6d9f799cb67b6a86d7fe5a9b5fdea98d7ef3a635efce86d6ffaccb4fb4b32d3be2b1b3ff9e66cffd884b3ff1248cfef4d0b3fb42c6cfdf28933f38ae8cfbf08933d7a332c7cf1ca31efcaa6c3fe9a1b0fde698c3ef6c6b0fb9a86c3df6a630dfcaf6c1fea9cb07ad704c0fb1bdaf7eca66bbfe8ba2efbe2c6bbdf8b4aef3ca48bbbf1b1abfecec6aff71af2bfc6a48afef1892bdce612aef7aa9ab7f5e86adfb8a9ab77c298adbf7a62b5fc286acff19caa6dc666a7fb484a9fcd65ca7c719229efd634a77358929b9ce12a6df079a47f998a7fee8259b7f8c766dfd61d9b7ed6046de6a4a9b6bcd8a6be714c927f149649fb422125fc604495b97991ff50d643fe17c90ef94a637fe3358dff54c837ef2510df994d637dfa568def64ba376f2628d7b9de633fe83e0c7bd1d231ed13e0c6fe90a31bd4728c6bc9bc31ac1258b7f54882dbf1688b6f990a25ee5650979958a21e723987ff88a61ff723207fbd57a1fe793586ff995a1bee13206dfe89619fe122067be16419ce84a865bc0d613fd82984fee0d613f775684ef60c8137f15104d6d1320df3822036fc52a0d3f346832fc8f809bf742826f54f8097f73981ff68d607f773581f7dcc807bf22e81ebdca606ff725817ee07605f76258177c888057f11d813fc86601fe611007e942201f9311007d502201f3a0c807b643201eba040079241001e20110077544401d780c8073e00001cc8040071883201be215006f040001b870c805f54320177515005cd400017161500579810015a5040054d04400fe008803dd03200ef3088037c81000bc104002e40000097
def pri:= qF wZ wO
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nI:Known false pri:= by
 apply vZ s2
 apply df (d:=6)
 simp only [cA]
 repeat' apply And.intro
 all_goals decide +kernel
def moY:Array (Bits × Bits):= #[(0xffffffffffffffff0247102040c820c0830811,0x3f03f81ff800001f8000),(0xffffffffffffffff04c1040881096109041223,0xffffffffffffffffffc000000007e000007fff),(0x888245902104218288206,0xfff800001ff81f8000),(0x111008902432803260844c,0xffffffffffffffff000000001fffe007e001ff),(0x302182060608060410c08,0xffc0fc07e0001ff8007e00),(0xa004820208841484826190,0xffffffffffffffff0000000000001fffe07fff),(0x4420410491010901141020,0x7fff81fffff8000),(0x280820430a040604082080,0xffff0007ffffe000000000),(0xd030c38414021802104140,0xfffffff800000000000000)]
def moC:List aZ:= ew 47 (fun x => (aU x 0 17,([0,1,16,128,256,8,4,2,64,32]:List Nat).getD (aU x 17 4) 0,aU x 21 17,([0,50,16,64,18,128,138,276,32,69,258,136,8,384,130,36,256,4,1,68,272,9,2,104,20,48,96,385,129]:List Nat).getD (aU x 38 5) 0,aU x 43 4)) 387 0x800058c004394a001e900a0a80016b0010a50005c580114a3009c3802154001cc10019280038c4002951806a1c002ad80031a80601b8004e9008834401c6a01106b0073040060cb00b0b00049c000f30008638002ae000a8700c6b0060a6e000da800129c0bbc705d1c38243d41201570007a80002ae057f882b839c001f100007401756e0bb488029b9c14e3100715ec38c0a00cebd8678140002bc000a1802bdcc15d190053b9829a320013730094640002e60008c80005e40010d0000de00010e00e35b371124015ab66ac24801256cc90490009ad98489200015b000124021bcc50c0980367981b013005df302e8260001e600004c814dbe0a72090003bc0022136725ec3940240017d0004148002fc00081902a6dc150912072df03910640d3be06920c80877c04241900b6f8058832063e78318c240ebde07510c8003d60001490367b41b0252069f683484a4031ed018094821fe610e0c90037cc018192000fc80001a4049fc02401cc15d7b0ae02a533af619c01606b5f835d02c00cbf006a05800d7e00740b02bcfc15d8160249f812302c00d3f006605819ebe0cea0b02ed7c175416024af812282c0a76f0534858026de01290b01b6bc0d8a16018d780c142c0e3bd071215806f7a03642b004ef4024856053f3829862c025e70120c58043ce02018b0437b8218236061f7030847010cff0868060093be04820c00df7c06c418034fb81a0230049fb0240260093fa04802c011ff408c058061ff0308070091fe04800e0067fc03201d033dfc19d01a090f784804100016220046ad802c2c009850007888001ac400a60802819c01616000c3819dbc0cf21702bbcc15e18fc002f480401c0af630574e3814f8e0a638700077000046e087f8843839c0ebf807503c0181f60c104802baf615e0500215ec10c0a0000bd000814021f7210e468035f989ac131b002f4800024000df000904818efc0c68190006f8000832000e78000c2402dde01610cc57ab66bc209033fb419c252053f982983240cffc06701cb177cc4ba01a52baf615c016071af838a82c0056f002485800af600484b001ebc00ca16000d7800142c11fe708f0c5821bce10c18b007f9c03c31600df700684700acff05680601d7be0ea20c02b77c158418009fb80482300e3fb07102600dbf606c04c004fec024098056fe82b00b0043fd021016005bfa02c02d02bdfc15d01a056bf82b2034001bf000206815fde0ae10d0067bc03021e000ff80000100015830013b5802e2c0088640073040024fa004ba00021f201cc1000140001f60010480392f61ca0500007f00040600cf5e06750c01d6b66ea2480007d4000153260f313002240ebf9075034c1c97b0e402a5392f61c801607d5f83ed02c0a73f05360580267e012c0b03ad7c1d5416000b7800242c06be70350c5804bdc02411c010bfc08601805def82e883010ffb087026021bfc10c01d030dfc18500d900a6080209f000e3500803821ff010e07800156cc08490075f603a84e00b5f505a05400dbcc46c099043ff021c07607dde83e90ac10fe70870c5806bdc03411c0437dc218118056fd82b01300ebfd075016804afe02480d010efc08481a018df80c10340c3ef061086803fde01e108043f98a1c13001bf310d8262e0097400004d8017b001009000778000432000f680004a4001f30000655403cc40000b0022fc0128160049f802302c031bd0182158033dc01811c038bfc1c601805aef82d08300aff7057046019ffa0ce02c01b7f40d8058090ff048007410dbf086206805b7e02c407a0038d40008f300dc380006c0053f002605821b7a10c42b0026f401085805d7f82ec0300e3df071106015ff60ae04c0037ec018098057fe82b80b40f97f07c40681f77e0fa40700035c00251005ead9af09200bbe625d04cc803cc40008c01b7dc0d8118087fe84380b0037fd01b01601affc0d601d0097bc048208000f010003e0019e620c04c8001ee00108988056cc004130005ec0000ac000bf000a058243dc12011c02efdc17411800fff007807410f7f0874068036fe01a80d004dfc02501a063df8319034037ef01b084016ab66b424940056cc00092c00f31000069e015b30000581afdc0d611b01ffb80fc23a069bf834a0340ebbf07520681af7e0d640d0036fc01881a067f78338418a005e90080bb802e2c0008802a75c150510000eb8000a200a75b3531240012b660824c043fdc21c11a05ddf82e901da005e90000c00017b0010296367989b0036009bd804a12c11fee08f08e821f7e10e40d02efbc17420eb00b8b0000a0001fa00002d28017b00000d00c7bc060216056bd82b213001bfe00d00e8012fe00880d038efc1c481a056df82b1024001fc00001d814ef60a684d033efc19c810900dc38000250b55b35a0258012be008a0d02befc15c81a06bf783584200c1e626004c0063cc4300980397e81c80b070071a800020c01716000060087fc04201d038dfc1c50100545ec2a40b00d9f706c0468176fe0ba80d0125fc091016057bd82ba12c0cfee06708e000dfe00700d0026fc01081a036f781b0418601b870002e00dbfc06c01c0067f803003a075bf83aa0340b57f05a4031402e2c000a7200730400418003ef8018830007f70030460093fc04801c001ff400c04c20071a80412c0015f000505806fdc03611c00dff806c03a072df8391018600974001440002b66002470007e00000fa086f7843042c0bbee05d08b08039820022d03afbc1d42180727f83940340abbf0552058063dc03011c0013fc00a01a06cf783604340c1ef0600840003cc40009c00b7f805803006cf313602740c77f063406017bf60bc04c02eff817403a087f7843842c001e70000c404039820000b0025ec011096000bd8002134007bf0032068002fe00080d034efc1a4818002fd8010130001fe00000e000bee00408d0007bc000218000fb80002340bd7f05e4060003f600004c00177c008418067ff033806c001bd000216818fde0c610d0015fc00901a069f7834842c001ee00008e014fbe0a620c00077c000418060ff03000700a7fb053026021ffc10e01d02afbc1542180537f829c030001fd000016014fee0a608c0003fc00201a055bf82aa0300ebfe07500e814f7e0a640d029dfc14d01a053f782984300a9fd05401681537e0a840
def moA:List (List Nat):= uL
def nH (j:Nat):Nat:= 0x30a206102004e8a0e8c6c0b2eb28da986d9ada8efa1d3d389edfd2bf251de8cb5cd425c1206ddb62a531480c954d524c120661814c53048152605314c120
def gA (j:Nat):Nat:= (if j<1 then 0xad8b0aad8b06ad8aa6adc30aaacb30a6cb2aa6cb0aa6c96aa6c94aa5d302a1ab0299c3029603028ebb926ebb906ebb306eb9946eb9926ed306683b8534438b3212cb300b8b291b012502a524d34f20d34320bb4f1cbb4b1d4aa51cb35114bb4b101b83051309050aa7057260fcbb52f8bb40f94260f80b90f4e302f40b90f0ea60f00b90e8b350e4b340e53b02e53260e4bb70e0bb6ae0bb40e14260e00b90dcc30adceb62d87b82d5e994d26186d26b30caa2a6c92b02c48b8cc2a392bea382bc9382bea360bea342be8330bea322bea300bea220bea192bea174bea152bc2196b98172b02390ad538cad6b88ad7386ad72a6ad7330a97192a9bb6aa69330a6c2a4a52342a1b262a0fb429d53309d92629d134299a262983382951b4295733095db0291f2a28cbb708a0aa2880b8a840b8a800b8080daa480c2a67c0b8a78d2a6780b90740b8472a3066dcb666ab34a6ab39266b38666b36666b34666b32666b30666b17464bb6a600b8a5c5b8a58e35054a36a500b8a4e4b02480b8244a30244c39640c3663c738639636638cb70340b903223502c4b96284b9026430424539020db461c53861a2aa619e3461652a615fb461272a6121b460c73860a2b460a3346067aa606439402838a00299700ab6ee25b30a4119498038247ff8ffd3ff0ff6bfd8ff4ffd2fbf3ef4f7f3dd3f72fd5bf3ebcf6f3d3cdbe7d79f3e7bf9ebe76f9d7e6ef9afe67f97fe5ef95fe3fb8fbe1ff7fadfe37f6dfd37f2dfbb7e6defb7b6d7fb5fcd7df5f6d7bb5dbd6ff5bed6ef5b7d5f7577d3fb3facfdb3eecf7b3d7cefb1ffc7fb1fdc7ef1f7c7bf1dfc6ff17fc4ff0ffbfdafd3bedadfdb7daddbaffa9ffa7f69fba7de9efa6fe7f69dea5fe8ffa3ee87fe1fd2a563505602a542505606c8a9505606c8a9605306cda5245302cda4661206d8a3661206e99564d206dc93645206d893645206c553605206cca9605202e9545c1205cd425c1202e5a154d206d8a954d206c4a954d202e5a54c5202e1a54c5202e9944c5206dca94c5206d8a94c5206d4a94c5202e9984c1202cd984c120661814c12054d814c120549814c1206e5804c1202e5534c12054d524c120661514c120609514c120605514c1202e5514c1206d5314c120605314c1206c8a54c1206d8954c1206d0954c1206cc954c120661a724d2069d9524d206999524d206c8a960d102e993609106d4a9609106cca9609106e9954c9106e5a54c11054d52481106c951481105495148110659a2604306e9926043068991604306c55364420661a3604206e9936042064da154c202e99854c20655a3608106e995608106c99560810651a3548106e993548106d593548106a1935481068d935481068d92548106e582548106a58254810661825481065d825481065982548106558254810651825481064d8254810 else 0x3be9190000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c2305002fffec004058000000000000000000000007ffcb004a5200000000000000000000000000c0081c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fff619148001ffc827bf200584e0ffbc0c200ffc80600f84dbc8c807710e102c029d632d006e32506181d0177035c0f361415300380572c00037f091a14989ae8940cc114815b81a749f0d3815ae10b841d133c21d08b411015c03900d3c0101e40490113a0be81bc00d8dafb5b696d1da1b3f676cdd99b2f656c9d91b1f636c5d89b0f616c1d81aff5f6bdd79aef5d6b9d71adf5b6b5d69acf596b1d61abf576add59aaf556a9d51a9f536a5d49a8f516a1d41a7f4f69dd39a6f4d699d31a5f4b695d29a4f49691d21a3f4768dd19a2f45689d11a1f43685d09a083d97a2f25e0bb9762ea5d0b99722e25c0b51692d059cb31652c858cb11612c057caf15d2b49652c2574ac9552a2534a49452824f49c9352624b4949252424748c915222434849052023f47c8f51e23b4748e51c23746c8d51a2334648c51822f45c8b51622b4548a51422744c895122234448851021f43c8750e21b4348650c217422c3204103c0023b0f30f30f2cf3031881930cf2a508f350fd7b06fd5b22f99a20f86392ec6b80ecf172ecf306ddc364cdd366c9d172c89b82c2ab02bd8972b6d364b29b04b2d2a4b28972b18b90)
def gG (j:Nat):Nat:= 0x6000005c000000000000000080000041000000000000428000000000000000000000000021ff0042000000002c0000080000000000007a03000000001
def gB (j:Nat):Nat:= (if j<3 then (if j<1 then 0x13747209b53804dc9bb864ca24aa65151b2272ecb91186588813743e71a21f3ad28f1d6887813743829b11c2ccc0d026e860db262a09ba142cd40a022e85043702425b31112dc081c6a040b3301c5d970e30cb071965438d3281c65ba0a62d9051b6e8201374106da30838d1839765c14c32c0a69940536dd01026e809836a046da80236d1811c6a004e3460225b90038d4802966001632e00b9960062ca803365001ab2600fd748002db3d016d9b22aa6c1215227025d10002e813ffdffdffe7fefff5ff8ffbffdbfebff4ff9ffbffddfeafef7f6ffb5fd8febff4ffa5fbffd7fdffefdf7afb57cffdfddffeff77f7bf7dfaefbf7dbbe7defef5f77fbb7dd7edff6efaffd7be7ff3fb9f7bffdff6ff77f7bf7defeeff6ffaffcffe7fb3fb9fbcfbe7bf3bf9bfcbfe3fefff7febfddfeafef7f6bf75efef7d5ffaff57f6bf75f7adfd5fe7ff3fe9fbc7fe37f17f69573581655c56058d71581715c16058d70581655096058d4158142505602a5415819864530655914c192645306a5814c152605302a5814c1a824530694914c1a224530660914c19524530648914c1a46612068598480a366120661944819864d2065d934819564d2026193481986452064d9148153645202619148093645206a58448195611206a581481986052054d81480a9605206898048131601206a174481985d12065d73481935cd2061d73481985c12064d70481845c1205cd70481715c12055170481535c12054570481425c12050570481a954d2068553481a054d2065153480a954d20695434819550d2061143481a75052066141481955052065141481845052054d41481a94c52069531481a04c52065131480a94c5206a130481a54c12068930481a14c12066130481954c12064530481824c12060530481804c12054d30481524c12054530481314c1202a530480a84c12029530480984c12025530481a32612068498481a824d2069c93481a624d2069493481a124d20660934819524d2025493481a564d10689934419864d1068d9244198649106559244193649106a583440a960d106a582441956091064d82440a96091064d8044131601106a552441935491060952440a9549106a532441a54c91065532440a94c91069530441984c11060130441534c1104c530441a84811069520441a34811066120441954811064d20441854811060d20441804811054d2044152481105452044150481104c120441a8644306a5810c1a26043065d810c19660430649810c191604306859808153644206a581081a3604206618108193604206a553081a854c20685530819854c2064d53081a564c106a192041a5648106a582041a36081066182041976081065982041956081065182041936081064982041a95481068d520419754810651520419354810649520418254810 else (if j<2 then 0xaa4bd48b95e6e5caf522d57a914abd48955e28dc2e946d570a364b851b15c28dc2d946c96ca362b651b55a28d9ad146c5693b42b451b85928d9ac946c5653b42b2ed98594898ac056cd5d3262ae81815642cc2aa1655550b02aa85515544cc2a226555112a2a87d985346a8a9856e1482b6aa47d98523ecaa9266054932a2a47da85118dc281f6a140fb4aa07da84e3ed4269f69534fb50967da54b18dc241f6c91cfaa48c7db3453ed2a29f68d14fb408a7d95453ec9a29f6e9106374887dba4318dd218c6d50cf9748631b5423ed2a11f68508fb40847d534218d9209f68cfcfb407e7d933f3edd1f0c6e8f863707c7cba3e72dc9eb96a4f5cb267b29533d725c9e9f6d4ecfb50767da53b3edc9d056e4e8fb30747cb93a3edd1c8c6e8e46370727da8393edc9b856e0dc2b626e7cb93718da9b0c6c8d9eb026b495335a4989ab76e4d1bb30691d52346e5c9a116d4cdbb306615b3320adc18a76a0c4fb30629da83018da97bb660b9db705a31b82d76da96bb6a0b4fb505aeda52d3ed296bb660b5db2a5aed852d28dd16146e4b0a3745651b92b76c99555548a8a3745215ba2928dc948c6e4a4a370532d8529a4c194d56e4a1cb725155b828aad994556a0a12b505155a328aacc1439660a2ab2650e59328aac1944a54ca2bb744f5db327aed193d764c9ebb064f5cba274ed4133b66099db264c51b5254ed412bb6609692a64b55522518d9121f6c88cfb44467db9220ada912d6e8856b4442bd52203edd0f8c6e87c636a3e7da51f72d10fba69479d3443ce9521e18d98e9f6e87063743831b81c74d88e1f6cc6cfb46367d531b3edc8d056d4695b4632ad53193edd0c0c6e860636a307da5186ea98c1f6e05cfb622e7da8173ed08b9f6e458fb722a7d98154cc08a9f6e850637428ada8146ed409b76844dbb7024ddb21272da88b96cc45cb7020e5b31072d4081f6a040fb6a1e7db30f3ed2879f68c3cfb721c7d950e56d286ab68c356b4a18b5a30c5aa9862f6942d7b4616c9ba0a3edd050c6e829936614e5b20a64d2853268c29917414d1a50968d184b454c25bb741031ba086eda840c6d421bb4a10dda3086ea984396d41dcb4a0ee5a30772a9839f6cc18fb460c7db9050adc02b46a00da34606ddba023edd010c6e809936a04dda8023ed4013768c09cb7002e5a80172d180b96e401cb520095a30072c9804a54c00c1536268a9b004d9d7826cabc13755809b2a906d9d3882ce883b6d4009ba9c0cdbcb076da5813672008b98d085d41c05ce026284fe61b67a0edb3d026c5e81172f208b976045cb7822e9b4336ed861b66c0edb36026d5b0f174ced8b36754cc318b6e58a32a6c02cb95f20daaf50605789364b635b6591eda2c906cd64bb30aa6198542ed3a8186994013749e61a64f04d923022e91011748609b54204d9a1026ccf else 0xc34db2612ad930d36c5869b04c34d8161acdc30566cd82b362c1598160aca9b0564c582b170c165b85fb2d9afd96c97ecb04bf64985f50caac28545614362aca1985650caab286055942a2aca1985350c0a9bc60541e2a498f1534a78c1a4bc61521e2a48ea1534578a822bc4c115e37488f1b34478d1a23c2e911e34a86f1a14378d021bc54905434480f1833f50c19fbc4c0fde3747cf1b83e78d41f3c684f9e3407d59b93dacd99ed66c4f6b3607b59a93dacd19ed6684f6b3407b59933dac989ed64c0f6b1727af1853b50dc9d286e0e9433074f1ba3978dc1cbc6a0e543046ea1813778a91b59548d69b70694db234a6d89a53608d29b02694d8233a6a919d9614c2cb0a5b65ba2cb2dc96596ccb2cb745765b92bb2da95d9694aecb2a5765532ab2dd14a86e8a6cb7252f1b929b2dc14956e0a6cb605365a82950d414d9660a5e3305364ba29b25c94d66e0a2b36650f1522378da8fbc6e871e37038f1a81c78da8c3c69461e3022ef1ba0a78d9853c68c282b616e7d98b77cb2da3e58ed0736366f973b31cd8d943596c0fae75e7da2ab3e51559f2a6a923674e7d98a746a953856d698fb314c7d95a63ed4529f6a290fb4b487da8a33ed2d19f68a8cfb4f447da4a13ed1d09f28e846363407da7a018d8cf8c6e274fb513a7da19d18dacd8c6c66cfb4b3631b99818d9cb8c6e258636b2c7d87953edd4a0c6c650f975287da3933ec9c99f24e4d5b2724ac9392185cc8856ce40fb27207d30900ad9c7856c63c29751c30b98e18d8c62d64e2c637114b5878a18d9c4146c62063631051b88728d8c3bb6621e0aeb0e51b98682c9c2c1612160b27090584849ac241946e608a361052d548228dc40d566202aaa70051b37f9ac23fc15cdfda168fc7da97d185cbe9f2a5f46372f87da97c3e54be1f6a5ec736cf431b17a3ed4bd1f6e9e06370f031b17868cabb8c6ddd4f974ea7dba7418dc3a1f2e9d1a32ae6d1957218dcb89f6a1c1a168e07ca8703e52b81f6e5bc2b72de7da96f3ecc379f2e5bc6172de7ca96f4ed43727695ba9326dc9ca96e4e543727295b8fb50da31b86c3edab60c6d5b0fb50d87da06c3ec2b61f541b0f90ad8ecb96b4e54b5a76a1a9d972d4ed98694ed43427695a1db30d1495368aaa9343b2e5a13950d09ca56876d9b3bb6c59d3974ceecb567a459b3bb661993974cced9865a4a9b2d5549953b42c8ed986428dd31946e58deb30c6f58263a4a9b1d55498ca172c651b2627ac0b1524c58a9372c231b961a4d930d26c5869360c31d5261a45cb0b72e5869152c355ba604add30556cd809b62c155b060aad4305566181cb30c13d536094a9b0552e982a952c154a860aa4c30146e97ca372bf49b35faad92fbb6617e5b2abf5d815fa4a9afbb2e57ca172bf49b95ea4daaf116d57a934abcdd985ea4caaf516057a7)) else (if j<5 then (if j<4 then 0xd65ad969659d965658d961657d95d656d959655d955654d951653d94d652d949651d945650d94164fd93d64ed93964dd93564cd93164bd92d64ad929649d925648d921647d91d646d919645d915644d911643d90d642d909641d905640d90163fd8fd63ed8f963dd8f563cd8f163bd8ed63ad8e9639d8e5638d8e1637d8dd636d8d9635d8d5634d8d1633d8cd632d8c9631d8c5630d8c162fd8bd62ed8b962dd8b562cd8b162bd8ad62ad8a9629d8a5628d8a1627d89d626d899625d895624d891623d88d622d889621d885620d88161fd87d61ed87961dd87561cd87161bd86d61ad869619d865618d861617d85d616d859615d855614d851613d84d612d849611d845610d84160fd83d60ed83960dd83560cd83160bd82d60ad829609d825608d821607d81d606d819605d815604d811603d80d602d809601d805600d8015ffd7fd5fed7f95fdd7f55fcd7f15fbd7ed5fad7e95f9d7e55f8d7e15f7d7dd5f6d7d95f5d7d55f4d7d15f3d7cd5f2d7c95f1d7c55f0d7c15efd7bd5eed7b95edd7b55ecd7b15ebd7ad5ead7a95e9d7a55e8d7a15e7d79d5e6d7995e5d7955e4d7915e3d78d5e2d7895e1d7855e0d7815dfd77d5ded7795ddd7755dcd7715dbd76d5dad7695d9d7655d8d7615d7d75d5d6d7595d5d7555d4d7515d3d74d5d2d7495d1d7455d0d7415cfd73d5ced7395cdd7355ccd7315c7f7081bbe6d49afa6aa1a5567819a2658993764318ba61d98165f197625cc16f25abd66458cd5e9567556954994e3525544c503d3c44de932c4b792a1497922047791a5455d12643bd0b141b90404034fc43e1cf453c28ecd3a58e50384cdcc35e4d3d33d4cab31d4c342fa4baa2d90b252ba8aa32964a1f278c9ac25dc93d24188d4226486720f87ff1f007871d1c6fb1b08690195c61217705a615c452d13e44b311b443f10103b00dec3380bb02b60a1023407f81b7055c118037c0b201cc03e000143056f1142b688aa5ac450ad622e7653987b078c0d73c54ab9e2435cf181ad7890d6bc616b1e30358f150ab78d4d52854aa143654ea152a750dad32854a99e2a54af152a478c3cf3c61679e3073cf1819e78c1ce3c60671e15138f1519b78c1cd3c61665e30732a1ba9878dccc3c66261e32730f0b99850c3cabc4c651430726f15093789849bc6e646c36322a1a99178dcc7156e238ab6b1d65b08e78a8c54264e26130913094189b2cc43596e60acb6105659382b2c2415954dfe7168fca1a97d785cbe956c9f1434ef8a1a27c50d0be3c6a5ecab62f539957778c3babc2e1d2732ae539877278dcb8bc655c5e30ae0f1507078cc37a864dbd4170dea0a86fb2c2b73c6059ec970cd64a866b24c33596e98ecb72c765b563b2d9b1d96c98ecb50c765a563b2d131d96618ecb2ac7658263b254b1d92958ec92ac7658262b2c0b1594c58a9b7 else 0x180081d40d58634b5a67040841c19b03581e04120b211506f04200e00c957b18c985045203482640b149f369029d0a4a2504c70400c2024a4f302014cc5ca0d5197044c18e2170ff085841a115130190e076060439839454a2450bc23403c3137ba81b610305c38cb8c8077d1b70c780c03806603700b3428307839a44a05204260ac137c1dc056022847a09d03e0ff453c4cc02d05d85e0e060770228a3440b0a01e7830078c11801f8b9c4ba20d03a82206805cb0ad82360782c01d686002ac06d0400ed815037c1d305109180700dc0bd415a0e01c685740502bd004092043022511d82b801d0cf02b843811e0bf0be813e2001f685345cc0503500e4068c09016015a819817e0e786f804055e02700f803a0bc0f687f425a06e09f0035f9d7c75e9d7875d9d7475c9d7075b9d6c75a9d687599d647589d607579d5c7569d587559d547549d507539d4c7529d487519d447509d4074f9d3c74e9d3874d9d3474c9d3074b9d2c74a9d287475d1b7465d177423d06f413d02f403cfef3f3cfaf3e3cf6f3d3cf2f3c3ceef3b3ceaf3a3ce6f393ce2f383cdef373cdaf363cd6f353cd2f343ccef333ccaf2f6cbbb2e6cb7b2d6cb3b2c6cafb2b6cabb2a6ca7b296ca3b286c9fb276c9bb266c97b256c93b246c8fb236c8bb226c87b216c83b206c7fb1f6c7bb1e6c77b1d6c73b1c6c6fb192c62b182c5eb172c5ab162c56b152c52b142c4eb132c4ab122c46b112c42b102c3eb0f2c3ab0e2c36b0d2c32b0c2c2eb0b2c2ab0a2c26b092c22b082c1eb072c1ab062c16b052c12b042c0eb032c0ab022c06b012c02b002bfeaff2bfaafe2bf6afd2bf2afc2beeafb2beaafa2be6af92be2af82bdeaf72bdaaf62bd6af52bd2af42bceaf32bcaaf22bc6af12bc2af02bbeaef2bbaaee2bb6aed2bb2aec2baeaeb2baaaea2ba6ae92ba2ae82b9eae72b9aae62b96ae52b92add0b722dc0b6e2db0b6a2da0b662d90b622d80b5e2d70b5a2d60b562d50b522d40b4e2d30b4a2d20b462d10b422d00b3e2cf0b3a2ce0b362cd0b322cc0b2e2cb0b2a2ca0b262c90b222c80b1e2c70b1a2c60b162c50b122c40b0e2c30b0a2c20b062c10b022c00afe2bf0afa2be0af62bd0af22bc0aee2bb0aea2ba0ae62b90ae22b80ade2b70ada2b60ad62b50ad22b40ace2adbab4eacbab0eabbaacea79a9c6a69a986a59a946a49a906a39a8c6a29a886a19a846a09a8069f9a7c69e9a7869d9a7469c9a7069b9a6c69a9a686999a646989a606979a5c6969a586959a546949a506939a4c6929a486919a446909a4068f9a3c68e9a3868d9a3468c9a3068b9a2c68a9a286899a246889a206879a1c6869a186859a0aa7d99dfe7779dbe7679d7e7579d3e7479cfe7379cbe6f49bb26e49b726d49b326c49af26b49ab26a49a726949a3268499f267499b26649972654985a60e96) else (if j<6 then 0x99f821d9fa046c0068900008fcdf90b0602589153f02bb02c8617f96ae0f011c7b104702ad1020a18d6a29ffb4c883c046c0478a0fe1c136f683104a3543c2067c18404e219ffc9901060c2041c4a3f060df84b40800913effa61909c80c200bc50016ffdf823830806f1415fc2b51620536917e6fcfa24c202710005fae490101653835f3039ffa623d10027a64e8100587f7c0001bf97a610096280803ffe046cd27801594688e9800bc12344c025a70035f00baa097bb115e627be14b30baac6501e086f7c9c0c978000809c48bf87db188105a1c00d7fe3d42041588279c33ac4082f10017370d02041688020fe16008094c01ff690ee3200813563fc9c2888105a1c1cfffb96304081244821f37c5010488810958beffe6851900456837fdd6038708100389000000005f053fcca241eff66f38548608f82619e61e9b34d3f468e00a16d14428ae783ca0cd2d09d11cf073140cb30f3444fbf988157c0e7088e78382af81cd10fcf06300a616c8462279f8c02ab44321e128a073f1b3ef01aa1c801bf837e43a9a00006b885fad43c181c54bbeae9adfc18bbae09a8742ffec130946ce11fb0d0251b387c2bf61a049c6813d6aabf2d1200dbb91b3491fd32d517589d5a71fe4cac2f185e4457f2cb5dd6299a113fe8099798819a400f921e6244eb08162b7f8bac85e4ce9257f7733b3414eff17590bc99d279f8f2694e4404ad12cfeaf2d00c2c36f1cae8d240c933f75d86220849afff812050022106a3ee5f330a102ab7fc5a0718020822275f8f1715000420889b87e3c2820a73e1882501103b4817ffff0ae06c501103b66ffec2284941273d3fb3025011483513fd3808604002144c503ffba2003190d3f1c485a4324025eae9c044400213ac58dff1301c4b0922ff7602184e2096224000000003fc3bfb7970009bc00f100de0ef0b440057f0e847175a21f80c20150a6fcda028881042200017fa6db970c2fcdf310000c3c448c81c409a69484f414b8aac4a603a432c6c61d31c986324511e929346509a8162060870607c0d606116c88191348da45d25a909492816c1520a8053c2d401ae1d689b46614b0a5052791a0e8007aa58c30af0e0582ec28c0a2084c80652a14d94b58dacb562db35da16c2461a0671b0e89d84d36a9bf42260b500b04481c7a9396b589609b633d278c282c205d011da4c6020b0d22ea1cc6c84ed1ee80c2e0156d57ca874a760fb13592a9840df0b9051014082ab5720b099615908f886817472b37c0248e58e0f41185794e66ed074e3042ea114e04846f0200ca06380630cb00d83a917884690c951120d8778a366ab2282d943be11b08f019442623d06287ec220aff079880c6d08e12df05e0dd07090b022d01ed07c32d8ca8b740b90a806a0c4522a80d50e614316a8f409c14304740061670a30a8855 else 0x8df904283c4000000abf939119a6629800000000000000000000000000000000000000000000000000000000000000cffd08b59234a000000000000000000000000000000000000000000000000000000000000000000000000000001dbcb1665b880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe4d7eff252488000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000029fff80d9e40694eb01163000000000001e0f0a08946a87000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000057fe4c20470a01d7e3fc33449620026c0031ffabfc400746100822c00000000000000000003b8ff24eac40ab400000000000000000000000000000000000000003bfec8060c202710000013fffebe900c1840028b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005be029164d068632a00000000013ff57fb60290460000f7fc0005393f0060c531a00000000010ff829f9e6940c91e00000affd3830a8b668d160013ffa603601cfa2b4500000055f9008296054aa000000001efffc852172c4b0093c8a5fdcf09c154574e009e17c019806b4f6396bc0371057195306620000023ffd96277022b14071f281c06400675000000047f01bcdb72b010f1a000bf829f1b7930049140000000025ff07be19040c31cf7d48d568e52cbff6a6a23bc650e0033db84bab0022240067e0fd7882c022c4c7edc0c302d9)))
def gH (j:Nat):Nat:= (if j<1 then 0x1caa00019150000000000000000000000000000000084ae2cf80b68a0000000000060accd2000100f800000000000000000000241400060be000609e00000000000000000000000000000000000000214a00044940000000000607603580000000000000641200040660000000000615c00000000000000000000123d000041b80010210000000000000061060000000000000000000000000000000000000001680578000000000083f0000000000120260500000000000000000000000000000000000000000000000097022a4a602d000000040b80448000000214000020e40000001841000000000000000001834800001680000000000000000101e000000000018068001b2ea15a0000001056000022e00000000000000000000000008178000000200400000000120eb782f26a2000000000000008388000000000000000000520001a398000150813800000a800040f60000000000000000000000000000000000000000000000000d508034000000000000010c1800000000010250eb8000000000062cc0000000000494000000000000000000000000000000000000000000094fc12200000900000001a3be03c000000000020298330000000000100940018230000000000000000000004162000000000000000000000000000080380004ad80000000000000000000060f2000000180892b40000000000204a00020d80000000000407400280000000000000000000000001038000848000025581660002143009a0a000000003ac8000000000000000000000000000000000032b800000000000000000000085900d00000c0800c00da0000000cd68001846c01c81c800200000000000000000000000000000004f5c00000000000000000000000000000000000000000000000000000000000013181b800103eeebc8238000000000000060ae0000000000000000000ea00000b7019000000048b600000000000000000000000000000000000000000000000000000000000614400041460000000000000000000000000000000207e000000000060700000000000000000000000000000000000104300000000000000000000060bb829331aa56800000000000000000000000000000000003094000000000000000000001843800023c00000000000000000000000000000000000000000040aa00000000000000000000000060438110000000011c0004010000095e00000f800000000000000000000080a80000000000000000085860a20000000000402e000000000000000000000000000101a00008058000baa60ee000000000000000000000822000000000000000000000006c000626200000000000000000000002c8000a46a06284f80008498000000000000000440182400c12288180091c125021a08803120000b00a200 else 0x401f853000084d8000000604c0000000000000000000f0000000000000018268434000000008160060000001840000000000000000000000205400000000000000000000000000000000000000245200060400000056811800131200000050000000094e0000000000000104b603600000000000000000000004c80000004f49847c108000000000000000000008000000000000000000000031204e000000000000000002058000000000041020000000000000084b800000000000000c6e030c1560000000000000000ec0de00028a800000018b080000538001bd40000000000000000000000000000000000000000000000000000000000000000000000213400040e600000000000000000000000000008458000916000000000000000000000000000000fe0000000000000000e00000000000000000000000000000000000000000000000000000224000080c8000000000102c00000000000000000000061100000001998800000000012520000398800000000000000000000000081e800010e84320000000000000000020c000022f800000000000000000000000000000000000000000000000000000000000209c0000000000000000020dc0000000115800083b0000000000110a80000000000000000000000000000000814800000060c6000000000000015ad000000000ce000607c0000000000205c00000000000000000000000000000000000000024d84a015400000000000000000000115020e800041520000001a30206a0000000000409800000000004018000000015100c800040d4000000000000000002f5a832a11584f0020144e2c890dce95042a0800b2e124020a69f004ec040000000000000185ae0920000000000000100300009be800000064380000f4a000000000000008298000854000104ee0e0000000022200f400000000000000000000000000000000000021800000000000006061046000)
def gC (j:Nat):Nat:= (if j<3 then (if j<1 then 0xd308fe9547f4cc3da54ded352ee9a1774d03ba651dd2e8ee8a9774cc39a655cd330de9956f4c3b7a5cdbd2a6de9a96b4d2b5a681ad32ad69946b4aa35a2a5ad14ad68956b4d2b3a6859d330ce995674c133a6059d2a6ce95267498b3a6617d32abe9a85b4d2ada6896d330b69a8574d2aba68d5d330ae995574c9aba60d5d352a69a94f4d2a7a68d3d3429e9a04f4caa7a64d3d2a69e8a94f4d125a64d2d2a6969524b498a5a6a51d3468e9a0474c9a3a60d1d34486993434c121a6a4fd34a7e9953f4c29fa694ed330769823b4c09da548ed3506e9a5374cc1ba64cdd2a66e9a22b4a915a68c6d2a6369a8174d08ba6941d3460e953074d180369706b317c187be4b2df258ef82e374963ba4b2d9258eb9a855b598a9acad4d64aa6b5348da8a06d2d0368a86b3143595a1ac950d69276b433b4a39dacc4cd66256b2f2b59595a4c4ad66246b272349891a49c836a636b2b1b5a9886d4c4e6622195310da2846d440d66201b52fc1977dac9bf061df82e8fe59879acc3d964decb08f41737a0b8bd9551ecaa6f65517b2a0bcd6a5d6952e8da571acc38d655c9b08e0da76dacc36d655b9b28dcd846dad4b43695acb40d359469a54b596a19cb4ace5a2672d0b3966196b30ce595672c8b396099cb02ce58066aa9b375499caa2cd53167254b392a19c94ace4986724ab2368d81b42c0da85c6d2ae368576b30bb5955da4aaed6a166b4ab35a259acc2cd6a156b46ab59855acaaad64d56b52a35a94c6d4a6d65536b269b4a94dac9a4d6a511b528b59346ec122d6a4f1b4a7b5953c6d29cd660ecb00755533aa989d96a0d1b506e5a5346d29b968cdcb306b598372ca9b964cd6b266e585372c19b9600dcaa66dd52372a81b94c0d6b505b5a9286d114d648a6b424b5a521ad40ed54c76b5230da319ac98cd6a451b5028da115acc0ad69436b50135a509ad482368c16b2a0b59305ad480368c06b2605d82000d4e0565ef8b09681a9b22b25602a6b0153481a98c054c406a610352f95977debabcf5d1e7ae6f3d717aca13c02a5d4328d80a9698cc33454d9b2a4cd131642d3ae269970352a00a9500d4a602a530152881a93c0549ec64cdb2a46e15134cd11806a4a2b2e51996296c89406a462330301a9152c98a568c44b4a1a9a8094d28406a4123300959704ccb027654143280a593054c90206a402b2e02194012c980a6480fffffeffcffbffaff7ff6feffbffaff7ff7eeffdffdfedfddfbdf7defddfdbfd7fcffbffbbfb7f9ff5cd605c5605c160591605096050560645306053024530661206512064d20645206112060520601205d1205cd205c12054d2050d20505204c5204c1202612024d2064d106491060d10609106011054910541104c9104c110481106583064430604306602064c20644206042054c2065c1064c10648106081054810 else (if j<2 then 0x1d02328b823c5cc4281508341160905ea25246a45614632208c4b43008f817409c09a2d21924f069c18a1f049044a2605882b80aa07a09a2ec0b83b21a059c31c2f039c06c0dc1703e40a05d80841541604340842802c40180c034e2003881e40e037c1d410c2182780ee1bc1ca2980581640ca12a19811a14c08a0b60f405c13c0a60702ac10a0680d024801c02c01c03c04c00ad375a4eb45d683acf759ceb35d663acb7594eb25d643ac7758ceb15d623ac37584eadf55b6ab5d569aacf5596ab1d561aabf5576aadd559aaaf5556aa9d551aa9f5536aa5d549aa8f5516aa1d5316a5ed4b5a95b5296a4ed495a91b50eea19d42ba847506e9c65384a6f94dd29b65364a6b94bbe941522aa35d44ca862508da10b41f683ad06da0cb41767e5cfc39f013de27b84f689ec13d627a84f489e813ce27984f289e413c62750ce999d233a26740ce799ce339a6730ce599ca33926720ce399c6338a6710ce199c233826700cdf99be337a66f0cdd99ba337266e0cdb99a7734ce695cd239a37344e685cd0399f733ce675cce399b7334e665ccc3997732ce655cca39937324e60ecc15981b30165fecbf597db2f965eecbd5979b2cfe5684a2d93692472433c7b08e011aa230cc5bd8ac313c624c444e87f50ec21b3c3148571090e0f0c18a82670322026bffa7f6afda9f91bee67d50f8c9ee4bd7f7a78f40de62bc627814ef15dab3af57516e89dcee397c7258e309c15b7af6ea6db1db2db5e96a96d37da47b4326794cda198332a86478c7158b7b10f6172c1b98132fb35eb8bc2d762ae6f5c56b7616bc2d2d59beb1e560f2baf56baabe1557aa6253eaa6dd4b6291c518ca17d40e27b24e909be136326764c7897f92dea5724a6893fd266249948da90ed1f8a3a746d28c5115f22744468879d0cea14041f482a50269feb3f387ce4f641e633bd076d4ebf9d533a0e7354e511c63386e7014dde1b65361c6a88d389a1f3370659cc8c98d1311460c8bee97962e965bb0b5696582bee56d0ab8952f29ae5224a2513fe27904de898d92e3252e49248f511942288442084e104820183e4c7a20ed71d0438dc6ec8d8e1a5433446378c1316fa2c405670a84148a28004df899b1266239444d086310641fec3e1077a0e7a1c4036786a80cd418882e4059a0aa4143c2660491089c106c1e9038e06a60c74173829304ba08240e7019b029804400678094007800034d4e1a6970d3097e942bf4c3d9a5cebd351569a5ab4d155a662ad32b56992ab45455a296ad145569a9a74d053a64a9d2a54e8a9a744953a6927d3473e9a19f451cfa6626d3512e9a7974d2cba6865d3312e997974cacba61e5d1512e8a59744c4ba6a24d34726998934c9c9a54e4d3311e9878f4d4c5a68e2d341169988b4c9c5a54e2d127169a2874d0c3a60a1d2630e998834cc3fa64df else 0x27f317c0c4100a442dfdd0d2280dffe2d584088135eea4016470197f03001883e0a6f524fffd90cf1020080a279f64531004b43eff3ea88241239fce441004b4381fef4880021698dffbb4208820080a249ffab1104012d0f3fc4820a24817ffd21801004fc45f99988227038005ed9d96b29c1eab0e002db6650e280007be0e717b2cf593518b440cf5932e141eab0e000e36650e2b3f9dbe68466caa3567f3b7cd08cd9456a260d10536fcd30e0d1053eece77212279e0b5bbac5431bff5a3f700656986241ffe1c220195a3a22bf1f1c81aab8b42c42c7b42eac92b10b1ed0bab2493f07bff76804a16e3a452c42c7b42eac926ff1fffc04a067034ad159f0050b705619a442f4744983a4bdff48802418e01a45a9133ef1a3217404a03aff302b8639553b4332d85a150869b7fffc0ce6940c301a3a8b133ae7a3217044a87027043823842cc0f16d17c16fc20a201768b04f04ac14517433cacfc8606810b33a181c7c1554b348c5420d845b0a42ef2872644a446c4a948647242147d4a813eaef0b28c488c49c47b1370ffa8513686daeb90b22e25a28508c06d07fc7b218c1a0adab1a96aab65a66b6850b917717f68964667e62963d61946011c6d367369715717941a11fad621b1671662c344d16533820330a6bc160a4f17e33b0cb30169333917a1784201718f520b2af17d8828fa3320df3314c217b0de18011616e2514526ae03b6a26f86d210d20a2d32900a000da7311446111b87510690590686504808a00852885455856bc48c5114844284c182c2b4b715dc05c0e93485b80087b82126b8042eba9d08d69dc8d16911311272d27e62e04e1091470200111642d51532fd4d045c10c8b316344843b4404658cb6202fc8a4c7247c4624310c644bc6c2452228aa41f8944686180c8a9511e46e8801202da61b0e81212812c03020e111911811daaf2a1aa1abc2360b041b0cd64a2fb0c9a1b81a82c4f44f30e941d8091174f18400400650542a283f11143f0e244c0dd110c15c47c63c62c7d22d0b8a7aa6b0e3aae01b10f4806c31000800c40918c10ca8514948a3c1e42f82f46d0b70a7a88c5f45f46343ac5b2962ab2012952b181d84d0ce60243c4352882d78660b4a930e703040760b8184d149f86e83c49e0278480e502b0b5441c220790e405506a267a670b6a4a06606e25324a4660188ac0c7075081841a22c1f0a5400209a8909aa7e2c50822ad4a00ba22540da188610a6c3a0bb23d060a8709b22600700f01a09081087f08e427c2342241c20661a84ea3244ec0701600c00500e830c1107605607120209923282262663604d625074098a1a297061423c64c41842417077a0f084860a0206f40f078847212a33a5a62d03c035273052070451c4cc3fa5083541805720f092207a36a46229250a53633612a3da030098280)) else (if j<4 then 0x7219fe1f007f080bb477f7fde5f082840286acbd5dce06080e38068a9006ff8ec55d8e204021aa81efe4f03bea90c0cd1e4049c685f80139fd76148a7a7fff240b56da0601f752017238dfd5ff86e9594189335c80bc8e43fc1ab202c9804071a9ead39ed40d59e2f47c49415555401cea5193f01ac183187dff14f3f1208092b7be9789ea9044e96efe1f0d210420080a2b7fc53cfc482024abff7ef01110155f9fe6022022adff500104a0937e660444a527fff30111294abfe3f6b788100405129ffff56bcf410103356feff3ea090440954f87bffa935220802108b47fdffd328c88820089e2c001ee87f43080085a8dec79627c482a24c164fee37c4384010b4507ffeff3100440442d4f71bcaf3069881020022aabf51fd20f30200822248fd6dbea084040045153efff37fbfe7510410054317afe9e847ffc10941040115c617ffefc7483a2202026bc7ffffe410a046882100405180f7ecf378048fba414310802248ff7fff1f1ee43848b384011446821f829e087ae9fb024041220084991dff50010446927fe7ef01111955f99811099497ffa364400010109b61fffcc0444653bfea00208152771f15d4004110265f9981112949fffcc0444a535ffb2742000202526b4bffbc134904004004475487ff292b8208008008e6a814f07800057fc42000020088e3ef8ff9c4446525fffff42364601010bb6025e2f0005fe4a00000802378e00affff3a100010111b673a3c13cd4c370633115deb0f5805b76e686d4025fc8b72f56e49aa1deafeb30e01465b66522309ffb43533e404641b2117e7f0a0449742b0caa15f97b435738a06b3c4c3f97a3f550879f0520d608ccfe7e6f346264ad277382cafdd484832427aa77eef02bfc9dc6410c6e2dc67054414dbb9dc83893391e8905567e695087245d4d45df99d401de8fa8749bb59cee42c613fa93ad1f209128b11404dff010629a369dde8f93f88806568622660858f617754963e4d64b5d27aa68dea5dff2d5fc7f012819c0d43460f10b1f449b02483fe0671172180d20454bff35e2570dd3b41314affff1f03058d2b4c0685a3002ffe7eff12ada1da688a01116fcdf9099c6d458a5bd8f7d6292e9a6000000000037e6fc7cd93cb508e37bb4626830e7f08d678b33e17a1ce6948a637e4f050dc70030c1aa759011a26c8d27afcbd020113e9266b6ffaf00f6c32f66afd20ca005b800009d0dee164e4c901ea89fe6fa7a84184001c4811fe36d9e51b89009016b1baffe546200af20212240aff5f013a6036d2e32024a37dfc0e8093652d81900e518015ebfe014b403b43da001b7eb8018fe14c42e342901946857ff847ff0f000cc00b0000e877f6c20026ee0023ffc44007bcc5e835520328f0be078358f2008a9f9f003f4e3671001889b7ece800904007100ff2cce0620802489 else (if j<5 then 0xe20022f3725ec44a491013ff8000020df1000ae2013e6d025ec44e59500006ffe00005aa749ad2c1e1495ce0858006db409c4e00000000000016ffc0001be28725d2f07a5c0aeb42519c000000000cffe9c10821e9a6a002ad9cae43c426539bdbe77b330a506c67aa42aa0000000008fffeead9ed349b273335010729cffa33ca2e6212ca07cc519cffa73c1c86212ca46cc7198ffffc5f0fb218842098c9acf51d27ff8189810c10140136aa00000b7d5fb29d102264fe00000017e62950c2a4000025f77eca744089dbf4f499e7314a9e54025f669c3fa8c4a74248a034fcbf36fb94308a5484ab000024fe47c2a90e9951060805157d9e241f0a5a3594760e00135937f97b380a534304024aab1fca4dccb24221840594628df013fcb2e529015338808c8f000000015ff27d5f67e836971013120afabdb420d64ce2026a2dcfa0ccafbd880274fd849b39ff1daa01d5ac936efc563b5404bb59adb6578a0000718024fb44580019c687e9fa452105b8c804de270807964414fffe53766eecef60e100711ba7fe909d46191012d4161fc553d9180046a6fc2bc7230173449ff0675d992274d0f9199be9e008340c4202523a5ffba91488c9c9a29a8a2d0f014fe8e7183334e0fffe68fc550aded0120120316381fcf1db20852d2d81901a51c000000c7fad825319100804c56957ce7f00a5a01da1ef2002380006ffcdb100c80328906bf0f164b89ef744280a88d0fd3a7ff00122440596b57f8b92782b95f8420ce2027a3d9ff0ffc410000c800280000781ef641000acb33fd5fc7c35654b0354b31462401248e3ff7370e551c6c189009c68008ffc6bedeb103120009013ee090008ca2be0b6001bd802837712a4004478000b7fff8035053055f8d500b71e003bff1e4c78f0201320012005196cdb3812acc0016fe087bf2eec13f1e6403cc771e4f38d02c647c02bd483dfc1e00640d5c582015e331fc80fffa45b3b590582025e340017c1cdea8b67707080658d03ae376c62ba11115c4019eb3adfd376c934e0bb7d80b36ed7f07dd77d00ab36bea2100d28e05bffc001228ecddd9c0e49201d1214f039a593189f3680414602da3a7a59333e6954800a4683de0fa1936dcfe20009179fa53a36be41600d9adeffd6f22e9c2007aa0000029fc1af03be4f30b2cd05d4780065d085f690cc98007aa97ffcc2ceca818e01a450bf0b3b2a8238069131ffffccefcd58327022b6774c74dd8327023b5cbff91aa80c012080378b87ff77f1120181812080038d2ffbf8cadd709c068d55fdffead81832703cb5e3fdbc12ffdf6e954241006d1b9763e34be80b8030e00eaac02ff87901e00001ff7088401247175cb8e0a0c19d0806edce07fff571047180c720809d8e67ffa044aa08e0324487e5f28640018f82a5ac14f03b013dfd43c954241000 else 0x61ffafe309544aa400000000000000000000000000000000000000000003ba27dcbf2c2100ecd4000000000000006fff79d6f98b308010458000000000dfffc9278bff8248110248018d0500699300000000000047f18006f655b6d759388e07d483aef17f42580a3c86041d200823c1e0e02a76ec09254829233dffffb7aaca4b0328e0d39c42001e411ffffc50979cea0c08e1ccc4202d643de2843078e0a644021196406f9093b6c96570590e00000000000000005ffe0355a7e307eab1f1a1004200134a001bffedab106a0068800000000000000000000000000effff3e39c0fcee1378089150112e400000000000000000000000000000000000000000000000000000000000023fff8386267fe8f101204a0105c80000000000000000000000000000000000000000001bffb75fe32842460c00004010912200000000000000000000000000001dffc5efed5880efde6f800a5c98000147fcc0c2040c696a2e8a3ae013ff814007a582d35a583c217b36001c69040d30000010f880c)))
def gI (j:Nat):Nat:= (if j<2 then (if j<1 then 0x4cc2da88830172831e002d02b281d3822485b0ad35c11a443bc1bfc2fa80de2ec2c2c98298826ceabb815c024ccc4e88e80d2582b9083602635225c116851d01b41c4d0577c05ec2a199d0014381e95c4fddfa8176a608831c82f8057841ff805a0122429d08f00160c2c0400bc4e390f742ef8016c1860729c19dc01ac0ce801800a0c266810c8333914e99fac03e42b61da642e1c86a992e402ec11fd1af413ec2c6c86f00f4031f412f429300000000821d001c826f0000d9e881ac10ee8d94c934a9030000000000008076000042c39e690000c09842614180d1ff0000000049940000ae81df0601e600004232000081a9c2010950821300ae424e919741bc1170000081ad902bc274c30142f409f00000c147020e2532813a0000010e91a48316000059dd403b81a1c1dd40f01804d1f0ae9592160d93c107018a81c8009dc03100004abb0090504ec50b4008c59b9db9812e0b25086c1a1a00051a5d5048000000ebc17321e8850140ed9f2b8525c0d1c899904a4d0981a6806841460000c26742f240d400008086051511710841915300000000c1a59c3300000325000000110000c2dfea0caaea66c142f642530000000042ee84fc893b00b3408ec1330000c896428801528ebbd0ea000000006e1300005172cd372226401400001038494825f800000000492504e1000042e0000000004538461b0300c0f71918031500b601de02cd52e4414e5f0f00c341054132c1b2d0605cd784d3c280d9300230803801c91e4a00000000015400c8000002dba305921f017f0a00405282d5d0500000ae8c9100c11182e2000002fd0037c2fe480dc135000000d808fd130b0000c81ecde3c007d02d826800008089804f00004637427d00a7c318c16781af000000000000c0e0019a863a42dec0bbc144c24f405b00004907526d52c3823c2e0609002302010a881c054a2502014110031026012e0b453e277704033e0011803e0700020910004f1c273a16170f6b0100090104001d1b0b0c122305130020012e1b0812000a1001035c4d0d070e0013043b032e1e200739100200000800051a3147000e0b2501000101020105000803112300100a02052202100217241a0f00090918000102004600001808186a056e353a250c1522074300030014031412190200280005101708000f080220001e43090a1e0e1a090a0f1006013f0601000b10390e3f00091e06190102061303002307000507002a0f09000b03010a1d0b0d60090004090520300e1e170c670409030b141707030b01261c000d2a061103310507020504101a0d0f040300380b010d02061318130103040505050e18050300170a00190806130d0829041a4e01010009063e0219220038001e0b03002d010515022001010500010400240302110500010c000702021d13000a051503021606 else 0x2cc126000002144071016c400ec00681484271102c125f828a82e68e054206c01580e3a250c312c27a8211088c00000000d83ac191dd0292ca4187e6c69985c32cc292972599389ef19c5c61e2000080f8c2a9846642eb0000a8fb023610f4486e827fc222000081f7d1bc1e7f8681ca020000c2c1427840b881c69980818b85ac41b3c1fb0f311e494219010d91914083810411b18294d042000000001839822100f5032640652d3c55041f26404a0de49223d98742ca000000c60000000092604ac20000a9441da76e4d00009986126c88975e6d000080e8000081ee00000000000000009efcc2814209480c411900006437426bef30000000000000c2d482570000000010f5d220000024ec1e7b42cba1e581cf0000c171c1f16e940000c192c25c8225c18d00000000c269584c0054830b000001490000830449b0c2834d284072405602d96d45e1d92d4d002741258323d5050073418f01c3c311c1fe80e202628168e10ba662000082e55a8140ee0000c03dca0102318d3bc1b8dd8dd2c200e982169ecb923901d622c28151000042aa4075294c02f0c60a0000c19f01f90725c2d682aec0db9f0e82b8c25b01c7813dd30f41e50000c1ed91a9c02a0000091395b08123c6094a9f0000000000000010000010cdc1cc00008cfc000005ae113b5928c0ecc1415ac2815390f626f300da48fc919d0000000080cc018907050000016f10c0ed339e7dc20a000000000000920901c00000000009270000429bca26401385c081ca50c700000000000082b700000000404100000000000051eb00002ac282ac0303000082720000c0340000c23400008ae3c04702730242000000d38917011852c8acf39ec6dec98170523a51b4030640fc83070000c1b041900000000042d7c85f0000429c998800000000000080b0424b0000024dda7a00000000809fc0ddc30800004a9c4202031452c481f0028b80b7e2a00000c0794208006cd16e9b05c1360000809201d5000029455e62e6c200006d2f41b6531712810000dd7b0000df1200001db0402200008d1c1ec8c10f1f08419c80e4000080590000009a40330000000000005ef60000814fdd7a813f82ea832702f30a855ef00000954bc30dc4e2407e828541a351a882e48036c06100000000000002ecc1280000e669c17b9da10000c09b021fc91bc032c1888243083c030c02a300008195416ad2c5c1fcd6a0a665032e49100000401f6dfa099201da00002f2e410900000000c2569d1a422d82b1c12d41210000021b00004181c30e00004094491a0137c1abc082d22251a00a4a0254c0b4027b021744d640f6c91ce85000b24d92dda98028c060c302d0bec28caebbc11d624a82a02d34008b00000320029e81650159c15f42a81b27c2b4c1d7844b41124062eaa5c24783175c35018c28ed6affc1) else (if j<3 then 0x40d2024985a1e2a148ea000081010023000041d8000001ce010000000000c3210000a6810000431d000082be020f5063a470000051991e08c26e0a6a40f342a681e340b5005f0265dcff41a7454b41e4c25f02288070881002ed4296c8148e48010643316d9bc14b4332889080fa80660134411c0244c8ecc27c44e002e7de7e80f282b3da7958cec83bc00a4cf7c0b152bb415bdacc00000000c087d97f803a11ae000000000000000059e2000066f0c2dd000011f9000002d80045000000fd80dfc01d80e700009ec2dc315d22d4fbe9b5c1b7000080cb99e50000014a0000088542904919d9dc02ff40bf0237022680968003ddc681db01a400000124403f0000402540bc0329400900000000018380350000c0c180fb00000000000010c80000c17e0000644fc0c081e8992fc06d00008019c1ef000081a201970000c0cd4812d50681df81bd513c829a817901b5401b486d00001d1800009d1c8115008000000000c83700000dfa822e82c7d19bd1a501c200005315000086e581f2819e000049b5e95100004309000c00005eca00000000c5c780cae94d11760000812a80a5820b832b8002c2230000c026c92919d81e6300e61d7cc1f8c8792117008101ecc88942339114ed2d01a80461c21e423e8064c20500001dcc8313402f000042c512f089440088800d0000a902022bc21cdae5821000004284000099a102158299000000000000000000e10000000081aa00000000000040f9cd3c00000030c2f5cd8bc039416b00002e911afe009e190b5de300914e81017c82c242cf00008c3b02480097c451521d431a82708204116bc16411be8220422c804349909ef95236c1eb828704e4425980c545ca0000422ac00f1e6500000000c255ddf8451f84679d88ca81464f807a02cc853702dc5681c32ac2f11dc300ea0000402b00000000000041a000005f0700001231423d91b3e1dd80c4420c000082290000e138c1829196c2ce4663c2bc000001c400006e8dd319d2265036c218030f8aa68108c1408156d3098142a66dd2bf01e2c0a882b58166c1174150c1ae1d51c139051b1dfe424a457902951d1b00000000413180d980d749e400f1828fc5c2c10a4103893cc94a815e4085521e01d98d29806f00004816432d80c745ccc8844069c264c10202bb41d0104dc238000002fb1ec1c90848e90000031b026d990c808a425a614500004638c68300460000c1750000019900008162e18600004004487c000042910000000040530c02c1f6e6cb40a90d8f11b90000c80ac5099f11472a817dc07712c60260c02980b940930057c80f4a4bc11e01fa5989c5864938e663c80b4130c15a422f00cfc08c0000c03cc196518cc04c827e40abc02442768a5596c2c2770000029f1aa046c240bdc12700000000420351c002a240fe8811c08f89 else 0x11a100afc23a000082ab9a1be29f0169621b4145428602d200000000821200a4d856c0ba12630000000000be426ac32f0000917481f401cb42af806a00000000000042fc0000e03901dc22e212e902ad40dc561b105f86e0ee930000c1140000881d025d41e181fd01bb81f3000040ad59d7829740c2d2f110ec46cd8ec205f30000c528000000001efa65fa428901130000020d516c91ba5e0700004310d1f8d8540809523880d00000c15d00000000e666ee909cd240a60048000059834178006302a48058c04dc2c8d18311925224000048399325ddc94319c1579da3de814044018ed30ac049023b407dde7c0000992742d0c30a0000c06bd2bd417a92c00000425e00000000408d81850000823f00005cd48240e990c07fc1b9c0ac81e0df1005fa000040d541c541bed97e00008817c2ba891d0406009c8818e1e6819840504055880e80a3819ba2814227016d0000aa2611fa00004279aa4a416e0000000024ff000080e5c252000090f38db045ad624906cc41d20158000002c4419300008095000010370000001ec20029b685c8d19e823542bfa1845262493a00000000c12bed4cdef28250c2821d25404b5ef348f7025841775ec7051742a7451e813b813802468239c11b1233e04c10f082a5092b866ee51a6e8f10495cdbc1b1d22dc021d98450f225a141948275c2f982e900748110c12990c30000c06702e381554120c099000049490084c91f421a41e7c12cdde940c94d8d82e84078d84d402083229e66024151c541741e2ec0ff82d1d9d5006e00002a810012818483300000926aed2ec52095ad014de6fcd2fc4c610f25807c00a29230000081c182b00a6340d681cd40a141f541ba0000d1ab0000c20700001234eec7c245000002d30000ae8800008328d86082f71eef000000000000c07b00000000c28d000042bdc1d1864800005da8000080aac02c9cdcdee4800101d4c10bc1ea000000004947805c000086a012f7000081612dbe83248042887300ef80400000428e904f192c004e005dc1634251000000008702c0515c34413c455a8305001700))
def gD (j:Nat):Nat:= (if j<1 then 0x99ff8fe7880a0e00018eec0cbbe6603945800007e0761dd4180851602fac46c0a44f8e2d41b00a483df013c0af006010662c3e1f5a5adc83308350ff9f0b1f8d1000804bea0ce0e7e965500318662b3feffe92f8480004004badc007bff2b4900108c51165e1ffe7881054a5d7ff1cdf102095cb80000392ada6fa910000bc82e3a85d04e2400f00b0c2007190c4805fa49a23320605120073c12905ef828ac56787c001b824009295d200ea1b900000000000bfc00001bfcf3d7bc035b9ffffe000000005e1557d71a0060baa96800000000005fe00000dfe79ebde01ad80000000000007dbfb7fc09be1bbc06a3301887aff5a413aa80182181f5bc0004e06d602c2e6fc00d5377af1541e980d4400beb11b02913e38b506c02933e38b11b1a91045f04f5b40b10536d91f0ca7cc0aa980a51b1be194f981553014a36027f3506f64d602936cefff8f4800562012a358f5fe00e16604a8960001f002f846b5b40b104d538817c33f00fde620122b6463d241140243691ff98016604a894bfc01c2cc09512a54cbf97d2a0a094017036840b2314912c998a52d0588978ff26a4b8b987052c80555a9503aac41505255cb5841a874c884d01aaf5423d549abc16101c86a0a5a6a8939a8b410a5c608ca0ea2785a8ac20b17211c5186110a20c2881810817c1685e05d0f93f1fc0981982e0241e81680b9f33de610f29dc3e8078180384c09312425449c92acf9391ec6348d05886104c1a580a21190610202cc6c06c1522703e01f0be218390be0fa1885f8a80962345a01a14613020c4c07e144550d41a02523e08e8c696a05c0610103c1b890015016070d98fb21a392bd50a99d4e85b0620e8318000081ec10a894fc940370230c10621f82203c11e3241c105026360b24f49ae312460cc1381407f83d05e2fa2282a2303442282294d0d4080ca22a2da3640507c1e22949f86e0ec0d01108436a2e40e1341aa4540c82c0683b05704e18a0fc409291e801874866080300901500a81142489919a2d81410013a1444b00e0100e02d00602005019002b9f587a75d14a771327944c7ee36f15b88843861230628143f19eecf1974f3891b34d6167d31dd858bf65d2ad4d64aaf155029654069b84ada42d19688c425a010f7a7773969b04c845bc29e937094444c1f90ed470e3531918b5c5182410fb06a42ce10105881d80760009663cb2fe584f2b9f95c7cae1e542f2a0f9646cb036491b2cc496524b27259192c2496064b01257492b9c95c24aa7254392a0c94c64a6124989249c964dcb24e58372c139601caa4e5507299394c1ca40e58152c09954ccb0425520acbf6597b2c9d963eea0e56622b29217090984564dab24e1206ac8a5660ab2655912ac9856480b2c819704ca0364c23243ffffefdfefeffdfbbef7bedfd7f581404c1204403008010 else 0x25fe2067259934a6b1ccffb7406a1e14a4f13bfffff9ff85c09f851030b02684d0060b0726ba37ffffc2fbf9c6df106850640b0b901f81125d004fffffa81fe04c2cc7da27100b9c86f8d6574003ff64f4a800270048252a141005d05e4f43ffffc4ffc2e04fe0a2068989a1340182c13f2f8077fc0be9f0048400a0926e000600822cf2003b043cd207231120f800066015b0d520722f1a00000001bf819fcca2425f35fe1423eef53135440180e0b7a8c5e16bfc03472f5cb20b170cda37fcfc21a1242880301c00f54b7cbb71810137a401a8b4ffffff60cd040010000436a7fff1f6d01241398a00018218014750ffff800006401a50028151b60039d0002bfc33e70094ab048205212602008d79c7c02c541810438037ffffe4411300060860c27000efff6f4e041204c02680006008018eeeff1c8da185c800822)
def gJ (j:Nat):Nat:= (if j<2 then (if j<1 then 0x8ae000001c40000000516800000000000000000000000000d8ea0001041a14ad94ba2f9110b467000184ac0000000d05054a506a80fa000180fc000204c49b7085c00042fcc1fe00030ae80000000000000054eba9e1317f16b00000001833e0a08000012a0000000000000000000000771488e40000000207400000000000000002fc047800070e6000001380000000000182480000000000000000000a5e00011186b3380000000000000000000000000000000000000000307e80000001525c0000000000000000000000000184b400000008150000000009538c4e232000000000000d55126300000000000000000000000000344600000000857d039c2b444c4000000060e4000131bc05680000000028000000008163817000000000000000103d40140001022400061240000000000000001166000000000000000000000000000000000070a800081fc232757300000000000000000002dfe000145e0000000000000006099c0cda2c874b80000001335400000000000000000000000000000095730720000000000000000001b4bf1868000e9f59a520148000401c04040000000000182060108000511c000000000000000810000000000000000000100001a660000000000000000001498c046d26600000006f70000000000000000109c000242d4f40c80400030a00000ca3600000000000985f051c0000000000000000000000000104c80000000000103300000000c1105be8000692a00000000000000082ac0000000408a00000000000000000000000000494e000000000000000000000000000000000000000000000000104f00000000000082d4000000000010600000606c000000020218148000005f000000000000b28400000000000000000000000000000004b00000000a19c00060d2000000000b00000000015f00000000c1be000000000000000000000000000001830800060390000000005a010ac15e000000000006e0e0000000011984da808c04d00000001005400000000000000000000000000000000000004091844c45680000001056c0000000000002c120d914b01900419a3d00008006025f21f4f714d68000005480000000000328880000000000000026310000bcdc00000000000bbb80000409124f8b0a00900000000000027c410000019c0d0550000000012c713a8959000034c745d80000000000000000000000392815b80000000000107a207708da908400040900460000303b00000000bd100000000d1a112a800000002d2880f4000600d34004122460351060000227330202013212740045132070000005072a301113130020210b81043010000000c000016100010064028024520010120056011014402310003150401010300103010012031250001300100100201006000220001001100210 else 0x200030ac0000516a5be3699000000008a3c00000000000000002a000000000002022c2e30000048400060a1000024a007c00009174000000000009d48000000000000000000000000000000000000008990000000000000000000b9744310000c2c2000000000004d48000233766b2000094140840000d9d1896646880f60000000341480005eb000024798000000000030a8e0dd0000000006c80000001807b419600c000083012a9e09b000000000000000ad3000000000000000000000000b0a0000256c00000000000000000060cd00000000000000000000000000208542d000016b80000c8dc000000000d60001102c000217b000082939a00000000084dc00000000000b3fc000000000000000000202f822a29d70b50000000000023498000022c000365e40056ae20d2c0000000000000024330000000003a66b68000000084da22d800002ed004c0000000c296000000000ea000000000000000106c09ac0000000e1e4000000041140000a26000001460000000000060172682000000000000000000300fc07d00000000000217ac8de00200000939407c000000060500001821d03cc11f000184cc000000002a000000000000009382ac00000000000000130d00005864000000e0000000120b805fe92300000001b15c14d00ac000000000004254000000016ec0001b1b800028970000000000051350000000102ee6f8c9e60000000609800000000000493a00012ce40006267000000030aba1281ca80000007800000000000000000000000002495800000000000000000000000000000000000000000000000000000000000685b00000000000000000000000000415381f7225400000000001bab80006b560001017800000000000829c0000000c29200000000000000139b000000000001db85002000042c6000000040a20000000119300000001cd10000245dd2ae000207be03000012b08759800000000000171000000012c340000000c25e840a0988e7b81580515a8c0000594483c800020e0000110fc00061674246000000000bd000000000000000594680a800000000000000000002b6000000000000000000081840000000004800010a78000000184b80000000d26f88b4000000000000000000000048c44baa086e03400000000062000000000001235000000000002697000000000000000000000000000000000040e4000000028bf000139aa00304790221a51055e0000407501fc0002084821c00000000000a8f0a88518500000000000001b000002980000000000000000000897e13000010412048cf420000d1b00006107822e45fa02b800000018298000610f0000000000000000000000218180000000011c06e2d350000000046580000001142eb397671000000000000000aa2925a000000000000000344e) else (if j<3 then 0x41d00000184b66e000000000000000000000000000000829c839e169800042da000201ac0b6000182380000000c61732da469349800000000000007c81ae00000000000ddda00000000000000000020b880000000000000000000000000000000000000000000020c700000000000000092c684600000000c1dc02c900500000000a04400000000000000323c0000000000000000000000000000004c700001ad2c0004152416e80880000000add200020380000c05c00000000000ccca000000000db00000000000000000000000000296c0000000102f800000000001221e0ce000181a811944fe00018129a89a064de30000041d00000000000000000650000000000000008a0e0000000000080d200036390000000000000948000000182e00000000000000020000000000180760ba0000000000000002ac1017c81f843f800000000000000286881f8000000060820000000000000180000000103a800000000001068e0bba1ca05700000000ae2a000000000000000000000022f800000000000211a00000000000000008003a8000000000000000000060d381dea5240000000000000000000000000000020b340372a8e0000000703c000000000000000d93d8183049b2b300000001052800088bc000229c800000013bca0310000614a000123649240001022c00000005d200327abf8000028400000004cfe20ea00030bbe89400000000000667400000002779804180b6000000020f1d28301e0a94095d5277c1df09a80b3000000000000000000083980000000000000000002f0b88ca000201d80000000000376be22ed10c000001980000001806d02a800000000000000294581c70278000000044d8000323180008948000000000000001d2990aa0051c0b00000000000098a9cbcc000000000000003634f6b90000814c0006962000183b220400000000000244deeaf00010059089530f86040000000000000000000031e03841b40000000000002bc000000000002ae00000000000000003ac20c0a08f00010564000600b0000000000000008146000000060eb82d680ad0b60000d5520000000606b000000010aaa0d000000003046000000000000000000000000000000044000000003a5ce493013a13d485ac06700000000000000094ce0000000000000000000000000000000000000000000000001972a746000002e6b1900000000a3da0008000020a000104300000000000160e004b4238048802200000000000374aa26eddf200000000000444e00024b58000000000020618000000005cc494c16e000000024b4f45d00000002649202540a424f0000029f81b050a59708000004f04e2418800000000000000000000000000000295480da00000002960c0b2000228528330000db7c000000042c800000000000827 else 0x544a7a0967a00d00000000000048b4049aa4dc81b266f832a755e4975a6891a603de0f30000000205d0000007800000006b0984ca937c08d8000c23a000172dc12082c485110bc0000d135004146a00009caa0ad712e422f02180000000000000b400000006020000090400000000000000018bf800000000001b8900000000000270c800000000000000000000008064000000000000003037a17f009a000202100000001842c00010e40000c96c0000032c11a000109d250600000000000000000000000b1f42724ae000020848000000083d449700000a5013ec1a6f63a000000000000080000103b40000000c27a0000000000000009029a3b80000000000309a000000000000000000000005ca4000000000000000000016f455284440000000000000033830000000005c80000000000000034268000c94c0001777ad7c000000010960672815c5bac00000009a96000000020c10000a07a443d02e0001a501018895100004a54770000042fa00030780000413800000000000000185c00000000418a0000000413f000000000000000024fa24c07c8000119b23c7274a8a98528000000000000000000067c402880dc00b40000000c85785e4000166f82cb849400000001dc48cb400000000000000104a440c0001c38f200a56d48e2809811e00000000a2e40000000000000000000ee4000085680004f6d000132500000000000000000000000409e000000000000000000000000000000827f003800041c5a33c0000000000000000000000000000000000000000180b000000002ada000000000000000000000040094ae391f800036770001a0c00000000c1ca00020658223000000000000000000105a4000000000012b4c00008f700000000000000041a92d3400005180000000106300004034000000000000000000079400000001838769c00000000000000000000000000209f6cbb000000010ba800009c000000000000d1e0000339300000000253f49e8103c28600014468000000083780000000000000000000000c022000105e0d80000184ec00))
def gE (j:Nat):Nat:= 0x7ffffe000017e010944e400000002fff97991d6494e800fff0000bf2a0c06404fe000b950499fc055100a38000fe26242400007ff2f09a1617fe00190c05617fe060020549117a2510a3384a4e9fc361524e0fa3e03e2f90c3917e5f1502d8f646c410d9f27b984791dc0c01203002050200401a01860138764508e288c86a0501f82c0f0261d0c613066170243d028168d6760620381e0d03a02096070421100a200a83101600004060900a823d1bacb1eeca4d18860005916050130481100c020043ff
def gK (j:Nat):Nat:= 0xd07800000000010b16ef035b8d00060d400000041c0000000000000000000100a00000000000000000000000000000247b7329af1074e2801b30d892800173a92a812c0b102511f000a24021bab101200006500000000001016000000002201800088e6a840008155ca08d000081c24b80024100000000002054000447800000000000000000000000000000000c3d456800107600000060f4000000000000204200048c2287204000000289800010be8a000000000000000000000000000e38000000000000300c2320000000000000c02800000000000060d20238200000000000000013800000000000480000000000000000000a1c0cb9688000000c19c4741080008018000a3000040200000000020000248000a2900060fc00000001f0000000000000401c000000e990cac65c000811808800000040c80000019054908003750000000000145c00000020c00000000000000536000516e8a80000000098003078000c8d000203a0000000002456000000000063b836000000000000000000000000000001058000000914000000000000000000000000000000000000c5cc274000bb9000000000000000020c5114000000000000000000000000000004830000000000000000000002600000000000005080ce400000069160ca1363b7017000102f039000645346000001480006151a0650000016e1010000001050000000206c0000144076040b30037c07c0022620000000000001bab88000af05a0000002cdc000000000000000012200042a315e000105800208308e0000000000000000406000000002060e80000000004c380000006c860bc24800008d8003534000000103503d10cc0b000000000091a80000000000000000000000000000000000000062e000088d000244800181f00c600880508000114000100510020081c0084222500080020
def gF (j:Nat):Nat:= 0x403103b437ff
def gL (j:Nat):Nat:= 0x3040022200000000000004200000000000006700107c08000000000000000000020500000000008cc000000000000951970000095f06002310000000000000005c40000000000000d000000000000000145000000000084c00000000000061c0000000000000000000000000000000000127000000000000000001140000000000000000037300000000004dc0000000894000000000000000000000000000000000000000090000000000000110000000000000000000000000000000000000000000000c44000000000024000000000000000edc000000085c0000000000000000000293000000000054000000000000000000d1c000000000318000005dc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e000e980000000000000000000000000000000000000003a70000000000000000000000000000000000000000000001c03000000000000024600000000000000000000c0c000000000000000000000000000000000000000000000000017400000000000012100253000000000000000001860000000000000000035100000000000000000000c04000000000000003080000000000000000000000000000000000000000000000000000000000000000009800000000000000000000000000000000000000000000366000000000000000400
def tX:Nat → aC
 | 9 => (7,6,9,393221,51,6,4096,nH)
 | 10 => (182,5,9,5963854,119,11,4144,gA)
 | 11 => (820,4,9,5898424,120,14,4465,gB)
 | 12 => (386,3,9,1769521,86,15,4664,gC)
 | 13 => (66,2,9,655368,67,13,4360,gD)
 | 14 => (9,1,9,65537,0,9,4180,gE)
 | 15 => (1,0,9,65537,0,0,4099,gF)
 | _ => bi
def uq:Nat → Nat → Option (Nat × Nat)
 | 10 => bY 3 61 1 8 3 3 gG
 | 11 => bY 65 977 3 14 8 4 gH
 | 12 => bY 353 1741 8 16 10 4 gI
 | 13 => bY 199 1993 4 15 9 4 gJ
 | 14 => bY 40 409 5 13 7 4 gK
 | 15 => bY 12 431 1 10 4 4 gL
 | _ => fun _ => none
def mo:aM:= ⟨1535,15,fun i => moY[i]?.getD (0,0),moC,moA,tX,uq⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma w0:aV mo (aI pri) = true:= by
 simp only [aV,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,df (d:=6) ?_⟩,df (d:=3) ?_⟩
 all_goals simp only [cA]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nL:ba mo 9 0 7:=
 (@ak mo 9 0 6 1
 (aO 0xce6632990c662)
 (cT 0x31401265))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nB:ba mo 10 0 182:=
 (@ak mo 10 0 87 95 (@ak mo 10 0 72 15 (@ak mo 10 0 5 67
 (aH (aG 9 0 0))
 (aO 0x225108743215088321a090242401fcfc000d8a43440001f400003e1ec32190c9e8f2193c1dc50000910408003b0000075200fc3074001cc24123909c4e710c1c0de6e369b0303f359a8d268)) (@ak mo 10 72 1 14
 (aH (by decide +kernel)) (@ak mo 10 73 13 1
 (aO 0x1c48915202a47a38884446a31168a)
 (aH (by decide +kernel))))) (@ak mo 10 87 52 43 (@ak mo 10 87 11 41
 (aO 0x2592a1c4a24c381c490ac562b) (@ak mo 10 98 2 39
 (aH (by decide +kernel))
 (aO 0x2bd5cad0012158ab0f07404aa548a1504753a9804285281082a42328d44a15027d3c9d4e26c08044d2653097))) (@ak mo 10 139 39 4
 (cT 0x65a530108746a23284b6838365ab401003ba0473656b4010a36b4872374672326561301009365573565a30707868a29109065573314312767b4b8964654b3196891b5ba3654131968786a2108786a2218786a2218786a221929b0761565630708786a280656030966565309665653096656530967868a2918786a2218786a29114a1901053341271533412715334127113ba04725334127126b43076) (@ak mo 10 178 1 3
 (aH (by decide +kernel))
 (cT 0x76b97121426b234314a59010)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nC:ba mo 11 0 820:=
 (@ak mo 11 0 504 316 (@ak mo 11 0 399 105 (@ak mo 11 0 112 287 (@ak mo 11 0 7 105
 (aH (aG 9 0 0)) (@ak mo 11 7 96 9
 (aH (aG 10 0 4))
 (aH (aG 10 0 0)))) (@ak mo 11 112 192 95 (@ak mo 11 112 96 96
 (aO 0x92f00402002ed74000000400040013000000012d7200000080802020117002010085ab7168b40a05028140a0e070381c0e0007c1c0e160b0584a2504c020109820261309ad96ab4040041001040201005028140a0b05801664924868000b59068361a028140a05042c410b0)
 (aO 0xe0766921981e0f32c3c526507c0c500332406090488812c8148bc0c09048258e216308464c527800420310b10a215100542ac3610c02a200a880a2c118b006031188c0a02f1793c280c270b800000000000bf5f13402000312c24bd)) (@ak mo 11 304 94 1
 (aO 0xb2451a8ddc0df1bb78b0dd6e160683721b6c64571b0306c0c1a95c6c0c04b688c356c959b0221a154a8d72a359aa5329b51a6d268b400ccf6708c0c0201000000000000000005800360011800000000800020100804360011804660003000000b058001008040601000)
 (aH (by decide +kernel))))) (@ak mo 11 399 23 82 (@ak mo 11 399 2 21 (@ak mo 11 399 1 1
 (aO 225)
 (aH (by decide +kernel))) (@ak mo 11 401 20 1
 (aO 0x74ba01e200789c1e0f1739dcce507b91c60f06030b2e2)
 (aH (by decide +kernel)))) (@ak mo 11 422 13 69 (@ak mo 11 422 10 3
 (aO 0x683276bb070071c3ac70ea)
 (aH (by decide +kernel))) (@ak mo 11 435 68 1
 (aO 0x20080c0201412070203170b9018004400ff000000803023f9fa5b0b3f1f6fa7c82412f87b8582cf60b3d42c0a1d3d0183a0a3cde4147883c7409048a8545a2b3c1de390a1385c090a03018ee)
 (aH (by decide +kernel)))))) (@ak mo 11 504 195 121 (@ak mo 11 504 89 106 (@ak mo 11 504 5 84
 (aO 275146343483) (@ak mo 11 509 1 83
 (aH (by decide +kernel))
 (aO 0x48e45219047e3c000002ca41f8e81e38000f80004178d85c463b0b80a341d1dc64be5f8c05c0000000080517030f402000b800aa428b08a2b140180cbc2489c4a223d0e8f03a3c1e168bb102ec3e1d0d238e4730c85c2a130883c1a0a04))) (@ak mo 11 593 3 103 (@ak mo 11 593 1 2
 (aH (by decide +kernel))
 (aO 150308)) (@ak mo 11 596 96 7
 (cT 0x8796a2328746a2328746a23214a190103183123214ab901065ab401076b8612165ab301076b8612165a1401070b9a12165ab301065ab301065ab301065ab301065ab301070b8a12170b8a12126183121754b297565ab301076b8612165a5301065ab301065ab301065ab3010658b301065a1301070b8a19170b8a19170b8a19170b8a19170b8a191133912a2133912a2133912a270b8a19135ab043070b8a19170b8a19165ab301076586121765861217658612165ab301065ab301065ab301070b8a12170b8a121a1b68661a1b6865076b86121765861213146129270b8a12170b8a12190a055403bb618978796a2218786a2218796a2218796a2218796a2218796a2218796a2218796a2218796a2218796a221a1b68650531a04937658612153ba0493a1b6866153ba04938796a232531a0493a1b6865076b8612153ba0493a1b6866103ba049353ba0493133912921339129214ab901014ab901031461232314612323146123214ab901014ab901014ab9010426b234335ab0440426b2343)
 (cT 0x8786a2218796a2328796a2328796a2328796a2328796a2328796a232)))) (@ak mo 11 699 72 49 (@ak mo 11 699 40 32 (@ak mo 11 699 1 39
 (aH (by decide +kernel))
 (cT 0xb67b0a8656b6308070b9a121560a3080560a3080560a30808786a2218786a2218786a2218786a221093a55848786a2218786a2218786a2218786a2218786a221093a55848786a2218786a2218786a221a1b786508786a221754b29648786a2a2a1b78651a1b78661b67b0a75a1b786518786a2a22619318126193181261931817868a2a226193181b67b0a75261931818786a221b67b0a75a26a2872)) (@ak mo 11 739 1 31
 (aH (by decide +kernel))
 (cT 0x754b296426543121b4a49550b4a49550b4a495508796a221a1b78650a1b78650a1b7865046ba7080a1b79650a1b78651b67b0a86b67b0a86a1b786618746a23242642343b67b0a8665a14010b67b0a86b4a495408796a232319612328796a2328796a2323146123231461232656b301065613010b464b550b67b0a86))) (@ak mo 11 771 4 45 (@ak mo 11 771 1 3
 (aH (by decide +kernel))
 (cT 0xa1b68661929b07728796a232)) (@ak mo 11 775 1 44
 (aH (by decide +kernel))
 (cT 0x70b9a121946475503746723294a4755076b9712176b9712170b8a12165ab30108785b23270b8a1213185123265a530107058a12170b9a12114ab901065a530102659312126193121658530106585301026193121261931218796a2328796a2328796a2328796a23265a0301014a0901065a030102654312165ab401065a5401065a54010a1b6866165a5401065ab401065a5401065ab40108796a232656130108796a23270b9a12170b9a12114a59010))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nD:ba mo 12 0 386:=
 (@ak mo 12 0 311 75 (@ak mo 12 0 265 46 (@ak mo 12 0 233 32 (@ak mo 12 0 62 171
 (aH (aG 10 0 3)) (@ak mo 12 62 96 75
 (aH (aG 11 0 4))
 (aH (aG 11 0 4)))) (@ak mo 12 233 10 22
 (aO 0x4d0013004041f0f87d26) (@ak mo 12 243 1 21
 (aH (by decide +kernel))
 (aO 0xb0582c1601030180c0000000020703ca423280680c4527)))) (@ak mo 12 265 31 15 (@ak mo 12 265 1 30
 (aH (by decide +kernel)) (@ak mo 12 266 29 1
 (aO 0x12c050925600000000000000000000000000001008040224008040201148cc672a)
 (aH (by decide +kernel)))) (@ak mo 12 296 13 2
 (aO 0xa0502a5c0a0516c140a128284b2d) (@ak mo 12 309 1 1
 (aH (by decide +kernel))
 (aO 10))))) (@ak mo 12 311 25 50 (@ak mo 12 311 14 11 (@ak mo 12 311 1 13
 (aH (by decide +kernel)) (@ak mo 12 312 6 7
 (aO 0x4a0a08040212f)
 (aH (aG 12 0 0)))) (@ak mo 12 325 6 5
 (aO 584087983513613) (@ak mo 12 331 1 4
 (aH (by decide +kernel))
 (aO 4857161824)))) (@ak mo 12 336 9 41 (@ak mo 12 336 1 8
 (aH (by decide +kernel)) (@ak mo 12 337 7 1
 (aO 0x402026130982026)
 (aH (by decide +kernel)))) (@ak mo 12 345 22 19
 (aO 0x2261068341a250680c06030183406039a97806030180c1a03) (@ak mo 12 367 1 18
 (aH (by decide +kernel))
 (aO 0xc33b9d4e671370381c0e070381c7b36038442211))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nE:ba mo 13 0 66:=
 (@ak mo 13 0 5 61
 (aH (aG 9 0 0)) (@ak mo 13 5 18 43
 (aH (aG 10 0 1))
 (aH (aG 11 0 3))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nF:ba mo 14 0 9:=
 (aH (aG 10 0 0))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nG:ba mo 15 0 1:=
 (aH (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tY:bS mo 15:= by
 intro k hk
 interval_cases k
 · exact as mo 0 0
 · exact as mo 1 0
 · exact as mo 2 0
 · exact as mo 3 0
 · exact as mo 4 0
 · exact as mo 5 0
 · exact as mo 6 0
 · exact as mo 7 0
 · exact as mo 8 0
 · exact nL
 · exact nB
 · exact nC
 · exact nD
 · exact nE
 · exact nF
 · exact nG
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma px:az false graph 15 inputs.toFinset:= by
 rw [show graph = bo mo by decide +kernel]
 exact ol (g:=mo) (top:=15) (i:=0) (ag pri nI) w0 tY (by decide) (by decide +kernel)
def lL:List eC:= [(151,5,94,[48,33,133,118]),(173,5,61,[32,83,116]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(247,9,478,[48,33,133,118]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(369,5,94,[16,82,131,100]),(422,5,61,[32,49,128,81,116,100]),(440,5,94,[81,130,118]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116])]
def spri:= qF lL zT
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma vspri:Known true spri:= by
 apply vZ s1
 apply df (d:=6)
 simp only [cA]
 repeat' apply And.intro
 all_goals decide +kernel
def sgY:Array (Bits × Bits):= #[(0xf4e2669a6837f027081c0f22055df808222736,0x40209409843f007000c0720001df800000733),(0x601c324b069010597803f9010a2609fbe0181f,0x2080a02e269000187801f800000000fbe0180c),(0x250f0dd0188027ef8024025e13c1fd105e4930,0x22808d1092003e78000000e03c1fd001e4031),(0xc9c0d906874040901240ffc4fc1e1027e41fc0,0xc0c0010ec000000000007fc0fc1e0003e01fc0),(0x1028d4b1279c83fa01f1902f20e021fc806260,0x1028d4b1279c03f801f1800f00e001fc006000),(0x86910025492109002481248fff0841ffff8000,0x9100a343a000000000000fff0001ffff8000),(0x81412a020041fe000ffffffe01001009,0x814120000001fe000ffffffe00000001),(0x28004905ffc0481fffff04000804208c000,0x28004905ffc0001fffff000000000000000),(0x3a518020b05fffffff08400880910680110480,0x20aa0103c5ffffffe00000000000000000000)]
def sgC:List aZ:= [(64,0,447,0,13),(128,0,383,0,13),(256,0,255,0,12),(32,0,479,0,12),(4,0,507,0,12),(8,0,503,0,12),(2,0,509,0,12),(17,0,494,0,11),(7,0,504,0,7),(16,0,495,0,13),(3,0,508,0,9),(32,1,460,18,7),(16,2,424,69,7),(9,16,486,0,8),(0,32,94,385,8),(16,4,353,138,7),(4,8,227,272,7),(0,8,227,276,8),(2,1,460,48,7),(256,8,227,20,7),(14,0,497,0,7),(8,4,369,130,7),(5,2,440,64,6),(16,256,135,104,7),(10,4,369,128,6),(258,64,189,0,8),(34,1,460,16,6),(28,0,483,0,8),(0,16,486,9,10),(260,8,227,16,6),(0,64,189,258,10),(9,0,486,0,8),(36,128,347,0,8),(260,0,251,0,8),(35,0,476,0,7),(256,32,94,129,7),(4,2,440,65,7),(0,128,347,36,10),(56,0,455,0,7),(32,256,151,72,7),(1,32,94,384,7),(40,256,151,64,6),(11,16,484,0,5),(15,16,480,0,4),(36,0,347,0,8),(2,4,369,136,7),(258,0,189,0,8),(64,1,396,50,7),(268,0,243,0,7),(8,256,151,96,7),(13,16,482,0,5),(33,0,478,0,9),(11,0,484,0,5),(134,0,377,0,8),(13,0,482,0,5),(8,16,486,1,9),(273,0,238,0,7),(264,0,247,0,9),(44,128,339,0,5),(1,16,486,8,9),(352,0,159,0,8),(289,0,222,0,7),(2,16,484,9,7),(39,128,344,0,4),(256,64,189,2,9),(128,32,94,257,7),(3,128,344,36,6),(20,8,227,256,6),(48,1,460,2,6),(32,128,347,4,9),(37,128,346,0,5),(259,64,188,0,5),(265,16,230,0,5),(2,64,189,256,9),(4,128,347,32,9),(16,8,227,260,7),(296,0,215,0,7),(64,2,440,5,7),(64,256,151,40,7),(72,256,151,32,6),(96,256,151,8,6),(257,32,94,128,6),(41,16,454,0,5),(44,0,339,0,5),(69,2,440,0,5),(266,64,181,0,5),(19,0,492,0,8),(49,0,462,0,8),(152,0,359,0,8),(128,1,332,50,7),(256,16,230,9,7),(4,16,482,9,7),(8,128,339,36,7),(16,64,173,258,7),(6,16,480,9,6),(136,4,369,2,6),(272,8,227,4,6),(384,32,94,1,6),(73,0,422,0,5),(262,64,185,0,5),(265,0,230,0,5),(274,0,173,0,5),(274,64,173,0,5),(276,8,227,0,5),(292,128,91,0,5),(39,0,344,0,4)]
def sgA:= moA
def sgD8 (j:Nat):Nat:= 0x1000090fd30b281002edebeda1759cedd17588f587f42ef25c4befc9513fe9b94549814c153549814c120f055354930483a454d524c120325535493048198edda54c910
def sgD9 (j:Nat):Nat:= 0xd41b34204741039105268403991050687dc08000035a0a59104010c882ef4310000067a320057a1640060818013810000ee00cc600000e06504339883a8461d12300009020000d6071810004e6200037d944cd86b6100008d840000000001b6100007a21b040cbc70497c248c00000000022c200001d6090174194188a0ae1220a46f606496407a0b20804d9158ddc05c25881835e27c1360287f60f012425a06a0fa0547940142720dc000300bc023e00267e0487c048166021c94099e01470075e040680a3a00058063b2e8f8dddf68d834bcf32dc971dc22f3baed6b06b9a667a9ca619664a90a3a87e1783e007d1e072db66b9a5669926297c5b9665494a4b9204490a408f43b0e4370d4330be2d89d2307317054130440f03409c1f05c0089cbc22727089a9c0af06e8ba6b91e9ac6f94ae2e9aa8ba6a4771681fc89d1e9a42bc4899e9a22bc4848f2205ba67d16a5e45a9744f2dc10cb6d8e61a77b665eed987fb65e854d72dc658b71959bb7524e61431c64e8f052a0c949c2e5183b542a54903db8214ea0787a71d7e9c757a71daed063fb814f6e4427c40cf6602a18306960c009cbc46f1af0bcbb46f1ad19c6a05f1e705cb981f2e50dcb8cdf0529fa44a366101bc63c6f18e4ba5353e94c43b62c072ca03cb24ee9c797c703ff0ff63fd2ff0bf6afd63deaf3d39afe5bf7f4deeb7b6debb5fcd7b75ebd6f757ed5bf3afcdbf1efc77b1ddc6ff1afc5ff16fbf4afbabedadedb7aecfda7be9afa5be1ff87f61ef86fe17fea79460530e9b94605306eb94605306cb94605306a794605306d79260530ec59260530e519260530e515260530e63a464d20657a464d20aa7a6605206a7a6605206d79360520ea791605206cf916052064f916052054f9160520ed193605206dba154d206d8a954d206a4a954d20661a54c520edd954c120e91814c12054d814c120549814c120ec5534c1202e5534c120e91524c120e61524c12054d524c120605514c120605314c1206a3a464d10663a464d10ec5a564d10ec1a564d10ed1a960d10aa7a7549106a7a754910e9f9354910ed19354910ec99354910e9d9354910e9d835491064d8254910edda54c91054d52481105495148110
def sgH9 (j:Nat):Nat:= 0xbb000000000000000000000000800000000000c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c500000000000044020000000000000000000000000000000000000000
def sgD10 (j:Nat):Nat:= (if j<2 then (if j<1 then 0x9c72fd9472fd9462fd9454fd24567d9c42dd9c42fd94459cc4421dbc32dd9c325db4258cc422dd8c183d24185d24069cc4089c9c01bdcbf1a5cbf2ddabe83d23e2cdabe8ac0be01dabd01d93d3fdb3c01dabc01d9bc01dc3b01dabb00dd3a00dab900d93900dc3800d93841d43741d2b740d43740d2b740cc3741d23600dc3600dab663d2354fd23511db3419d8b41bd83419d8b31bd83319d8b241d23215d9b100d9b000dc2f00daaf06daae42d42e42cc2e11db2d19d8ad13da2c19d8ac11db2b17d92b13da2a17d92a00dd2914d9a941da2815d9a801d92845d82800daa706d8a708d82700dca600dca500dd2400dd2300dd220cdc2216d9223fdb2101d9a117d92143d8a107d8a145d82109d82101dd1e13da1e08d81c3b5c9b3b549b3adc9b3ad49b00dc9a3bd39900dd1916d91803db9709d81701dd1513da1517d9153bd39500dc9200dd1100dd1014d99016d91001da8f41da0f17d90f43d88f01dc8e03db8e00dd0d32da8b8ea90b2fd90933d88921db8833d88829da0733d88725db062fd90633d88663da0529da0569d9052fd90571db8169c98168c9817ca9818ed9003dd37778a9c07aa900ffe7febff1ff6ffa7fcbfddfeaff37f7bfb7fdafec7f4bf7dfaffbdfdebbfddfdefdf7ebbeddefef776ffb7ddbdebff3fb9fbbfddfdefeb7ddbbfdd7edff3ff9fecfee7bf37f9afcbfe3feffd7fdbfe5feeff57f6bf7dfbaf7f7bebbfddfadfd5ffaff57f6bf75f7af7d6feaff4ff9ffcffa7fb3bf9bfc7fda1e51306a3914c1a5e453068b914c3a264530e81914c39464530e51814c39260530aa5814c1a960530649814c1526053068f98481a8e4d206979348198e4d206a391481a3e452064f9148153e4520e8598483a06612068598483a864d20e91934839864d20661934819564d2064d91483a960520e9981483a360520e4d814839160520aa581481a96052066181481936052054d81483a154d20aa553481a954d2068553480a954d20e9531483954c520aa531481a94c52069531480a94c520e9130483a14c120e6130483934c1206a130481a54c12068530481984c12065530481814c12054d30481524c12054530481314c1206a393441a8e491068f9244183e4910ea193443a564d10e9193443a264d10e8193441a864d1069593441a264d1066193443a864910e8d92443a1649106a192441a364910661924419364910aa583441a960d10ea582443a560910e8d824439560910e4d82442a9609106a582441a56091065582441936091054d82443a954910e9d52443a354910e4d52442a9549106a552441a35491064d52441835491060952443a54c910e5532442a94c9106a532441a54c91065532441854c910e852044393481106a120441a54811068d20441984811064d20441854811060d204415348110549204415148110 else 0x732dcb87285c74710dc116f71bb66df5b536ca1b036b45ab66a01a5968f5a0d67ed9df66e99a3661595664798f4633d8ae6209858608d8025f457a65e217765d657325c316f65b0969a599962a58355f057415ae562156b553151d53f54e152f94a751d945250713f74f713bf4e613744d493294bf52e54b212ad4a3125648b51fe47251a045e914744610e242e5083417104740c8fff3f08f8a3db4f3f3c20ef03b40eaa3a44e753974e423880deb3740da73604d4e34b0d0d33bccdc3338cbb32b0c993200c6d3178c1e2ff4bd12eb8b7f2da4b342c30ae42ab0a7d2940a2a27c89d526e0993259894024948f423748b4223885e20d48061f547be1e307621c906f11b406af1a1065118645ea16a457d152051113dc4de12e848d11ac44e109c3ef0ee439d0df835c0cf03170b7c2ba0a50275096422d07ec1d706d41990584142046c0fb033c08c011c00075d37764dd7764d97764d4f761d37647d2f61cdaf635d8f34dd37365ca7365ca720bdaf01ddaee1ddc6a0adae61cdae447d4620adade47d2dd1cdadd6cd9dc34d9dc6cc9dc6ca9dc2bda584dd3584dd3571d5cd61cdcd60adc5626db5646d4d647d4d51cd8d51dd8d41ddcd31c5cd326db5246d4d20adc511cdc500bdc4d46cc4d36dac937dc436fcc4377db4237dac287d24293c8c28ca9c290a9428dd8c18c5cc191cc406fcc3f92c0bf1ddaba46d2ba0adab954c1ae1dd9ab2ada270ad9a734d8a70ad9a647caa50adaa546caa51cdaa30bd9a135d8a123dba06fd81f37d81f1dda9e2bda1e0b5d1d0a5d1d0ad99c48d99b0adc1a1cdc1931d91649d3961ddc1565da152bda156bd91531d91547d4155bd39549d39549d3941cdc947fda9373d39353d1936bc9936ac9937ea9930adc121cdc111cda900bdc0e49db8e23db8e53d90e31d90e47cc0e46cc0e1ddc0d6fd80d37d80d47d40d46d40d46d48c92c28b92c18b92a98b6ec28a37d9866ec28537d98437da8337dc0236dc0280c2828cc18290c18192c18013dc7e13dafe13d97e40d47e40d17e01dafd01d97d01dc7c01d97c01dc7b01dafb41ca7a63ca7908dc7941d47841d2f841d4f74bd377415d7740dd7740d4f73fd37600dd7618d8f513da7419d8f401daf101d8f13ed37101daf001d8f001dc6f3bdbef0fdbef01d8ef01d9ed01dc6c01daec41da6c13da6c13da6b00dd6a00d9e951d16859cc6808d8e811db6741cc6541cae540cc6540cae510db6439d46313da6108d8603f5cdf3f54df3edcdf3ed4df00dcde3fd35d00dd5d0cdc5d43d4dc5dd35c56dc5c18d9dc56cc5c0cdc5b00d9db18d8db05db5a19d8da09d85a1fd85900dcd604db5600dc5514d9d515d9d400dcd108d85100dd5014d9d000dc4f00dacf14d9cf18d8cf19d8ce01dccd00dacc63cc4b62cc4b50a94a5edb4924db4983d2482cdac866cc482dd) else (if j<3 then 0xe4f6b20c7814441e1d451138b15a449c588f812716293ca51271623e05bff5e71e80004a953c8a9a459fe26100b479e6c1468ddfe98200ad9b491435fc749640392497af884632975f8851b2afaf290a0039a51fd71c00842adff313009a3afbd610a12bf3ea1000028954ab2c268c98892a9c0f0851b7fad640688f4f8ea51944788225cff6e4d44ab3473423dfe8544ea32fad612a1519571c001acf5f62000d6605b93ea1350bdc7f08e8ac6680ed451ff856c045b31974f00c6525f0db9a2b510b34dff2e9900732a9f140522a7f109d90bafb884e335ff2e9900232acebae2880030691fea3ac8568fd970d6e7a102216adfa19c03247bffe3b1a012155ffe6d8900252b6bc70151f280b4f7b0644e3f5c110354753c24268c7184688b5dfa10c26dcde451942361eeffc76340242bd9a58445fa11a890defd632456194b267895c699402c5f94242721d9f8398d0833e0f4ca2f61ce66484fa463668a5188b850fff406a0a99b9dd8706123ec50d6484fa463001dd5c92462875fa106881d3cc04d95de4e660f9d02d806a1403c230fe348813b497c71e746e180115a803d3f84143b0039b52ae0b416c330642372809290150513122a37602c251018081260a1089e1382084285c1b0a061841b60087104c0430a60c3018430c178271890642646040760887c15857876a103085f137c0a19a0ac14c964251ca0e483c178550746e42c82b12478800810a72041d03c09747c8fe890a013c5704da07218528aca04c180699c06aa7bc2051141607024831134264c806060a0306d04052a15c230a828109c0f8341a0f94c844086e19c4a0805c0841b01b814470208380584248550d07a09ac001fb0809e06804d02015c2d0a05e0d00e81460e0730302205a0c5c10250500934000ae0b6180d01e030059c060702a08f41b83b0404e04002b0b60c01812d0ba180b80bd05c134201002203fc4f0601003007707f01e07383cd6b329cbe72d9caef29dc9fb258c8a3200c7971ccc6cb19ec5f7157c50f12fc3e70d6c313097c1d7056c0a300fbfd2fe0bf42fbabe12f70bd66f42bc8eef1bb6eeabba6ee7eb9bae52b8eee1bb7eedd8b722da6b626d6bb556d37b466cffb3aacd5b302ca4b246c80b17ac48b0cec1db022becaf1abaaae2eb76ad82b47acdeb27ac22af1ab72aa2aa36a66a946a33a8729f4a75a9aea63296ba53a92aa40a8d5a2f6886a1fa866a17a84ea0ba826a0467fa9f9a7d19ec27979e1e7779d467299c4a7029bca6dd9b066919a2668199ca66a997664c98f662e987e61097e25e097625d096be59095b2542946a4e492a2472910e40b8f563b88e8a3828db63588cae2f28b3629e899e22d87fa1d786ca188852e11c83a20ab81c20338021ff57ee9f867d81f3b7c35ef37b65ea779c5e427859df17721d8b75d5d4a747dce6 else (if j<4 then 0x120c1a341832eea18f40f0481e622cf3147d30b1c7162e5e0c5daa6d462e8c16b960addc822f8b105b2931f31e2d03091f4c2c66f41a20f5cb056ee415cc87088e848e84de83441a3d1822f8b10000d7fe0b4030fae582bb91eba5485f162b2b9a20f6a5d13d539230d2581e050698af46a2cbe065e6c2607cba5919287107cc3265908a71b8211496d9b0356085e1d8c205392c0e83170e00319d4401338329be1106005f16207c904196c45f16202ee9251c8c930a570657040cf9f2d8462055d24a407c904474247434cc828fa616306347f5199850000170201341a9e0fb81f703ee07dc0f2de6170de61000049d5f1a8c58d5cc1909f50742057e27916ca00067ae3483f35e880031a4d7e5a7400002a348f8fda2000c4927fa87b018ca77e4f06c002512b7e751b000234997203419bd3054d87ccc96c38257cc163f340008a17a195aff4882ed00003e078400ff468018cd4fc40240002a1c13f84e5a4415683f924e00485231d0e24518dfa104f0879fc7c4d13c7ff83800001cda4feb2e002a152bf5dd120064377f863800001cda63f947000004234d7fd238000009da6bf82e045b2d76625fff8a9a8010693bfe68a0010892b76f84104d7dbc0b89dbe96a401c6611e990c47a64355fb658009926f9ff61b00842aef9f4d0046cc4fc0c00270a6eed00d841538591a239bfaa01878003a23df9821f88b204a8e3f40e40111d9d3e611a801d0e1d3dc9321b12de90404b67b00d42c317c8d8052180efcd2101c864ffdefc441133adbde1081209ffa4bab00c683fafc208ca33e18a04eb33be4401a123ff2c38919663f0dc499e1fb34a041b3c9d86a41a4b789425dff314003c483580f5e4060e9f2f1044eb7a4139c034833cce3d8106534ff0922420630fbad6b019238cdad08d1a6d68468bbf43320648fbe30a811a3afd6124801cd2adb793a4dbf34500028495d2eb004a8f49c4a931ac065c3e66358fdf0a6127cb780b13dd37444ff08082c270c17c808034845b7c03c02ace14b7eb8a50042d2ce1c6839e52e227759543227b7930c95db3930b2c3750a0e67ac4a2772f5b142166d3a76245d3cdd448cf961ac87ac88d1f90808c450d0d1b12d089fd25511813b40738a28d9503f331d3c6e20fae91206d2039f503424f284428a985de38366eb4305c4a66dd8dc2a78dc41a07e9634c3d17326fe31a8000e69371f10085298f63d64814cebfcea40007349bbc4804294afeb6050137fcba6401cca8fbbc48032950ffd1a8000e69371f10085295ff83500009d256bf5c3a04db0e095f3053dc7fd8402d239f062d190001711afc8c93000150f2e406835fefec00511e7fc50e00041a491d4d123e41341d9fb6c164f3ec1439e096445ec1435c12c891f5813322631e5e80071a27da1225de240214a57f5b02809bfe5d3200e6559f else 0x35dc301da928e045843494f16eb6ec185024fe49088a5271834836ff1a18d5bbe2838d254cc8afa7e714205ee1ae601d2ed91b4e9d275ba9632bc6d10d6a886186c4e59c62a382b6c7d210d508db298808feae8ea0386ef8e342c91a3133e3416a2e172f7304a3ec1072c8427d312ac42d0d73093d3331d32c11b117a0f0400031fe5d4543734c133e58267cb0505e2b99012fa25142286a75208df895ef70614d88a93ca2c66c44401e8c6c7a68a281a0a8fca33668daf580cd1cee0b43ea26c98f0a483b480ca0f51782068d)))
def sgH10 (j:Nat):Nat:= 0xc00610b72b813515482944203880e207a351422c16800008701a0004eaa05fa2f400a0d0001237c1e000361303240f8000132821414a8a707e017956201f74b02a99f60b903701281ee061047806088800275c000000010617800281ccc88717bb381380b008934101d001005000081def00044000000489c03ba2d4058000151040c198025a80bbd408a4b3060008802a03b04d19900060af06a00cc1b40350218034a1e8e8001889ca0606606e59780a800000083e0002094028024807ec5f04100a8c0605800103100000009828e7428a14542800e000810e6819a12007908005916
def sgD11 (j:Nat):Nat:= (if j<1 then 0xbe0f07e2408e0381a80a9c2a5fe94ca46e8dba2ba88ca17e8189fa27c09e6a7589cda7169baa6b89a1a65c98e660f97ae5bd960654c949250193424af923646390f24158f8e3b48dd23388c3e2df8ada28889a223388221d4869e17f850211583a20b5822a0358019fd97ea1f7a7d41f287c1dedd7ac5e73791de257805dd576c5d86753dd127359c9f71c1c397011bd86e69b646c79ae06ab1a91699da2b67fd9bf668d980652d90f634d8ab61c185060557ee5e997895d857435c8d6f65b316a159e965358915ed570559555bd542549d5035351492518541a4f4938a4d5532c4bd12bb49a1234481d1d0467115f44c90fa433908140f900b3f60fae3e10f3f3bd4eca3a64e7038b8e0b378cda43594d26337cca03180c262fccbb02db8b2a2bb0aac2a1ca4728149ec26e097b252091c23e08b521e08341ff07cf1e747841cfc70b1b646a019e464418345cb165455914b851513784b51208442101c3d20e743660d083130b982c70a8827d08d4206073018e053c12a042c0e0028c06c00e0000d3533d3253d2a53d2a70d2a6dd326cd2a6cd742bd552bd352bd342bd152bd3065d3524d7523d74a3d7463d3523d34a3d3463d32a3d3263d2a63d3462d3262d3062d34a1d32a1d30a147514474b447454cf41473314732b4732549f29377253755337353373472434727351143511734b1434b17331173510435107347043470733107327072a704746f7742f4742fcf40f7342f4750e474ae9f48e4742e7730e772ae7330e732ae7330d7326d4752c8f4cc4746c7726cc722c7552c7352c4352c7b30c4742b7552b7352b474aa772aa7552a7352a434aacb40acf309cf2a9cf229cb509cb4a9cb429cb309cb2a9cb229cb029caa29730677750647506774a6474a69f4867744647446cf40673506734a67344673306735057346573305732a573265755247352447523474a347463772a377263755237352343523732a37326347522874e2474627726275522735224352273262b3042474a1772a17552173521434a1732a1cb500cb4a0cb460cb300cb2a0cb260cb0a0cb060caa605b43613515134b5134553f4145f2945f293534d2234d2134721343213511134b11343113510134701742f3f40f4f30f2f48e274cc6722c1552c1552b1152b1552a1152a974893f4296f309a72696b309a2a69aaa49a262913508134a81344813507134a71346717506174a65f4862f486174466f4063f406175051746567425374251352417523135231f4e213521bf4206f2606b260aaa40baa20034d20f486fffffeffdffcffbffaff6feffeefbff7feffdffdfedfddefdbfcffbffbfebfdbefbbfb7f9ff9ef9bfe5130e45306453060530e6120e4d20e45206612064d20645206052054d204c5204c120e4d10e491064d106491060d1060910549104c91048110 else (if j<2 then 0x8542afd71e6b0001ba52f32a1711238ebf7ff5900019256fc84a20ef8022451fe210c4033a489fdf9a32a01aa54ff9d546c4023a546f1303b14a434fce22a254693f9219251fbcaa48401349667f570b89f3fe98dc21988015dac77dd6892bf5c0388c3f133a274386132019fe5cc0e147f0fb81c46c3c7ae0468c7d61fab89efc9a20b945f7db09027299ff02a48006894bfea2802c8f3f1be002a8f332078ea32ff5c000511f31a0b1ccefe85a2d7961c802b662e4de5e45900215ab33f9a10046cf3f5cf8161c2400c93b7e7ff8030db40189377fffed4918b201a5317fcd41f4058903e67a02346effdd5880035684d3f9680000a344ebcffc1a9230090027505fe3cdf4015486fe2d5648b317a7c7e7088e67a4e4bc4488f684f0a1f860910bb4d70cb40095997f1baf9001e124b0f3eb22d957d7a4fb3604da00e4a1bff38138f3400992e312f6b400634373e862800568c0fc300699718c9f10a85d5deeeeb0c48001272fbb11e3d8c1a00849c7eff1005ca03a05d3c32ccf9e768b04664ff587950000099a7bba7b4b248f21b23238fe78c0c0200744b1fcf181804008e963f9e303008011d2c03ff113dcd30024b5c7c21267d400396acf8d1467d400396a9848fac4401492e381f10c01e3467fe3c48a0600786a4f3db1cfb1801e1a80bff70c70808185a833c3f1c202021698fcf40c02000536a3f3c00d13affff8a5820029a52f5febf0288010696741a0795af234006349def9a522a0049a61ff5b0e10922aec71c001c669fc002245ef98f9680cc00ced41dff8c0c0601769affd2450c0400826a5e56be300052495cfea000d23bbeb80000550c741a070ed79f8310000093597c32d02012b3cf88830004c923f903a5200784abfa7006451bf1534b4087499fc385c000d095b5fbe3dc202053a5df9f409c004e591fad02c44010cd23bf0a80751ce8340ebcac7cba0151247d99402c8fbf106d20159247ff1fca10401892a7caff00280212547e4fed141d8ae7f43fc6c01c91b1d78104024929b3fb454233f510c01a33cae7f000891df7a0d039fce00289cfe700144ebfea7fef0202002499313ffd00551d7958f1e400634a0fcfe7b0990a05a47dfc294020039a61fce00689df7a0d0387c5d40892a1f8e27406004925cf63660c00324b8ffb4301831671de3fc09801849c2604080631a2204f21b47e02200ae11603224341a6060f8671591c138c0820861304246e198d455064bc0e2891284041452a649e150060104911c46c0e81204844240e12031e183648017096800a0b9214370e9330fc334103b20d03c09020b82f08d0726d800782d0702c6041b8350d0cb05044266103000c020901f2082782805e118603e83280220ac99060290582a069894281007607e14210301502a8604813a11850500dc128260b82a170660c0 else 0x6793eb688648959a83db84618641099a63c740e409a479934f3f3214290c86effccaac81b307b7ad10a01a00b4fa2e200b4216d680b684ce5ebac8ab347f659b6ea4ab9476bced6888f666748473d1c6577aa891a102bc9cbc82839626a2f0aef5902b0fa5903fcca8341971d13a6892886c51cd17aeaa181e5210518597053a3085c82bba533230d968c235503e7852cdde12e1054384cd36f5eb152d5087ad577bd96597053a3080979abed48861dedce22cd713188a3e3bdc0e231cdb982328bd93305e50bffd5a740f240ff5b6202548eed6ff3ec60018698388e3e6cc0174a8bdfe00ea3484bdfe00f242e7f00051187dfe60016476edd4664dfcfa9e00112433962690c854a571ef6d0d675fe78800aa3edfa000b23d7fdb183000027699fce2e13a8dd40871d0b66dffb7e8002c913f9e1c2751a7ffff8deb89168800e69c7ee43840a0a674f18005c900eac208342861fe3c000d51f7ef000354795fae01c46087df3b2574eb8c98cac0186ad82cd9fc363b400013b4b393d9885c2bead62e10f8ad85013bfde0002a8f34efe348b35f7810311c08e9b3a901543f65f0da0488095a64ff23f0c000592b3ffa38440073457cb1ac01d66af973090005ed03ffd2f00016486e9100d0b669f32a37d4001152d3fccc050014686f84bf5c048000d5abbf949be800056699ff97e8802e480f2ccc78c64f8))
def sgH11 (j:Nat):Nat:= (if j<1 then 0x931828049fe42bc283841e02d972182e205d00b1c0aa0a6ea580092e0644ad55c4d284a03880fc040b33d80010027941c054eef74e2c00016b94095ca329413025e03495f80002ab801520a3400000002022117f049800000001c8a0000006842901a8000160d000001b7817007c6f400001003c03420dd023d028903294fe8079a28da44e527413c0003b160029d8ee000346776bd00e3912003ea0464207ad0400060e5416684f00006894c0f5dcc4233613e02400001b206136c1c182f488ce07302ae84a8449c0e81eab21f70a1e00c406c85a910be431803e824b68c8000096f913938c80cf8213c08c000494341268052054609952d40001b86406c1a0e52540002f4121438564241a148e880911406ce16e001c2214031e01c9d4c224a004a0495e9715160310e5f028881b40a2cc23003785603a0828c42a685a462f003781758258077e0d0c04a80ec000212c403100ce81ad7204892829841aa14ac05f01f1080e067c2c80002b116525c81a0001028211d42b4903204fa0400001dc8d30040ec829b5c90057a0ff415a1c1209de111d2cb821609be13f418d02db210887f081d82de203a16101e98441048813d89ef5c2b2904c7fc9b95c26681370b41c801fd0b780bcc9bb8168000012182ca22a3202000089c2a0110914172402dbd604516008000b831caa3062d0a0a256e76d2d6d000883470ad800000004813064c2869025a27d47ee900c0c20003020c0b2e5eea204000014e01e6911d097cf72ca579504000507700015c654578803000103e407380000100015b3172af9000000027a8e0b48a0600020666b002e2a857cb0c6052d941d370058c039c13a01200869530e0bcbd7776c6100025c03c04104146c1c4a51945ac8c5019704c922c972c81f601e7074800040993d1001fc0f251aa043c779494c5cf1113409a2027c143316d062e8ac0230825e20bae8e00950156034c076ee1004571a0ee8dd2801cf677c68a7e621dc3d779c112021da1ef0b3294280bc820c000085841e3985c441e08d95f5029c01ee00641b9008d270495f02d181830ab0948c2e0043105cf56c01fca0170420124480621e388d416d087e53cf047c0d6805c911840ae4f3e96c82286822130ae662bdb02e806e0156002db9380005176000aa22a139807c988e08b8135822635b962e02401130900028132a04800181b0341038078101800004502617008408a480700004040484c1607191205e731200418002280d404b0409016b9100841608070800008040082a20068497e8d02c84020e0b0dc0208010f4441c0a8186687148001608028a04411148088e3c0500c0a120501474200301c1c1604804642b010193a000180812011500c0e0b148183a0a0001c024604800120e080241c2f00884fa73060a400040f0000000000f80407010100048 else 0x403d05cc06901278235042c000484dc1120146043a0d5414a141a409c08280cd01614b420434a1d02534a4c0e1023f047000040c0c176b1e000d251881cd0313008642381fa836b7b5805942d981bd1410162c1ee221e0ae8138500e82c308de546029383d404e60fa002f83b409980004159853f57faca104fe80c8b0cc10480a7011c23e609b40e4023a09d2057c20c837d061a4fb82ce097502fe128405a2044000002b806b810b03bc0eb01a700c6027c12bee283a9407b457082a081ab44f015e0000325c066801941bd95b3b8892fa6c82002a07741084059a213082a119229b15c4026e52a52bd038c4a38f57828e520e01360ce029782fda7c467c4022a31d28a683900013a05022402ac28494020432114c0d682b80004003404982e345f609a510c00022920c9442800003094d32692c880740ae216b4024258a05f481402c1b36c0a88000c18484c60756081800e8116b11971a5ad6022c0270c6200009a6203c612dc22d31e800064b841b1829207e0000c0e8d2f706ba070ae0500a30aa60750194bd5a0aaa0c100600221091a0a3884f00840a6407b80400c5a40b6945c494805506414f6eac601500004098d83a82d6046403a412000030850000c)
def sgD12 (j:Nat):Nat:= 0x1fffd8340260acff0e695c049961e62b073fe4c016141fe7000114a5dffad88930b3f9cc984002f0b5f5c41d0287ff9b1146197fcf3084026557f2fd08004a1607ffb22804a15b7b883a0517e79a0c051961fdc2650006565f397220392bbf61c200251597fd3800c50edf80c0eff6c42184bff980a812ec02a04ada80c20de782b849387810f730d4217a60040a67f00a40b4fe2128147eb4e000c520b0ec3464260a09054395c884403f158243e1c0206832990b06214830d81a0a35038350906c32190589c24110a0ac28220f82c1e07012b63b45b865015ebb9d6f2d318c2e255ca292b2243e6708cc1782a44b0870f119c2d04a87309e0b00046468c0d3986726ce458cc31936322c6058a9b131632646488c1918222a444c85ca47918f309e4d3c8a5985a609e4c3c905930b2434801ca5fffff7efbff7bd3048110
def sgH12 (j:Nat):Nat:= 0x1094021e25e00490cc0ace241c14ea5b890b0ce4298000832c095c012604024e007811fbc0910205b0dd801f0a44000d42547e00014030212032800b034c2060d69b5a0978268000589140600032b100000008b2fab200000d44af1255010873a14ad051c028000026d08c410505f9d0109981104a6820c000503b250000000011fe0bcc294000ed6f05e09290c28180030000322b4242b4a41aa2b0c2ea7d4022f478c4e5a20593801e405309f8093a598e09050c08508880140cf9295bc51242010000306f00020d39f3f5a0920010940d604c428a0699e1e4afdecb10bd28f0bdc27b098d509009404f13fa5010270228017034b02d9ddf0b980f506d5a1002f59430be0003422c1f4000c18a016412b4aec95213a40de0d7c914476ed246bd0001b4ee82a4970a300bb402d77dc325956447b07e14b50c4011743002ce01510d9356c9641b30000275003b59d524c05490b97a20b00000c1d6076c1ba08280060a802d30396b1e0860c2200d989b485810d07942c164b8acb05943010c6c1fea5f9d044770c0804d45f10960001420c82701d0001008c170000aa40908d8fc028000107880fb04800e30d1d09800000030cd824800000030258184000413c00040fdb5fdc93bc8919f64d03057cb84be2bf000208eeb12a58806831e000204641f107429dc019ab2c19d5285bbd4060349029e24d01b106580e97d05e2327701c109d40f0bc719240bf015eb5841c976351230ae11e868503428830003a7581ae789415b479000002c40ec1499af201ca1432490214b50c226728d01c05a000249e00d903102acb6000000a0c08f02ac23c447c2db0b2a1610290124498d847b4f8329073c16263a000104e621b7d6534a0550002bc4107c080000205d493c0001d8848f49da077800c00000000001e0800082b1071c4910228b0c000cd437cddcfd08d000277548e624000030b1c4b4000012eb5501a00000001040c2a42440293000c2840000d4852f0b58000c14a0c3418f0aa804706641ee0af00030a341930c700016b2896a15000000ad82e301bc0aead600cc09c59280000322067c80c000409800659300b7290607aca0a1a0d2a400f96464968033020ac28686035702e02d568382479c15f4d68149990c50104002921771400253a01a1039b3e122e323b18a5010342351a2a03110000063202613702520603112a0e1a181d0665130005003b161e3d02160e02040c03200f01000009006d0c0e08010c0201130201070600011f08024b0509070c1c03010b1c0102002c
def sgD13 (j:Nat):Nat:= 0xe802012c810082004024341410281a1a16120a0e06001f36804c120443ff
def sgH13 (j:Nat):Nat:= 0x13ae07e26ca224c0000042410606e07dcc000000001c68540000090200000000c2e001030000000000000000130d6300090c000000000000000000000088c000000083f40000000000127e00caa0700000089a002370009ba000000000000000000000100e08c3c0848f4000000000020800000000000000c19ad500c0b000000000000011480009a00107400000000003448000000000000000185000000000000000000005bc000008348ac2280000084c002050008640b00800125c0061bc05038a780041200205000000c0c000000000000000000000397000d961100c44362122d0052001005
def sgD14 (j:Nat):Nat:= 0x10090e08185081808013ff
def sgH14 (j:Nat):Nat:= 0xc1009de4c0000284000045004a5c00c9005500000000000000000000000000000000000000000000008d0000000000d40000008c00000000009200
def th:Nat → aC
 | 8 => (6,6,7,327686,51,6,4097,sgD8)
 | 9 => (69,5,7,2818098,102,10,4151,sgD9)
 | 10 => (373,4,7,4849791,119,14,4299,sgD10)
 | 11 => (216,3,7,1769495,85,14,4244,sgD11)
 | 12 => (30,2,7,327683,50,11,4144,sgD12)
 | 13 => (3,1,7,65537,0,6,4109,sgD13)
 | 14 => (1,0,7,65537,0,0,4105,sgD14)
 | _ => bi
def uv:Nat → Nat → Option (Nat × Nat)
 | 9 => bY 1 113 0 8 3 3 sgH9
 | 10 => bY 26 127 7 13 7 4 sgH10
 | 11 => bY 159 691 9 15 9 4 sgH11
 | 12 => bY 102 467 8 14 8 4 sgH12
 | 13 => bY 16 163 4 11 5 4 sgH13
 | 14 => bY 3 59 0 8 2 4 sgH14
 | _ => fun _ => none
def sg:aM:= ⟨511,14,fun i => sgY[i]?.getD (0,0),sgC,sgA,th,uv⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nr:aV sg (aI spri) = true:= by
 simp only [aV,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,df (d:=6) ?_⟩,df (d:=3) ?_⟩
 all_goals simp only [cA]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rr:block sg 8 0 6 = true:= by
 apply bC (ar:=9) (rows:=0) (d:=0)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
lemma uy:block sg 8 0 6 = true:= rr
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rg:block sg 9 0 21 = true:= by
 apply bC (ar:=9) (rows:=0) (d:=2)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma p0:block sg 9 21 48 = true:= by
 apply bC (ar:=10) (rows:=0) (d:=3)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
lemma ut:block sg 9 0 69 = true:= (@aT sg 9 0 21 48 rg p0)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pN:block sg 10 0 3 = true:= by
 apply bC (ar:=9) (rows:=0) (d:=0)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma p8:block sg 10 3 128 = true:= by
 apply bC (ar:=10) (rows:=0) (d:=4)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma oA:block sg 10 131 111 = true:= by
 apply bC (ar:=10) (rows:=0) (d:=4)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma oZ:block sg 10 242 128 = true:= by
 apply bC (ar:=11) (rows:=0) (d:=4)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma oG:block sg 10 370 3 = true:= by
 apply bC (ar:=11) (rows:=0) (d:=0)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
lemma ud:block sg 10 0 373 = true:= (@aT sg 10 0 131 242 (@aT sg 10 0 3 128 pN p8) (@aT sg 10 131 111 131 oA (@aT sg 10 242 128 3 oZ oG)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pY:block sg 11 0 2 = true:= by
 apply bC (ar:=9) (rows:=0) (d:=0)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma p3:block sg 11 2 62 = true:= by
 apply bC (ar:=10) (rows:=0) (d:=3)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pl:block sg 11 64 123 = true:= by
 apply bC (ar:=11) (rows:=0) (d:=4)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma oQ:block sg 11 187 29 = true:= by
 apply bC (ar:=12) (rows:=0) (d:=2)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
lemma tb:block sg 11 0 216 = true:= (@aT sg 11 0 64 152 (@aT sg 11 0 2 62 pY p3) (@aT sg 11 64 123 29 pl oQ))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma qf:block sg 12 0 1 = true:= by
 apply bC (ar:=9) (rows:=0) (d:=0)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pP:block sg 12 1 12 = true:= by
 apply bC (ar:=10) (rows:=0) (d:=1)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pL:block sg 12 13 17 = true:= by
 apply bC (ar:=11) (rows:=0) (d:=1)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
lemma ue:block sg 12 0 30 = true:= (@aT sg 12 0 1 29 qf (@aT sg 12 1 12 17 pP pL))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma p6:block sg 13 0 3 = true:= by
 apply bC (ar:=10) (rows:=0) (d:=0)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
lemma uc:block sg 13 0 3 = true:= p6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pQ:block sg 14 0 1 = true:= by
 apply bC (ar:=9) (rows:=0) (d:=0)
 simp only [cells,boxes]
 repeat' apply And.intro
 all_goals decide +kernel
lemma tc:block sg 14 0 1 = true:= pQ
set_option maxHeartbeats 0 in
lemma uf:bP sg 14:= by
 intro k hk
 interval_cases k
 · exact (rfl:block sg 0 0 0 = true)
 · exact (rfl:block sg 1 0 0 = true)
 · exact (rfl:block sg 2 0 0 = true)
 · exact (rfl:block sg 3 0 0 = true)
 · exact (rfl:block sg 4 0 0 = true)
 · exact (rfl:block sg 5 0 0 = true)
 · exact (rfl:block sg 6 0 0 = true)
 · exact (rfl:block sg 7 0 0 = true)
 · exact uy
 · exact ut
 · exact ud
 · exact tb
 · exact ue
 · exact uc
 · exact tc
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma p5:az true graph 14 inputs.toFinset:= by
 rw [show graph = bo sg by decide +kernel]
 exact nj (g:=sg) (top:=14) (i:=0) (ag spri vspri) nr uf (by decide) (by decide +kernel)
def lY (i:Fin 9):Sig:= inputs.getD i.val zero
lemma oI (a:Sig):a ∈ inputs ↔ ∃ i:Fin 9,lY i = a:= by
 rw [← gt,List.mem_ofFn]
 rfl
def kh (i:Fin 9):Row × Row:=
 ([(3,2),(3,1),(6,2),(12,4),(24,8),(33,1),(66,2),(132,4),(264,8)]:
   List (Row × Row)).getD i.val (0,0)
lemma iO: ∀ i:Fin 9,
   kx graph inputs (lY i) (kh i) = true:= by decide +kernel
lemma m5 {u k s} (run:Live u graph k s) (raw: ∀ a ∈ s,a ∈ inputs):
   s = inputs.toFinset:= by
 ext a
 constructor
 · exact fun ha => List.mem_toFinset.mpr (raw a ha)
 · intro ha
   obtain ⟨i,rfl⟩:= (oI a).mp (List.mem_toFinset.mp ha)
   obtain ⟨p,n,diff,isolated⟩:= iT (iO i)
   exact ex run inputs (lY i) raw p n diff isolated
lemma nY:Lower true inputs graph 15:= by
 intro k bank path hit
 have plain:bJ graph = true:= by decide +kernel
 have init:inputs.all bJ = true:= by decide +kernel
 obtain ⟨j,S,hj,run,raw⟩:= gv iA plain init path hit
 rw [m5 run raw] at run
 by_contra! small
 exact p5 j (by omega) run
end PEqualNP.Outside.L_meta_4817.eg
namespace PEqualNP.Outside.L_meta_4817.aJ
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x:Fin 10 → Bool):Bool:=
 (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
   (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
   (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
   (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
def base (x:Fin 10 → Bool):List Bool:= List.ofFn x ++ [x 0 && x 2]
def inputs (k:Fin 12) (x:Fin 10 → Bool):List Bool:=
 base x ++ [!(base x).getD k.val false]
end PEqualNP.Outside.L_meta_4817.aJ
namespace PEqualNP.Outside.L_meta_4817.ch
open PEqualNP.Outside.L_meta_4817.aJ (target)
private def tf (p q:Fin 10):Fin 10:=
 (![
   ![1,4,4,1,1,1,4,1,1,1],
   ![2,0,0,0,2,2,0,0,0,0],
   ![3,3,1,1,1,1,3,1,1,1],
   ![2,4,4,2,2,2,2,4,2,2],
   ![3,3,0,0,0,3,0,0,0,0],
   ![7,7,0,0,7,0,0,0,0,0],
   ![8,8,8,1,1,1,1,1,1,1],
   ![2,5,5,5,2,2,2,2,2,2],
   ![3,3,5,5,5,3,3,3,3,3],
   ![6,4,4,6,6,4,4,4,4,4]
 ]:Fin 10 → Fin 10 → Fin 10) p q
private def fy (p q:Fin 10) (b:Bool):Fin 10 → Bool:=
 fun i => decide (i = tf p q ∨ (i = q ∧ b = true))
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2500000 in
private lemma nO (p:Fin 10): ∀ q:Fin 10,p ≠ q → ∀ b:Bool,
   fy p q b p = false ∧ fy p q b q = b ∧
   target (fy p q b) = false ∧ target (Function.update (fy p q b) p true) = true:= by
 fin_cases p <;> decide +kernel
lemma kt (p q:Fin 10) (different:p ≠ q) (b:Bool):
   ∃ x:Fin 10 → Bool,x p = false ∧ x q = b ∧
     target x = false ∧ target (Function.update x p true) = true:=
 ⟨fy p q b,nO p q different b⟩
lemma dependence_at_value (p q:Fin 10) (different:p ≠ q) (b:Bool):
   ∃ x y:Fin 10 → Bool,x p = false ∧ y p = true ∧ x q = b ∧ y q = b ∧
     (∀ i,i ≠ p → x i = y i) ∧ target x = false ∧ target y = true:= by
 obtain ⟨x,hp,hq,hOff,hOn⟩:= kt p q different b
 refine ⟨x,Function.update x p true,hp,Function.update_self _ _ _,hq,?_,?_,hOff,hOn⟩
 · exact (Function.update_of_ne different.symm true x).trans hq
 · intro i hi
   exact (Function.update_of_ne hi true x).symm
private def i4:Fin 10 → Bool:= fun _ => false
private def et (i:Fin 10):Fin 10 → Bool:= fun j => decide (j = i)
private def qt:Fin 10 → Bool:= fun i => decide (i = 0 ∨ i = 1)
private lemma oL:target i4 = false:= by decide +kernel
private lemma l0: ∀ i:Fin 10,target (et i) = false:= by
 decide +kernel
lemma target_not_constant (b:Bool): ∃ x:Fin 10 → Bool,target x ≠ b:= by
 cases b
 · exact ⟨qt,by decide +kernel⟩
 · exact ⟨i4,by decide +kernel⟩
lemma target_not_signed_primary (i:Fin 10) (negated:Bool):
   ∃ x:Fin 10 → Bool,target x ≠ (if negated then !(x i) else x i):= by
 cases negated
 · refine ⟨et i,?_⟩
   change target (et i) ≠ et i i
   rw [l0 i]
   simp [et]
 · refine ⟨i4,?_⟩
   change target i4 ≠ true
   simp [oL]
lemma target_not_signed_hint (negated:Bool):
   ∃ x:Fin 10 → Bool,target x ≠ (if negated then !(x 0 && x 2) else x 0 && x 2):= by
 cases negated
 · exact ⟨qt,by decide +kernel⟩
 · exact ⟨i4,by decide +kernel⟩
end PEqualNP.Outside.L_meta_4817.ch
namespace PEqualNP.Outside.L_meta_4817.ey
open PEqualNP.CircuitLowerBounds
private def step (w:List Bool) (g:Gate):List Bool:=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private lemma lA (C:Circuit) (x:List Bool):C.wires x = C.gates.foldl step x:= rfl
private lemma md (gs:List Gate): ∀ w:List Bool,
   ∃ t:List Bool,gs.foldl step w = w ++ t ∧ t.length = gs.length:= by
 induction gs with
 | nil => intro w;exact ⟨[],by simp,rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩:= ih (step w g)
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
   rw [List.foldl_cons,ht];simp [step]
private lemma me (gs:List Gate) (w:List Bool):
   (gs.foldl step w).length = w.length + gs.length:= by
 obtain ⟨t,ht,hl⟩:= md gs w
 rw [ht];simp [hl]
private lemma iF (gs:List Gate) (w:List Bool) (i:ℕ) (h:i < w.length):
   (gs.foldl step w).getD i false = w.getD i false:= by
 obtain ⟨t,ht,_⟩:= md gs w
 rw [ht,List.getD_append _ _ _ _ h]
def rd (C:Circuit) (x:List Bool) (g i:ℕ):Bool:=
 if i < g then (C.wires x).getD i false else false
lemma wires_length (C:Circuit) (x:List Bool):
   (C.wires x).length = x.length + C.gates.length:= me _ _
lemma wires_input (C:Circuit) (x:List Bool) (i:ℕ) (h:i < x.length):
   (C.wires x).getD i false = x.getD i false:= iF _ _ _ h
lemma kp (C:Circuit) (x:List Bool) (j:ℕ) (hj:j < C.gates.length):
   (C.wires x).getD (x.length + j) false =
     C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i):= by
 have hsplit:C.gates = C.gates.take j ++ C.gates[j]::C.gates.drop (j + 1):= by
   simp
 set A:= (C.gates.take j).foldl step x with hA
 have hAl:A.length = x.length + j:= by
   rw [hA,me];simp;omega
 have hw:C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]):= by
   rw [lA]
   conv_lhs => rw [hsplit]
   rw [List.foldl_append,List.foldl_cons]
 have hreadA: ∀ i,A.getD i false = rd C x (x.length + j) i:= by
   intro i
   unfold rd
   by_cases hi:i < x.length + j
   · rw [if_pos hi,hw,iF _ (step A C.gates[j]) i (by simp [step];omega),step,
       List.getD_append _ _ _ _ (by omega)]
   · rw [if_neg hi,List.getD_eq_default];omega
 rw [hw,iF _ _ _ (by simp [step];omega),step,
   List.getD_append_right _ _ _ _ (by omega)]
 simp only [hAl,Nat.sub_self,List.getD_cons_zero]
 congr 1
 exact List.map_congr_left (fun i _ => hreadA i)
lemma wires_gate_of_input_reads (C:Circuit) (x:List Bool) (j:ℕ)
   (hj:j < C.gates.length) (reads: ∀ t ∈ C.gates[j].inputs,t < x.length):
   (C.wires x).getD (x.length + j) false =
     C.gates[j].op.eval (C.gates[j].inputs.map fun t => x.getD t false):= by
 rw [kp C x j hj]
 congr 1
 apply List.map_congr_left
 intro t ht
 have ht':= reads t ht
 rw [rd,if_pos (by omega),wires_input C x t ht']
private lemma lQ (C:Circuit) (a b:List Bool) (hl:a.length = b.length)
   (R:Bool → Bool → Prop) (keep:ℕ → Prop) (zero:R false false)
   (initial: ∀ i < a.length,keep i → R (a.getD i false) (b.getD i false))
   (compatible: ∀ g ∈ C.gates,∀ f f':ℕ → Bool,
     (∀ i ∈ g.inputs,R (f i) (f' i)) → R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map f')))
   (gate: ∀ j (hj:j < C.gates.length),keep (a.length + j) →
     R ((C.wires a).getD (a.length + j) false) ((C.wires b).getD (a.length + j) false) ∨
       ∀ t ∈ C.gates[j].inputs,t < a.length + j → keep t):
   ∀ i,keep i → R ((C.wires a).getD i false) ((C.wires b).getD i false):= by
 intro i
 induction i using Nat.strong_induction_on with
 | _ i ih =>
     intro hi
     by_cases ai:i < a.length
     · rw [wires_input C a i ai,wires_input C b i (by omega)]
       exact initial i ai hi
     by_cases gi:i < a.length + C.gates.length
     · let j:= i - a.length
       have hj:j < C.gates.length:= by dsimp [j];omega
       have index:a.length + j = i:= by dsimp [j];omega
       rw [← index]
       rcases gate j hj (by rwa [index]) with equal | inputs
       · exact equal
       have wb:(C.wires b).getD (a.length + j) false =
           C.gates[j].op.eval (C.gates[j].inputs.map fun t => rd C b (a.length + j) t):= by
         rw [hl,kp C b j hj]
       rw [kp C a j hj,wb]
       apply compatible C.gates[j] (List.getElem_mem hj)
       intro t ht
       unfold rd
       by_cases before:t < a.length + j
       · rw [if_pos before,if_pos before]
         exact ih t (by omega) (inputs t ht before)
       · rw [if_neg before,if_neg before]
         exact zero
     · rw [List.getD_eq_default _ _ (by rw [wires_length];omega),
         List.getD_eq_default _ _ (by rw [wires_length];omega)]
       exact zero
private lemma nq (g:Gate) (f f':ℕ → Bool)
   (h: ∀ i ∈ g.inputs,f i = f' i):g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f'):= by
 congr 1
 exact List.map_congr_left h
lemma eval_eq_of_read_agreement (C:Circuit) (a b:List Bool) (hl:a.length = b.length)
   (output:a.length ≤ C.output)
   (gate: ∀ j (hj:j < C.gates.length),
     (C.wires a).getD (a.length + j) false = (C.wires b).getD (a.length + j) false ∨
       ∀ t ∈ C.gates[j].inputs,t < a.length → a.getD t false = b.getD t false):
   C.eval a = C.eval b:= by
 let keep:= fun i => a.length ≤ i ∨ a.getD i false = b.getD i false
 apply lQ C a b hl Eq keep rfl _ (fun g _ => nq g) _ C.output (Or.inl output)
 · intro i hi hk
   exact hk.resolve_left (by omega)
 · intro j hj _
   rcases gate j hj with same | h
   · exact Or.inl same
   · right
     intro t ht _
     by_cases small:t < a.length
     · exact Or.inr (h t ht small)
     · exact Or.inl (by omega)
lemma exists_consumer_of_eval_ne (C:Circuit) (a b:List Bool) (hl:a.length = b.length)
   (output:a.length ≤ C.output) (j:ℕ) (outOther:C.output ≠ a.length + j)
   (different:C.eval a ≠ C.eval b)
   (others: ∀ q (hq:q < C.gates.length),q ≠ j → ∀ t ∈ C.gates[q].inputs,
     t < a.length → a.getD t false = b.getD t false):
   ∃ q,∃ hq:q < C.gates.length,j < q ∧ a.length + j ∈ C.gates[q].inputs:= by
 by_contra absent
 apply different
 let keep:= fun i => i ≠ a.length + j ∧ (a.length ≤ i ∨ a.getD i false = b.getD i false)
 apply lQ C a b hl Eq keep rfl _ (fun g _ => nq g) _ C.output
   ⟨outOther,Or.inl output⟩
 · intro i hi hk
   exact hk.2.resolve_left (by omega)
 · intro q hq hkeep
   have qOther:q ≠ j:= by
     intro eq
     exact hkeep.1 (by rw [eq])
   right
   intro t ht before
   refine ⟨?_,?_⟩
   · intro eq
     exact absent ⟨q,hq,by omega,eq ▸ ht⟩
   · by_cases small:t < a.length
     · exact Or.inr (others q hq qOther t ht small)
     · exact Or.inl (by omega)
private lemma oK (g:Gate) (hop:g.op = GateOp.and ∨ g.op = GateOp.or)
   (f f':ℕ → Bool) (h: ∀ i ∈ g.inputs,f i = true → f' i = true):
   g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true:= by
 rcases hop with he | he
 · simp only [he,GateOp.eval,List.all_eq_true,List.mem_map,id]
   intro H x hx
   obtain ⟨i,hi,rfl⟩:= hx
   exact h i hi (H (f i) ⟨i,hi,rfl⟩)
 · simp only [he,GateOp.eval,List.any_eq_true,List.mem_map,id]
   rintro ⟨x,⟨i,hi,rfl⟩,hx⟩
   exact ⟨f' i,⟨i,hi,rfl⟩,h i hi hx⟩
lemma eval_true_of_read_monotonicity (C:Circuit) (a b:List Bool) (hl:a.length = b.length)
   (output:a.length ≤ C.output)
   (ops: ∀ g ∈ C.gates,g.op = GateOp.and ∨ g.op = GateOp.or)
   (ordered: ∀ j (hj:j < C.gates.length),∀ t ∈ C.gates[j].inputs,
     t < a.length → a.getD t false = true → b.getD t false = true):
   C.eval a = true → C.eval b = true:= by
 let keep:= fun i => a.length ≤ i ∨ (a.getD i false = true → b.getD i false = true)
 apply lQ C a b hl (fun x y => x = true → y = true) keep (fun h => h) _
   (fun g hg => oK g (ops g hg)) _ C.output (Or.inl output)
 · intro i hi hk
   exact hk.resolve_left (by omega)
 · intro j hj _
   right
   intro t ht _
   by_cases small:t < a.length
   · exact Or.inr (ordered j hj t ht small)
   · exact Or.inl (by omega)
end PEqualNP.Outside.L_meta_4817.ey
namespace PEqualNP.Outside.L_meta_4817.cf
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.aJ (target)
open PEqualNP.Outside.L_meta_4817.eg
 (Wire aS inv bH ad co Reach gb da cC
   Row Sig bit aF graph inputs cn edge mL Lower eL iA
   px gt fu eY hB)
private def bl:Fin 10 → Fin 10:= ![1,2,3,4,0,6,7,8,9,5]
private def bI:Fin 10 → Fin 10:= ![5,7,9,6,8,0,2,4,1,3]
set_option maxHeartbeats 1500000 in
private lemma hC (x:Fin 10 → Bool):
   target (fun i => x (bl i)) = target x:= by
 change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
     (x 0 && x 1) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
     (x 4 && x 9) || (x 0 && x 5) || (x 6 && x 8) || (x 8 && x 5) ||
     (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6)) = target x
 simp only [target,Bool.and_comm,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private lemma gw (x:Fin 10 → Bool):
   target (fun i => x (bI i)) = target x:= by
 change ((x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) ||
     (x 8 && x 5) || (x 5 && x 0) || (x 7 && x 2) || (x 9 && x 4) ||
     (x 6 && x 1) || (x 8 && x 3) || (x 0 && x 4) || (x 4 && x 3) ||
     (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0)) = target x
 simp only [target,Bool.and_comm,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private def bn (v:Fin 10):ℕ:=
 (5 - (if v.val < 5 then v.val else (bI v).val)) % 5
def cG (v i:Fin 10):Fin 10:=
 (bl^[bn v]) (if v.val < 5 then i else bI i)
lemma hR: ∀ v:Fin 10,cG v v = 0:= by
 decide +kernel
private lemma cc (n:ℕ) (x:Fin 10 → Bool):
   target (fun i => x ((bl^[n]) i)) = target x:= by
 induction n with
 | zero => rfl
 | succ n ih =>
   simp only [Function.iterate_succ_apply]
   exact (hC (fun i => x ((bl^[n]) i))).trans ih
lemma h5 (v:Fin 10) (x:Fin 10 → Bool):
   target (fun i => x (cG v i)) = target x:= by
 by_cases h:v.val < 5
 · simpa only [cG,if_pos h] using cc (bn v) x
 · simpa only [cG,if_neg h] using
     (gw (fun i => x ((bl^[bn v]) i))).trans
       (cc (bn v) x)
def cz (r:Row):Fin 10 → Bool:=
 ![false,cn r 4,cn r 0,cn r 1,cn r 6,
   cn r 7,cn r 3,cn r 5,cn r 2,cn r 8]
def original:List (Wire Row):= inputs.map aF
private lemma zzzy (i:Fin 10):
   ad false original (fun r => cz r i):= by
 have col (j:Fin 9):ad false original (fun r => cn r j):= by
   have inList:j.val < inputs.length:= by
     have same:inputs.length = 9:= rfl
     rw [same]
     exact j.isLt
   left
   unfold original
   refine List.mem_map.mpr ⟨inputs[j.val],List.getElem_mem inList,?_⟩
   funext r
   exact (congrArg (bit r) (List.getD_eq_getElem _ _ inList)).symm
 fin_cases i
 · exact Or.inr (Or.inl ⟨false,rfl⟩)
 · exact col 4
 · exact col 0
 · exact col 1
 · exact col 6
 · exact col 7
 · exact col 3
 · exact col 5
 · exact col 2
 · exact col 8
def restrictedAll (v:Fin 10) (r:Row) (i:Fin 10):Bool:=
 cz r (cG v i)
lemma restrictedAll_self (v:Fin 10) (r:Row):restrictedAll v r v = false:= by
 change cz r (cG v v) = false
 rw [hR] <;> rfl
private lemma ff (r:Row):target (cz r) = aF graph r:= by
 have table:aF graph r = edge (cn r):= mL r
 rw [table]
 let x:= cn r
 change ((false && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && false) ||
     (false && x 7) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) ||
     (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7)) = edge x
 simp only [edge,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,
   Bool.and_comm,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
lemma allCofactorCorrect (v:Fin 10) (r:Row):
   target (restrictedAll v r) = aF graph r:=
 (h5 v (cz r)).trans (ff r)
private lemma rx:Lower false inputs graph 16:= by
 apply eL iA (by decide +kernel) (by decide +kernel) ?_ px
 intro a member
 rw [←gt] at member
 obtain ⟨i,rfl⟩:= List.mem_ofFn.mp member
 refine ⟨fu i,eY i,hB.1 i,?_⟩
 intro b hb distinct
 rw [←gt] at hb
 obtain ⟨j,rfl⟩:= List.mem_ofFn.mp hb
 exact hB.2 i j (fun eq => distinct (by rw [eq]))
def aP {R:Type}:Wire R:= fun _ => false
def ae (k:Fin 12) (useHint:Bool) (x:Fin 10 → Bool):List Bool:=
 (List.ofFn x ++ [if useHint then x 0 && x 2 else false]) ++
   [!(aJ.base x).getD k.val false]
def aK (k:Fin 12) (useHint:Bool) (v:Fin 10):List (Wire Row):=
 (List.ofFn (fun (i:Fin 10) r => restrictedAll v r i) ++
   [fun r => if useHint then restrictedAll v r 0 && restrictedAll v r 2 else false]) ++
   [fun r => !(aJ.base (restrictedAll v r)).getD k.val false]
@[simp] lemma seedColumns_length (k:Fin 12) (useHint:Bool) (v:Fin 10):
   (aK k useHint v).length = 12:= by simp [aK]
lemma gy (k:Fin 12) (useHint:Bool) (v:Fin 10) (r:Row):
   (aK k useHint v).map (fun f => f r) = ae k useHint (restrictedAll v r):= by
 simp only [aK,ae,List.map_append,List.map_singleton,List.map_ofFn,Function.comp_def] <;> rfl
def bc {R:Type} (ws:List (Wire R)) (g:Gate):Wire R:=
 fun r => g.op.eval (g.inputs.map fun i => (ws.getD i aP) r)
private def bk {R:Type} (seed:List (Wire R)):
   List Gate → List (Wire R) → List (Wire R)
 | [],past => past
 | g::gs,past => bk seed gs (past ++ [bc (seed ++ past) g])
def aB {R:Type} (seed:List (Wire R)) (gs:List Gate):List (Wire R):=
 seed ++ bk seed gs []
def Free {R:Type} (ws:List (Wire R)) (g:Gate):Prop:=
 g.inputs.length ≤ 1 ∨ (∃ i,g.inputs = [i,i]) ∨
   ∃ i ∈ g.inputs,aS (ws.getD i aP)
private lemma sm {R:Type} (ws:List (Wire R)) (g:Gate) (r:R):
   bc ws g r = g.op.eval (g.inputs.map fun i => (ws.map (fun f => f r)).getD i false):= by
 unfold bc
 congr 1
 apply List.map_congr_left
 intro i _
 exact (List.getD_map (l:= ws) (n:= i) (d:= aP) (fun f:Wire R => f r)).symm
private lemma mr {R:Type} (seed past:List (Wire R)) (gs:List Gate) (r:R):
   (seed ++ bk seed gs past).map (fun f => f r) =
     (⟨gs,0⟩:Circuit).wires ((seed ++ past).map (fun f => f r)):= by
 induction gs generalizing past with
 | nil => rfl
 | cons g gs ih =>
   change (seed ++ bk seed gs (past ++ [bc (seed ++ past) g])).map
       (fun f => f r) =
     (⟨gs,0⟩:Circuit).wires (((seed ++ past).map (fun f => f r)) ++
       [g.op.eval (g.inputs.map fun i => ((seed ++ past).map (fun f => f r)).getD i false)])
   rw [ih]
   simp only [List.append_assoc,List.map_append,List.map_singleton,sm]
lemma om {R:Type} (seed:List (Wire R)) (gs:List Gate) (r:R):
   (aB seed gs).map (fun f => f r) = (⟨gs,0⟩:Circuit).wires (seed.map (fun f => f r)):= by
 simpa only [aB,List.append_nil] using mr seed [] gs r
private lemma jw {R:Type} {seed past bank:List (Wire R)}
   (havePast:co false bank past) (i:ℕ)
   (primary:i < seed.length → ad false bank (seed.getD i aP)):
   ad false bank ((seed ++ past).getD i aP):= by
 by_cases h:i < seed.length
 · rw [List.getD_append _ _ _ _ h]
   exact primary h
 · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h),List.getD_eq_getElem?_getD]
   cases found:past[i - seed.length]? with
   | none => exact Or.inr (Or.inl ⟨false,rfl⟩)
   | some w => exact havePast w (List.mem_of_getElem? found)
private lemma fx {R:Type} {bank past:List (Wire R)} {w:Wire R}
   (old:co false bank past) (new:ad false bank w):
   co false bank (past ++ [w]):= by
 intro f h
 rcases List.mem_append.mp h with hp | hw
 · exact old f hp
 · rw [List.mem_singleton.mp hw]
   exact new
private lemma oR {R:Type} {roots bank:List (Wire R)} {used:ℕ}
   (ws:List (Wire R)) (g:Gate) (save:Bool) (reach:Reach false roots used bank)
   (hop:g.op = .and ∨ g.op = .or) (arity:g.inputs.length ≤ 2)
   (ready: ∀ i ∈ g.inputs,ad false bank (ws.getD i aP))
   (free:save = true → Free ws g):
   ∃ spent next,Reach false roots spent next ∧ ad false next (bc ws g) ∧
     (∀ w,ad false bank w → ad false next w) ∧
     spent + (if save then 1 else 0) ≤ used + 1:= by
 have retain (h:ad false bank (bc ws g)):
     ∃ spent next,Reach false roots spent next ∧ ad false next (bc ws g) ∧
       (∀ w,ad false bank w → ad false next w) ∧
       spent + (if save then 1 else 0) ≤ used + 1:=
   ⟨used,bank,reach,h,fun _ h => h,by cases save <;> simp⟩
 cases pins:g.inputs with
 | nil =>
   apply retain
   exact Or.inr (Or.inl ⟨g.op.eval [],by funext r;simp [bc,pins]⟩)
 | cons a tail =>
   cases tail with
   | nil =>
     apply retain
     have same:bc ws g = ws.getD a aP:= by
       funext r
       rcases hop with h | h <;> simp [bc,pins,h,GateOp.eval]
     rw [same]
     exact ready a (by simp [pins])
   | cons b tail =>
     cases tail with
     | nil =>
       let aCol:= ws.getD a aP
       let bCol:= ws.getD b aP
       let op:= !(g.op.eval [])
       have same:bc ws g = bH op aCol bCol:= by
         funext r
         rcases hop with h | h <;> simp [bc,pins,op,bH,h,GateOp.eval,aCol,bCol]
       have ha:= ready a (by simp [pins])
       have hb:= ready b (by simp [pins])
       by_cases hs:save = true
       · apply retain
         rcases free hs with short | repeated | ⟨i,hm,const⟩
         · simp [pins] at short
         · obtain ⟨i,eq⟩:= repeated
           have samePins:a = i ∧ b = i:= by simpa [pins] using eq
           have ab:a = b:= samePins.1.trans samePins.2.symm
           have sameCol:bc ws g = aCol:= by
             rw [same]
             funext r
             simp [aCol,bCol,ab,bH]
           rw [sameCol]
           exact ha
         · rw [same]
           simp only [pins,List.mem_cons,List.mem_nil_iff,or_false] at hm
           rcases hm with rfl | rfl
           · exact da op (Or.inl const) ha hb
           · exact da op (Or.inr const) ha hb
       · refine ⟨used+1,bc ws g::bank,?_,Or.inl List.mem_cons_self,
           fun _ h => cC _ h,by simp [hs]⟩
         rw [same]
         exact Reach.two op reach ha hb
     | cons c after =>
       simp [pins] at arity <;> omega
private lemma te {R:Type} (seed:List (Wire R)) (save:ℕ → Bool) (start:ℕ)
   (gs:List Gate) {roots bank past:List (Wire R)} {used:ℕ}
   (reach:Reach false roots used bank) (havePast:co false bank past)
   (model: ∀ g ∈ gs,(g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
   (ready: ∀ g ∈ gs,∀ i ∈ g.inputs,i < seed.length →
     ad false bank (seed.getD i aP))
   (fixed: ∀ before g after,gs = before ++ g::after → save (start + before.length) = true →
     Free (seed ++ bk seed before past) g):
   ∃ spent next,Reach false roots spent next ∧
     co false next (bk seed gs past) ∧
     spent + (gs.zipIdx start).countP (fun row => save row.2) ≤ used + gs.length:= by
 induction gs generalizing start used bank past with
 | nil => exact ⟨used,bank,reach,havePast,by simp⟩
 | cons g gs ih =>
   have hg:= model g List.mem_cons_self
   have h (marked:save start = true):Free (seed ++ past) g:=
     fixed [] g gs rfl (by simpa using marked)
   obtain ⟨mid,bank',reach',value,keep,cost⟩:=
     oR (seed ++ past) g (save start) reach hg.1 hg.2
       (fun i hi => jw havePast i (ready g List.mem_cons_self i hi)) h
   have havePast':co false bank' (past ++ [bc (seed ++ past) g]):=
     fx (fun w hw => keep w (havePast w hw)) value
   obtain ⟨spent,next,reachable,supplied,budget⟩:=
     ih (start:= start+1) reach' havePast'
       (fun w hw => model w (List.mem_cons_of_mem _ hw))
       (fun w hw i hi before => keep _ (ready w (List.mem_cons_of_mem _ hw) i hi before))
       (fun before w after eq marked => by
         have same:g::gs = (g::before) ++ w::after:= congrArg (List.cons g) eq
         have startEq:start + (g::before).length = start + 1 + before.length:= by simp;omega
         exact fixed (g::before) w after same (by rwa [startEq]))
   refine ⟨spent,next,reachable,supplied,?_⟩
   simp only [List.zipIdx_cons,List.countP_cons,List.length_cons]
   cases hs:save start <;> simp [hs] at cost ⊢ <;> omega
private lemma eb {α:Type} (p:α → Bool):
   ∀ l:List α,l.countP p =
     (Finset.univ.filter fun i:Fin l.length => p (l.get i) = true).card
 | [] => by simp
 | a::l => by
   have ih:= eb p l
   have split:(Finset.univ.filter fun i:Fin (a::l).length => p ((a::l).get i) = true).card =
       (if p a = true then 1 else 0) +
         (Finset.univ.filter fun i:Fin l.length => p (l.get i) = true).card:= by
     rw [show (Finset.univ.filter fun i:Fin (a::l).length => p ((a::l).get i) = true).card =
         (Finset.univ.filter fun i:Fin (l.length + 1) => p ((a::l).get i) = true).card from rfl,
       Fin.card_filter_univ_succ (n:= l.length) (fun i:Fin (l.length + 1) => p ((a::l).get i) = true)]
     by_cases h:p a = true
     · simp [h,Function.comp_def,add_comm]
     · simp [h,Function.comp_def]
   rw [split,← ih,List.countP_cons,add_comm]
def cl (C:Circuit) (i:ℕ):Prop:= ∃ g ∈ C.gates,i ∈ g.inputs
def Ready (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10):Prop:=
 ∀ i < 12,cl C i →
   ad false original ((aK k useHint v).getD i aP)
lemma iG (k:Fin 12) (useHint:Bool) (v i:Fin 10):
   (aK k useHint v).getD i.val aP = fun r => restrictedAll v r i:= by
 have bound:= i.isLt
 unfold aK
 rw [List.getD_append _ _ _ _ (by simp;omega),
   List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using bound),
   List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using bound),List.getElem_ofFn] <;> rfl
lemma iy (k:Fin 12) (useHint:Bool) (v i:Fin 10):
   ad false original ((aK k useHint v).getD i.val aP):= by
 rw [iG]
 exact zzzy (cG v i)
lemma sd (k:Fin 12) (useHint:Bool) (v:Fin 10):
   (aK k useHint v).getD 10 aP =
     fun r => if useHint then restrictedAll v r 0 && restrictedAll v r 2 else false:= by
 unfold aK
 rw [List.getD_append _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)] <;> simp
lemma sx (k:Fin 12) (useHint:Bool) (v:Fin 10):
   (aK k useHint v).getD 11 aP =
     fun r => !(aJ.base (restrictedAll v r)).getD k.val false:= by
 unfold aK
 rw [List.getD_append_right _ _ _ _ (by simp)] <;> simp
lemma eK (k:Fin 12) (useHint:Bool) (v:Fin 10):
   aS ((aK k useHint v).getD v.val aP):= by
 rw [iG]
 exact ⟨false,funext (restrictedAll_self v)⟩
lemma jq (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (fixed:useHint = false ∨ v = 0 ∨ v = 2):
   aS ((aK k useHint v).getD 10 aP):= by
 rw [sd]
 refine ⟨false,?_⟩
 funext r
 rcases fixed with off | rfl | rfl
 · simp [off]
 · simp [restrictedAll_self]
 · simp [restrictedAll_self]
private lemma fw (x:Fin 10 → Bool) (v:Fin 10):
   (aJ.base x).getD v.val false = x v:= by
 have bound:= v.isLt
 unfold aJ.base
 rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using bound),
   List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using bound),List.getElem_ofFn] <;> rfl
private lemma i6 (x:Fin 10 → Bool):
   (aJ.base x).getD 10 false = (x 0 && x 2):= by
 unfold aJ.base
 rw [List.getD_append_right _ _ _ _ (by simp)] <;> simp
lemma lD (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (fixed:k.val = v.val ∨ k.val = 11 ∨ (k.val = 10 ∧ (v = 0 ∨ v = 2))):
   aS ((aK k useHint v).getD 11 aP):= by
 rw [sx]
 refine ⟨true,?_⟩
 funext r
 rcases fixed with atV | outside | ⟨atHint,endpoint⟩
 · rw [atV,fw,restrictedAll_self] <;> rfl
 · rw [outside,List.getD_eq_default _ _ (by simp [aJ.base])] <;> rfl
 · rw [atHint,i6]
   rcases endpoint with rfl | rfl <;> simp [restrictedAll_self]
lemma m6 (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (goodHint:(useHint = false ∨ v = 0 ∨ v = 2) ∨ ¬cl C 10)
   (goodNeg:(k.val = v.val ∨ k.val = 11 ∨ (k.val = 10 ∧ (v = 0 ∨ v = 2))) ∨
     ¬cl C 11):
   Ready C k useHint v:= by
 intro i bound usedHere
 by_cases small:i < 10
 · let j:Fin 10:= ⟨i,small⟩
   change ad false original ((aK k useHint v).getD j.val aP)
   rw [iG]
   exact zzzy (cG v j)
 · by_cases equal:i = 10
   · subst i
     exact goodHint.elim (fun h => Or.inr (Or.inl (jq k useHint v h)))
       (fun h => (h usedHere).elim)
   · have is11:i = 11:= by omega
     subst i
     exact goodNeg.elim (fun h => Or.inr (Or.inl (lD k useHint v h)))
       (fun h => (h usedHere).elim)
private lemma fq {R:Type} (seed past:List (Wire R)) (a b:List Gate):
   bk seed (a ++ b) past = bk seed b (bk seed a past):= by
 induction a generalizing past with
 | nil => rfl
 | cons g gs ih => exact ih _
private lemma dj {R:Type} (seed past:List (Wire R)) (gs:List Gate):
   ∃ tail,bk seed gs past = past ++ tail ∧ tail.length = gs.length:= by
 induction gs generalizing past with
 | nil => exact ⟨[],by simp [bk],rfl⟩
 | cons g gs ih =>
   obtain ⟨tail,h,hlen⟩:= ih (past ++ [bc (seed ++ past) g])
   exact ⟨bc (seed ++ past) g::tail,by simpa [bk,List.append_assoc] using h,
     by simp [hlen]⟩
lemma jx {R:Type} (seed:List (Wire R)) (gs:List Gate):
   (aB seed gs).length = seed.length + gs.length:= by
 obtain ⟨tail,eq,size⟩:= dj seed [] gs
 simp [aB,eq,size]
lemma ry {R:Type} (seed:List (Wire R)) (gs:List Gate) (i:Fin gs.length):
   (aB seed gs).getD (seed.length+i.val) aP =
     bc (aB seed (gs.take i.val)) (gs.get i):= by
 let before:= gs.take i.val
 let after:= gs.drop (i.val+1)
 let g:= gs.get i
 let prior:= bk seed before []
 let value:= bc (seed ++ prior) g
 have split:gs = before ++ g::after:= by simp [before,g,after]
 have forTail:= dj seed (prior ++ [value]) after
 obtain ⟨tail,eq,_⟩:= forTail
 have full:aB seed gs = ((seed ++ prior) ++ [value]) ++ tail:= by
   unfold aB
   conv_lhs => rw [split,fq]
   change seed ++ bk seed after (prior ++ [value]) = _
   simp [eq,List.append_assoc]
 have width:(seed ++ prior).length = seed.length+i.val:= by
   change (aB seed (gs.take i.val)).length = _
   simp [jx,Nat.min_eq_left i.isLt.le]
 have longer:((seed ++ prior) ++ [value]).length = seed.length+i.val+1:= by
   rw [List.length_append,width,List.length_singleton]
 rw [full,List.getD_append _ _ _ _ (by omega),← width]
 change ((seed ++ prior) ++ [value]).getD (seed ++ prior).length aP = value
 simp
private lemma pS (gs:List Gate) (save:ℕ → Bool) (i j:Fin gs.length)
   (distinct:i ≠ j) (hi:save i.val = true) (hj:save j.val = true):
   2 ≤ (gs.zipIdx 0).countP (fun row => save row.2):= by
 rw [eb]
 let a:Fin (gs.zipIdx 0).length:= ⟨i.val,by simpa using i.isLt⟩
 let b:Fin (gs.zipIdx 0).length:= ⟨j.val,by simpa using j.isLt⟩
 have ha:save ((gs.zipIdx 0).get a).2 = true:= by
   change save ((gs.zipIdx 0)[i.val]).2 = true
   simpa only [List.getElem_zipIdx,Nat.zero_add] using hi
 have hb:save ((gs.zipIdx 0).get b).2 = true:= by
   change save ((gs.zipIdx 0)[j.val]).2 = true
   simpa only [List.getElem_zipIdx,Nat.zero_add] using hj
 exact Finset.one_lt_card.mpr
   ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,
     b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,
     fun h => distinct (Fin.ext (congrArg (fun z:Fin (gs.zipIdx 0).length => z.val) h))⟩
lemma dl (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (mono:Monotone2 C) (outGate:12 ≤ C.output) (ready:Ready C k useHint v)
   (fits: ∀ x,C.eval (ae k useHint x) = target x)
   (i j:Fin C.gates.length) (distinct:i ≠ j)
   (freeI:Free (aB (aK k useHint v) (C.gates.take i.val)) (C.gates.get i))
   (freeJ:Free (aB (aK k useHint v) (C.gates.take j.val)) (C.gates.get j)):
   18 ≤ C.size:= by
 let seed:= aK k useHint v
 let save:ℕ → Bool:= fun index => decide (index = i.val ∨ index = j.val)
 have model (g:Gate) (member:g ∈ C.gates):
     (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2:= by
   simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g member
 obtain ⟨spent,bank,reach,supplyPast,count⟩:= te seed save 0 C.gates
   (roots:= original) (past:= []) Reach.start (by simp [co]) model
   (fun g member pin hp bound => ready pin (by simpa [seed] using bound) ⟨g,member,hp⟩)
   (by
     intro before g after split marked
     have flags:before.length = i.val ∨ before.length = j.val:= by simpa [save] using marked
     have reindex (idx:Fin C.gates.length) (atIdx:before.length = idx.val)
         (isFree:Free (aB seed (C.gates.take idx.val)) (C.gates.get idx)):
         Free (seed ++ bk seed before []) g:= by
       have takeEq:C.gates.take idx.val = before:=
         (congrArg (fun l:List Gate => l.take idx.val) split).trans (List.take_left' atIdx)
       have gateEq:C.gates.get idx = g:= by
         apply Option.some.inj
         calc
           some (C.gates.get idx) = C.gates[idx.val]?:= (List.getElem?_eq_getElem idx.isLt).symm
           _ = (before ++ g::after)[idx.val]?:=
             congrArg (fun l:List Gate => l[idx.val]?) split
           _ = some g:= by
             rw [List.getElem?_append_right (by omega),atIdx,Nat.sub_self] <;> rfl
       simpa only [takeEq,gateEq,aB] using isFree
     exact flags.elim (fun h => reindex i h freeI) (fun h => reindex j h freeJ))
 have outReady:ad false bank ((aB seed C.gates).getD C.output aP):=
   jw supplyPast C.output (by
     intro tooEarly
     have len:seed.length = 12:= seedColumns_length k useHint v
     omega)
 have evaluates:(aB seed C.gates).getD C.output aP = aF graph:= by
   funext r
   have same:= List.getD_map (l:= aB seed C.gates)
     (n:= C.output) (d:= aP) (fun f:Wire Row => f r)
   rw [om] at same
   change C.eval (seed.map (fun f => f r)) =
     ((aB seed C.gates).getD C.output aP) r at same
   rw [show seed.map (fun f => f r) = ae k useHint (restrictedAll v r) from
     gy k useHint v r] at same
   exact same.symm.trans ((fits _).trans (allCofactorCorrect v r))
 rw [evaluates] at outReady
 have lower:= rx spent bank reach outReady
 have twice:= pS C.gates save i j distinct (by simp [save]) (by simp [save])
 change 18 ≤ C.gates.length
 omega
end PEqualNP.Outside.L_meta_4817.cf
namespace PEqualNP.Outside.L_meta_4817.ce
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.aJ (target base)
open PEqualNP.Outside.L_meta_4817.cf
abbrev bf (C:Circuit):= Fin C.gates.length
def Reads (C:Circuit) (i:bf C) (input:ℕ):Prop:=
 input ∈ (C.gates.get i).inputs
def cg (C:Circuit) (i:bf C) (pins:Finset ℕ):Prop:=
 ∃ a ∈ pins,Reads C i a
lemma kk (C:Circuit) (pins:Finset ℕ) (i:bf C)
   (hi:cg C i pins):
   (∃ j:bf C,j ≠ i ∧ cg C j pins) ∨
     ∀ j:bf C,cg C j pins → j = i:= by
 classical
 by_cases another: ∃ j:bf C,j ≠ i ∧ cg C j pins
 · exact .inl another
 · refine .inr fun j hj => ?_
   by_contra distinct
   exact another ⟨j,distinct,hj⟩
lemma fi {g:Gate} {p q:ℕ} (arity:g.inputs.length ≤ 2)
   (hp:p ∈ g.inputs) (hq:q ∈ g.inputs) (different:p ≠ q):
   g.inputs = [p,q] ∨ g.inputs = [q,p]:= by
 have enough:1 < g.inputs.toFinset.card:=
   Finset.one_lt_card.mpr ⟨p,List.mem_toFinset.mpr hp,q,List.mem_toFinset.mpr hq,different⟩
 have len:= List.toFinset_card_le (l:= g.inputs)
 have exactly:g.inputs.length = 2:= by omega
 obtain ⟨a,b,h⟩:= List.length_eq_two.mp exactly
 rw [h] at hp hq ⊢
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hp hq
 rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
 · exact (different rfl).elim
 · exact .inl rfl
 · exact .inr rfl
 · exact (different rfl).elim
lemma hI (C:Circuit) (mono:Monotone2 C) (i:bf C):
   ((C.gates.get i).op = .and ∨ (C.gates.get i).op = .or) ∧
     (C.gates.get i).inputs.length ≤ 2:= by
 simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono _ (List.get_mem C.gates i)
lemma bL (k:Fin 12) (useHint:Bool) (x:Fin 10 → Bool) (v:Fin 10):
   (ae k useHint x).getD v.val false = x v:= by
 unfold ae
 rw [List.getD_append _ _ _ _ (by simp;have:= v.isLt;omega)]
 rw [List.getD_append _ _ _ _ (by simpa using v.isLt)]
 rw [List.getD_eq_getElem _ _ (by simpa using v.isLt),List.getElem_ofFn] <;> rfl
lemma dm (k:Fin 12) (useHint:Bool) (x:Fin 10 → Bool):
   (ae k useHint x).getD 10 false = (if useHint then x 0 && x 2 else false):= by
 simp [ae,List.getD_append_right,List.getD_append]
lemma iE (k:Fin 12) (useHint:Bool) (x:Fin 10 → Bool):
   (ae k useHint x).getD 11 false = !((base x).getD k.val false):= by
 simp [ae,List.getD_append_right,List.getD_append]
lemma dk (k:Fin 12) (useHint:Bool) (x:Fin 10 → Bool)
   (v:Fin 10) (atV:k.val = v.val):
   (ae k useHint x).getD 11 false = !(x v):= by
 rw [iE,atV]
 unfold base
 rw [List.getD_append _ _ _ _ (by simpa using v.isLt)]
 rw [List.getD_eq_getElem _ _ (by simpa using v.isLt),List.getElem_ofFn] <;> rfl
lemma iU (useHint:Bool) (x:Fin 10 → Bool):
   (ae 10 useHint x).getD 11 false = !(x 0 && x 2):= by
 rw [iE]
 simp [base,List.getD_append_right]
lemma eB (useHint:Bool) (x:Fin 10 → Bool):
   (ae 11 useHint x).getD 11 false = true:= by
 rw [iE]
 have beyond:(base x).length ≤ (11:Fin 12).val:= by simp [base]
 rw [List.getD_eq_default _ _ beyond]
 rfl
lemma kj (k:Fin 12) (useHint:Bool) (x:Fin 10 → Bool)
   (a:ℕ) (ha:a < 12):
   (∃ v:Fin 10,a = v.val ∧ (ae k useHint x).getD a false = x v) ∨
     a = 10 ∨ a = 11:= by
 by_cases h:a < 10
 · exact .inl ⟨⟨a,h⟩,rfl,bL k useHint x ⟨a,h⟩⟩
 · right
   omega
lemma pD (g:Gate) (op:g.op = .and ∨ g.op = .or)
   (x:ℕ → Bool) {p q:ℕ} (form:g.inputs = [p,q] ∨ g.inputs = [q,p]):
   g.op.eval (g.inputs.map x) = (match g.op with
     | .or => x p || x q
     | _ => x p && x q):= by
 rcases op with isAnd | isOr
 · rcases form with same | reverse
   · simp [isAnd,same,GateOp.eval]
   · simp [isAnd,reverse,GateOp.eval,Bool.and_comm]
 · rcases form with same | reverse
   · simp [isOr,same,GateOp.eval]
   · simp [isOr,reverse,GateOp.eval,Bool.or_comm]
end PEqualNP.Outside.L_meta_4817.ce
namespace PEqualNP.Outside.L_meta_4817.ce
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.aJ (target)
open PEqualNP.Outside.L_meta_4817.cf
lemma cO (v:Fin 10):
   ∃ x y:Fin 10 → Bool,x v = false ∧ y v = true ∧
     (∀ i,i ≠ v → x i = y i) ∧ (x 0 && x 2) = (y 0 && y 2) ∧
     target x = false ∧ target y = true:= by
 let q:Fin 10:= if v = 0 then 2 else 0
 have ne:v ≠ q:= by
   by_cases h:v = 0
   · simp [q,h]
   · simpa [q,h] using h
 obtain ⟨x,y,xv,yv,xq,yq,agree,off,on⟩:= ch.dependence_at_value v q ne false
 refine ⟨x,y,xv,yv,agree,?_,off,on⟩
 by_cases h:v = 0
 · simp [q,h] at xq yq
   simp [xq,yq]
 · simp [q,h] at xq yq
   simp [xq,yq]
lemma dw (k:Fin 12) (h: ¬k.val < 10):k = 10 ∨ k = 11:= by
 have bound:= k.isLt
 by_cases h10:k.val = 10
 · exact Or.inl (Fin.ext h10)
 · exact Or.inr (Fin.ext (by change k.val = 11;omega))
lemma im (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (x y:Fin 10 → Bool) (xv:x v = false) (yv:y v = true)
   (agree: ∀ i,i ≠ v → x i = y i) (hint:(x 0 && x 2) = (y 0 && y 2))
   (a:ℕ) (ha:a < 12) (different:a ≠ v.val):
   (ae k useHint y).getD a false ≤ (ae k useHint x).getD a false:= by
 rcases kj k useHint y a ha with ⟨i,rfl,_⟩ | rfl | rfl
 · rw [bL,bL,agree i]
   intro eq
   exact different (congrArg Fin.val eq)
 · rw [dm,dm,hint]
 · by_cases hk:k.val < 10
   · let u:Fin 10:= ⟨k.val,hk⟩
     rw [dk k useHint y u rfl,dk k useHint x u rfl]
     by_cases hu:u = v
     · rw [hu,xv,yv]
       decide
     · rw [agree u hu]
   · rcases dw k hk with rfl | rfl
     · rw [iU,iU,hint]
     · rw [eB,eB]
lemma lx (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (x y:Fin 10 → Bool) (agree: ∀ i,i ≠ v → x i = y i)
   (pin:ℕ) (inRange:pin < 12) (primary:pin ≠ v.val)
   (hint:pin = 10 → (if useHint then x 0 && x 2 else false) =
                        (if useHint then y 0 && y 2 else false))
   (negated:pin = 11 → (ae k useHint x).getD 11 false =
                         (ae k useHint y).getD 11 false):
   (ae k useHint x).getD pin false = (ae k useHint y).getD pin false:= by
 rcases kj k useHint x pin inRange with ⟨i,rfl,_⟩ | rfl | rfl
 · rw [bL,bL]
   exact agree i (fun eq => primary (congrArg Fin.val eq))
 · rw [dm,dm]
   exact hint rfl
 · exact negated rfl
end PEqualNP.Outside.L_meta_4817.ce
namespace PEqualNP.Outside.L_meta_4817.ce
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.aJ (target)
open PEqualNP.Outside.L_meta_4817.cf
lemma bp (k:Fin 12) (useHint:Bool) (x:Fin 10 → Bool):
   (ae k useHint x).length = 12:= by simp [ae]
def Fits (C:Circuit) (k:Fin 12) (useHint:Bool):Prop:=
 ∀ x,C.eval (ae k useHint x) = target x
lemma cI (C:Circuit) (k:Fin 12) (useHint:Bool) (fits:Fits C k useHint):
   12 ≤ C.output ∧ C.output < 12 + C.gates.length:= by
 have lo:12 ≤ C.output:= by
   by_contra below
   have idx:C.output < 12:= by omega
   have read (x:Fin 10 → Bool):(ae k useHint x).getD C.output false = target x:= by
     have ev:= fits x
     change (C.wires (ae k useHint x)).getD C.output false = target x at ev
     rwa [ey.wires_input C _ _ (by simpa [bp] using idx)] at ev
   rcases kj k useHint (fun _ => false) C.output idx with ⟨v,hv,_⟩ | hint | neg
   · obtain ⟨x,diff⟩:= ch.target_not_signed_primary v false
     have h:= read x
     rw [hv,bL] at h
     exact diff (by simpa using h.symm)
   · cases useHint
     · obtain ⟨x,diff⟩:= ch.target_not_constant false
       have h:= read x
       rw [hint,dm] at h
       exact diff (by simpa using h.symm)
     · obtain ⟨x,diff⟩:= ch.target_not_signed_hint false
       have h:= read x
       rw [hint,dm] at h
       exact diff (by simpa using h.symm)
   · by_cases hk:k.val < 10
     · let v:Fin 10:= ⟨k.val,hk⟩
       obtain ⟨x,diff⟩:= ch.target_not_signed_primary v true
       have h:= read x
       rw [neg,dk k useHint x v rfl] at h
       exact diff (by simpa using h.symm)
     · rcases dw k hk with rfl | rfl
       · obtain ⟨x,diff⟩:= ch.target_not_signed_hint true
         have h:= read x
         rw [neg,iU] at h
         exact diff (by simpa using h.symm)
       · obtain ⟨x,diff⟩:= ch.target_not_constant true
         have h:= read x
         rw [neg,eB] at h
         exact diff h.symm
 refine ⟨lo,?_⟩
 by_contra above
 obtain ⟨x,diff⟩:= ch.target_not_constant false
 have ev:= fits x
 change (C.wires (ae k useHint x)).getD C.output false = target x at ev
 rw [List.getD_eq_default _ _ (by rw [ey.wires_length,bp];omega)] at ev
 exact diff ev.symm
lemma eF (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (mono:Monotone2 C) (fits:Fits C k useHint):
   ∃ i:bf C,Reads C i v.val:= by
 by_contra no
 obtain ⟨x,y,xv,yv,agree,hint,off,on⟩:= cO v
 have order:= ey.eval_true_of_read_monotonicity C (ae k useHint y)
   (ae k useHint x) (by simp [bp])
   (by simpa [bp] using (cI C k useHint fits).1)
   (fun g hg => by
     simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (mono g hg).1)
   (by
     intro j hj t ht htSmall htrue
     have ne:t ≠ v.val:= by
       rintro rfl
       exact no ⟨⟨j,hj⟩,ht⟩
     have le:= im k useHint v x y xv yv agree hint t
       (by simpa [bp] using htSmall) ne
     rw [htrue] at le
     exact Bool.eq_true_of_true_le le)
   ((fits y).trans on)
 rw [fits x,off] at order
 exact Bool.false_ne_true order
lemma h9 (C:Circuit) (k:Fin 12) (useHint:Bool)
   (i:bf C) (x y:Fin 10 → Bool)
   (initial: ∀ a ∈ (C.gates.get i).inputs,a < 12)
   (same:(C.gates.get i).op.eval ((C.gates.get i).inputs.map fun a =>
     (ae k useHint x).getD a false) =
     (C.gates.get i).op.eval ((C.gates.get i).inputs.map fun a =>
       (ae k useHint y).getD a false)):
   (C.wires (ae k useHint x)).getD (12 + i.val) false =
     (C.wires (ae k useHint y)).getD (12 + i.val) false:= by
 have left:= ey.wires_gate_of_input_reads C (ae k useHint x) i.val i.isLt
   (fun t ht => by simpa [bp] using initial t ht)
 have right:= ey.wires_gate_of_input_reads C (ae k useHint y) i.val i.isLt
   (fun t ht => by simpa [bp] using initial t ht)
 rw [bp] at left right
 exact left.trans (same.trans right.symm)
lemma dx (C:Circuit) (k:Fin 12) (useHint:Bool)
   (fits:Fits C k useHint) (x y:Fin 10 → Bool) (off:target x = false) (on:target y = true)
   (agree: ∀ i:bf C,
     (C.wires (ae k useHint x)).getD (12 + i.val) false =
       (C.wires (ae k useHint y)).getD (12 + i.val) false ∨
     ∀ t ∈ (C.gates.get i).inputs,t < 12 →
       (ae k useHint x).getD t false = (ae k useHint y).getD t false):False:= by
 have eval:= ey.eval_eq_of_read_agreement C (ae k useHint x)
   (ae k useHint y) (by simp [bp])
   (by simpa [bp] using (cI C k useHint fits).1)
   (fun i hi => by simpa [bp] using agree ⟨i,hi⟩)
 rw [fits x,fits y,off,on] at eval
 exact Bool.false_ne_true eval
end PEqualNP.Outside.L_meta_4817.ce
namespace PEqualNP.Outside.L_meta_4817.ce
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.aJ (target)
open PEqualNP.Outside.L_meta_4817.cf
lemma fp (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (x y:Fin 10 → Bool) (agree: ∀ j,j ≠ v → x j = y j)
   (j:bf C) (off: ¬ cg C j {v.val,10,11})
   (a:ℕ) (read:Reads C j a) (ha:a < 12):
   (ae k useHint x).getD a false = (ae k useHint y).getD a false:= by
 have away:a ∉ ({v.val,10,11}:Finset ℕ):= fun mem => off ⟨a,mem,read⟩
 have none:a ≠ v.val ∧ a ≠ 10 ∧ a ≠ 11:= by
   simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using away
 exact lx k useHint v x y agree a ha none.1
   (fun eq => (none.2.1 eq).elim) (fun eq => (none.2.2 eq).elim)
lemma iC (C:Circuit) (k:Fin 12) (useHint:Bool) (mono:Monotone2 C)
   (i:bf C) (x:Fin 10 → Bool) {p q:ℕ} (hp:p < 12) (hq:q < 12)
   (form:(C.gates.get i).inputs = [p,q] ∨ (C.gates.get i).inputs = [q,p]):
   (C.wires (ae k useHint x)).getD (12 + i.val) false =
     (match (C.gates.get i).op with
       | .or => (ae k useHint x).getD p false || (ae k useHint x).getD q false
       | _ => (ae k useHint x).getD p false && (ae k useHint x).getD q false):= by
 have initial (t:ℕ) (ht:t ∈ (C.gates.get i).inputs):t < (ae k useHint x).length:= by
   rw [bp]
   rcases form with eq | eq <;> rw [eq] at ht <;>
     simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
   · rcases ht with rfl | rfl <;> assumption
   · rcases ht with rfl | rfl <;> assumption
 have ev:= ey.wires_gate_of_input_reads C (ae k useHint x) i.val i.isLt initial
 rw [bp] at ev
 exact ev.trans (pD _ (hI C mono i).1 _ form)
lemma eJ (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (index:k.val = v.val) (mono:Monotone2 C) (fits:Fits C k useHint)
   (i:bf C) (untouched: ∀ j:bf C,j ≠ i → ¬ cg C j {v.val,10,11})
   (form:(C.gates.get i).inputs = [v.val,11] ∨ (C.gates.get i).inputs = [11,v.val]):False:= by
 obtain ⟨x,y,xv,yv,agree,_,off,on⟩:= cO v
 apply dx C k useHint fits x y off on
 intro j
 by_cases eq:j = i
 · subst j
   left
   have hx:= iC C k useHint mono i x (by have:= v.isLt;omega) (by decide) form
   have hy:= iC C k useHint mono i y (by have:= v.isLt;omega) (by decide) form
   rw [hx,hy,bL,bL,dk k useHint x v index,
     dk k useHint y v index,xv,yv]
   rcases (hI C mono i).1 with eq | eq <;> simp [eq]
 · exact .inr (fp C k useHint v x y agree j (untouched j eq))
end PEqualNP.Outside.L_meta_4817.ce
namespace PEqualNP.Outside.L_meta_4817.ce
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.aJ (target)
open PEqualNP.Outside.L_meta_4817.cf
lemma ln (C:Circuit) (k:Fin 12) (v:Fin 10) (i:bf C)
   (endpoint:v = 0 ∨ v = 2)
   (pins:(C.gates.get i).inputs = [v.val,10] ∨ (C.gates.get i).inputs = [10,v.val])
   (untouched: ∀ j:bf C,j ≠ i → ¬ cg C j {v.val,10,11})
   (mono:Monotone2 C) (fits:Fits C k true):
   (∀ x:Fin 10 → Bool,(C.wires (ae k true x)).getD (12 + i.val) false = x v) ∧
     ∃ j:bf C,i.val < j.val ∧ Reads C j (12 + i.val):= by
 obtain ⟨x,y,xv,yv,agree,hint,off,on⟩:= cO v
 have primaryPin:v.val < 12:= by
   have:= v.isLt
   omega
 have hintPin:(10:ℕ) < 12:= by decide
 have agreeOther (j:bf C) (different:j ≠ i):=
   fp C k true v x y agree j (untouched j different)
 rcases (hI C mono i).1 with isAnd | isOr
 · exfalso
   have andValue (z:Fin 10 → Bool):
       (C.wires (ae k true z)).getD (12 + i.val) false =
         (z v && (z 0 && z 2)):= by
     rw [iC C k true mono i z primaryPin hintPin pins,isAnd,bL,dm] <;> rfl
   have falseHint:(x 0 && x 2) = false:= by
     rcases endpoint with rfl | rfl <;> simp [xv]
   apply dx C k true fits x y off on
   intro j
   by_cases same:j = i
   · subst j
     left
     rw [andValue x,andValue y,← hint,falseHint]
     simp
   · exact Or.inr (agreeOther j same)
 · have aliasesPrimary (z:Fin 10 → Bool):
       (C.wires (ae k true z)).getD (12 + i.val) false = z v:= by
     have value:
         (C.wires (ae k true z)).getD (12 + i.val) false =
           (z v || (z 0 && z 2)):= by
       rw [iC C k true mono i z primaryPin hintPin pins,isOr,bL,dm] <;> rfl
     rw [value]
     rcases endpoint with rfl | rfl <;> cases z 0 <;> cases z 2 <;> rfl
   have outputOther:C.output ≠ 12 + i.val:= by
     intro eq
     obtain ⟨z,different⟩:= ch.target_not_signed_primary v false
     change target z ≠ z v at different
     apply different
     refine (fits z).symm.trans ?_
     simpa only [Circuit.eval,eq] using aliasesPrimary z
   have outputsDiffer:C.eval (ae k true x) ≠ C.eval (ae k true y):= by
     rw [fits x,fits y,off,on]
     decide
   obtain ⟨j,hj,ordered,uses⟩:= ey.exists_consumer_of_eval_ne C
     (ae k true x) (ae k true y) (by simp only [bp])
     (by simpa only [bp] using (cI C k true fits).1) i.val
     (by simpa only [bp] using outputOther) outputsDiffer
     (fun j hj different a read small =>
       agreeOther ⟨j,hj⟩ (fun same => different (congrArg Fin.val same)) a read
         (by simpa only [bp] using small))
   exact ⟨aliasesPrimary,⟨⟨j,hj⟩,ordered,by simpa only [Reads,List.get_eq_getElem,bp] using uses⟩⟩
end PEqualNP.Outside.L_meta_4817.ce
namespace PEqualNP.Outside.L_meta_4817.ce
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.cf
open PEqualNP.Outside.L_meta_4817.eg (aS)
def ct (C:Circuit) (k:Fin 12) (useHint:Bool) (i:ℕ):Prop:=
 (∃ b:Bool,∀ x,(ae k useHint x).getD i false = b) ∨ ¬ cl C i
private lemma kf (C:Circuit) (k:Fin 12) (useHint:Bool)
   (h10:ct C k useHint 10) (h11:ct C k useHint 11)
   (a:ℕ) (lower:10 ≤ a) (upper:a < 12) (used:cl C a):
   ∃ b:Bool,∀ x,(ae k useHint x).getD a false = b:= by
 by_cases h:a = 10
 · subst a
   exact h10.resolve_right (fun unseen => unseen used)
 · have e:a = 11:= by omega
   subst a
   exact h11.resolve_right (fun unseen => unseen used)
private lemma iK (k:Fin 12) (useHint:Bool) (v:Fin 10) (pin:ℕ)
   (fixed: ∃ b:Bool,∀ x,(ae k useHint x).getD pin false = b):
   aS ((aK k useHint v).getD pin aP):= by
 obtain ⟨b,e⟩:= fixed
 refine ⟨b,?_⟩
 funext r
 have map:= List.getD_map (l:= aK k useHint v) (n:= pin)
   (d:= aP) (fun f => f r)
 rw [gy] at map
 exact map.symm.trans (e (restrictedAll v r))
lemma eU (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (i:bf C) (a:ℕ) (readsA:Reads C i a) (small:a < 12)
   (fixed:aS ((aK k useHint v).getD a aP)):
   Free (aB (aK k useHint v) (C.gates.take i.val)) (C.gates.get i):= by
 refine Or.inr (Or.inr ⟨a,readsA,?_⟩)
 unfold aB
 rw [List.getD_append _ _ _ _ (by simpa using small)]
 exact fixed
private lemma mI (g:Gate) (arity:g.inputs.length ≤ 2):
   ∃ v:Fin 10,v.val ∉ g.inputs:= by
 by_contra! all
 have sub:({0,1,2}:Finset ℕ) ⊆ g.inputs.toFinset:= by
   intro j hj
   simp only [Finset.mem_insert,Finset.mem_singleton] at hj
   refine List.mem_toFinset.mpr ?_
   rcases hj with rfl | rfl | rfl
   · exact all 0
   · exact all 1
   · exact all 2
 have few:= (Finset.card_le_card sub).trans (List.toFinset_card_le (l:= g.inputs))
 have three:({0,1,2}:Finset ℕ).card = 3:= by decide +kernel
 omega
private lemma mm (C:Circuit) (k:Fin 12) (useHint:Bool)
   (h10:ct C k useHint 10) (h11:ct C k useHint 11)
   (p:Fin 10) (x y:Fin 10 → Bool) (agree: ∀ z,z ≠ p → x z = y z)
   (a:ℕ) (lt:a < 12) (other:a ≠ p.val) (used:cl C a):
   (ae k useHint x).getD a false = (ae k useHint y).getD a false:= by
 by_cases primary:a < 10
 · let i:Fin 10:= ⟨a,primary⟩
   have no:i ≠ p:= fun e => other (congrArg (fun z:Fin 10 => z.val) e)
   exact (bL k useHint x i).trans ((agree i no).trans (bL k useHint y i).symm)
 · obtain ⟨b,hb⟩:= kf C k useHint h10 h11 a (by omega) lt used
   exact (hb x).trans (hb y).symm
lemma dc (C:Circuit) (k:Fin 12) (useHint:Bool)
   (mono:Monotone2 C) (fits:Fits C k useHint)
   (h10:ct C k useHint 10) (h11:ct C k useHint 11):
   18 ≤ C.size:= by
 have out:= cI C k useHint fits
 let i:bf C:= ⟨0,by have hlo:= out.1;have hhi:= out.2;omega⟩
 let g:= C.gates.get i
 have spec:(g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2:= hI C mono i
 have primaryFree (v:Fin 10) (j:bf C) (read:Reads C j v.val):
     Free (aB (aK k useHint v) (C.gates.take j.val)) (C.gates.get j):=
   eU C k useHint v j _ read (by have:= v.isLt;omega) (eK k useHint v)
 have ready (v:Fin 10):Ready C k useHint v:= by
   intro a limit used
   by_cases inRaw:a < 10
   · let p:Fin 10:= ⟨a,inRaw⟩
     exact iy k useHint v p
   · exact Or.inr (Or.inl (iK k useHint v a
       (kf C k useHint h10 h11 a (by omega) limit used)))
 have firstFree (all: ∀ v:Fin 10,
     Free (aB (aK k useHint v) (C.gates.take i.val)) g):
     18 ≤ C.size:= by
   obtain ⟨v,absent⟩:= mI g spec.2
   obtain ⟨j,hj⟩:= eF C k useHint v mono fits
   have diff:i ≠ j:= by
     intro e
     subst j
     exact absent hj
   exact dl C k useHint v mono out.1 (ready v) fits i j diff
     (all v) (primaryFree v j hj)
 by_cases twoPrimary: ∃ p q:Fin 10,p ≠ q ∧ g.inputs = [p.val,q.val]
 · obtain ⟨p,q,diff,pins⟩:= twoPrimary
   have readP:Reads C i p.val:= by change p.val ∈ g.inputs;simp [pins]
   let controlling:= !(g.op.eval [])
   obtain ⟨x,y,_,_,xq,yq,agree,off,on⟩:=
     ch.dependence_at_value p q diff controlling
   have frozen:
       (C.wires (ae k useHint x)).getD (12+i.val) false =
       (C.wires (ae k useHint y)).getD (12+i.val) false:= by
     apply h9 C k useHint i x y
     · intro t ht
       change t ∈ g.inputs at ht
       simp only [pins,List.mem_cons,List.mem_nil_iff,or_false] at ht
       rcases ht with rfl | rfl
       · exact p.isLt.trans (by decide)
       · exact q.isLt.trans (by decide)
     · change g.op.eval (g.inputs.map (fun t => (ae k useHint x).getD t false)) =
         g.op.eval (g.inputs.map (fun t => (ae k useHint y).getD t false))
       simp only [pins,List.map_cons,List.map_nil,bL]
       rcases spec.1 with isAnd | isOr
       · have hx:x q = false:= by simpa [controlling,isAnd,GateOp.eval] using xq
         have hy:y q = false:= by simpa [controlling,isAnd,GateOp.eval] using yq
         simp [isAnd,GateOp.eval,hx,hy]
       · have hx:x q = true:= by simpa [controlling,isOr,GateOp.eval] using xq
         have hy:y q = true:= by simpa [controlling,isOr,GateOp.eval] using yq
         simp [isOr,GateOp.eval,hx,hy]
   have second: ∃ j:bf C,j ≠ i ∧ Reads C j p.val:= by
     by_contra onlyFirst
     apply dx C k useHint fits x y off on
     intro j
     by_cases isFirst:j = i
     · subst j
       exact Or.inl frozen
     · refine Or.inr fun t read upper => ?_
       have unequal:t ≠ p.val:= by
         rintro rfl
         exact onlyFirst ⟨j,isFirst,read⟩
       exact mm C k useHint h10 h11 p x y agree t upper unequal
         ⟨C.gates.get j,List.get_mem _ _,read⟩
   obtain ⟨j,other,readsP⟩:= second
   exact dl C k useHint p mono out.1 (ready p) fits i j other.symm
     (primaryFree p i readP) (primaryFree p j readsP)
 · apply firstFree
   intro v
   by_cases short:g.inputs.length ≤ 1
   · exact Or.inl short
   have length:g.inputs.length = 2:= by omega
   obtain ⟨a,b,pins⟩:= List.length_eq_two.mp length
   by_cases same:a = b
   · exact Or.inr (Or.inl ⟨a,by simpa only [same] using pins⟩)
   have high (pin:ℕ) (lower:10 ≤ pin) (used:pin ∈ g.inputs):
       Free (aB (aK k useHint v) (C.gates.take i.val)) g:= by
     by_cases below:pin < 12
     · exact eU C k useHint v i pin used below
         (iK k useHint v pin
           (kf C k useHint h10 h11 pin lower below ⟨g,List.get_mem _ _,used⟩))
     · refine Or.inr (Or.inr ⟨pin,used,?_⟩)
       have emptyPrefix:C.gates.take i.val = []:= by simp [i]
       rw [emptyPrefix]
       have value:aB (aK k useHint v) [] = aK k useHint v:= by
         change aK k useHint v ++ [] = aK k useHint v
         simp
       rw [value,List.getD_eq_default _ _ (by simp;omega)]
       exact ⟨false,rfl⟩
   by_cases aRaw:a < 10
   · by_cases bRaw:b < 10
     · exact (twoPrimary ⟨⟨a,aRaw⟩,⟨b,bRaw⟩,fun h =>
         same (congrArg (fun z:Fin 10 => z.val) h),pins⟩).elim
     · exact high b (by omega) (by simp [pins])
   · exact high a (by omega) (by simp [pins])
end PEqualNP.Outside.L_meta_4817.ce
namespace PEqualNP.Outside.L_meta_4817.lk
open PEqualNP.CircuitLowerBounds
def step (w:List Bool) (g:Gate):List Bool:=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma lA (C:Circuit) (x:List Bool):C.wires x = C.gates.foldl step x:= rfl
lemma o3 (a a' b b':Bool) (h1:a ≤ a') (h2:b ≤ b'):(a && b) ≤ (a' && b'):= by
 revert h1 h2
 cases a <;> cases a' <;> cases b <;> cases b' <;> decide
lemma ul (a a' b b':Bool) (h1:a ≤ a') (h2:b ≤ b'):(a || b) ≤ (a' || b'):= by
 revert h1 h2
 cases a <;> cases a' <;> cases b <;> cases b' <;> decide
lemma tl (l:List ℕ) (f f':ℕ → Bool) (h: ∀ i,f i ≤ f' i):
   (l.map f).all id ≤ (l.map f').all id:= by
 induction l with
 | nil => exact le_refl _
 | cons a l ih =>
   simp only [List.map_cons,List.all_cons,id]
   exact o3 _ _ _ _ (h a) ih
lemma tg (l:List ℕ) (f f':ℕ → Bool) (h: ∀ i,f i ≤ f' i):
   (l.map f).any id ≤ (l.map f').any id:= by
 induction l with
 | nil => exact le_refl _
 | cons a l ih =>
   simp only [List.map_cons,List.any_cons,id]
   exact ul _ _ _ _ (h a) ih
lemma ra (W:List Bool) (v:Bool) (i:ℕ):
   (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false:= by
 split_ifs with h1 h2
 · exact List.getD_append _ _ _ _ h1
 · subst h2
   simp
 · rw [List.getD_eq_default]
   simp
   omega
def R (W W':List Bool):Prop:=
 W.length = W'.length ∧ ∀ i,W.getD i false ≤ W'.getD i false
lemma vg (W W':List Bool) (g:Gate) (hg:g.op = GateOp.and ∨ g.op = GateOp.or)
   (h:R W W'):R (step W g) (step W' g):= by
 obtain ⟨hl,hle⟩:= h
 have hv:g.op.eval (g.inputs.map fun i => W.getD i false) ≤
     g.op.eval (g.inputs.map fun i => W'.getD i false):= by
   rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
   · exact tl _ _ _ hle
   · exact tg _ _ _ hle
 refine ⟨by simp [step,hl],fun i => ?_⟩
 simp only [step,ra,hl]
 split_ifs
 · exact hle i
 · exact hv
 · exact le_refl _
lemma vh (gs:List Gate) (hgs: ∀ g ∈ gs,g.op = GateOp.and ∨ g.op = GateOp.or):
   ∀ W W':List Bool,R W W' → R (gs.foldl step W) (gs.foldl step W'):= by
 induction gs with
 | nil => intro W W' h;exact h
 | cons g gs ih =>
   intro W W' h
   simp only [List.foldl_cons]
   exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
     (vg W W' g (hgs g List.mem_cons_self) h)
lemma mD {l1 l1' l2 l2':List Bool} (h1:R l1 l1') (h2:R l2 l2'):
   R (l1 ++ l2) (l1' ++ l2'):= by
 obtain ⟨hl1,h1⟩:= h1
 obtain ⟨hl2,h2⟩:= h2
 refine ⟨by simp [hl1,hl2],fun i => ?_⟩
 by_cases hi:i < l1.length
 · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (hl1 ▸ hi)]
   exact h1 i
 · have hi':l1.length ≤ i:= by omega
   rw [List.getD_append_right _ _ _ _ hi',List.getD_append_right _ _ _ _ (hl1 ▸ hi'),hl1]
   exact h2 _
lemma tk {n:ℕ} (f g:Fin n → Bool) (h: ∀ i,f i ≤ g i):
   R (List.ofFn f) (List.ofFn g):= by
 refine ⟨by simp,fun i => ?_⟩
 by_cases hi:i < n
 · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi)]
   simp only [List.getElem_ofFn]
   exact h ⟨i,hi⟩
 · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
lemma lM (C:Circuit) (hm:PEqualNP.MetaComplexity.Monotone2 C) (l l':List Bool)
   (h:R l l'):C.eval l ≤ C.eval l':= by
 have hops: ∀ g ∈ C.gates,g.op = GateOp.and ∨ g.op = GateOp.or:= by
   intro g hg
   have:= (hm g hg).1
   simpa using this
 show (C.wires l).getD C.output false ≤ (C.wires l').getD C.output false
 rw [lA,lA]
 exact (vh C.gates hops _ _ h).2 C.output
end PEqualNP.Outside.L_meta_4817.lk
namespace PEqualNP.Outside.L_meta_4817.ir
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.lk (R mD tk o3 lM)
open PEqualNP.Outside.L_meta_4817.aJ (target base inputs)
private def edges:List (Fin 10 × Fin 10):=
 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]
private lemma og (x:Fin 10 → Bool):
   target x = true ↔ ∃ e ∈ edges,x e.1 = true ∧ x e.2 = true:= by
 have same:target x = edges.any (fun e => x e.1 && x e.2):= by
   simp [target,edges,Bool.or_assoc]
 rw [same,List.any_eq_true]
 simp only [Bool.and_eq_true]
private def extra (k:Fin 12):Finset (Fin 10):=
 if hk:k.val < 10 then {⟨k.val,hk⟩} else if k.val = 10 then {0,2} else ∅
private def eE (e:Fin 10 × Fin 10) (k:Fin 12):Finset (Fin 10):=
 {e.1,e.2} ∪ extra k
private def keep (e:Fin 10 × Fin 10) (k:Fin 12) (x:Fin 10 → Bool):
   Fin 10 → Bool:= fun i => x i && decide (i ∈ eE e k)
private lemma ux (e:Fin 10 × Fin 10) (k:Fin 12) (x:Fin 10 → Bool):
   ∀ i,keep e k x i ≤ x i:= by
 intro i
 cases h:x i <;> simp [keep,h]
private lemma pk (e:Fin 10 × Fin 10) (k:Fin 12) (x:Fin 10 → Bool)
   (he:e ∈ edges) (ha:x e.1 = true) (hb:x e.2 = true):
   target (keep e k x) = true:= by
 apply (og _).mpr
 exact ⟨e,he,by simp [keep,eE,ha],by simp [keep,eE,hb]⟩
private lemma fw (x:Fin 10 → Bool) (i:Fin 10):
   (base x).getD i.val false = x i:= by
 unfold base
 rw [List.getD_append _ _ _ _ (by simpa using i.isLt),
   List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn] <;> rfl
private lemma i6 (x:Fin 10 → Bool):
   (base x).getD 10 false = (x 0 && x 2):= by
 unfold base
 rw [List.getD_append_right _ _ _ _ (by simp)] <;> simp
private lemma lu (x:Fin 10 → Bool) (i:ℕ) (hi:11 ≤ i):
   (base x).getD i false = false:= by
 exact List.getD_eq_default _ _ (by simpa [base] using hi)
private lemma rl (e:Fin 10 × Fin 10) (k:Fin 12) (x:Fin 10 → Bool):
   (base (keep e k x)).getD k.val false = (base x).getD k.val false:= by
 by_cases hk:k.val < 10
 · let i:Fin 10:= ⟨k.val,hk⟩
   change (base (keep e k x)).getD i.val false = (base x).getD i.val false
   rw [fw,fw]
   have atI:i ∈ eE e k:= by simp [eE,extra,hk,i]
   simp [keep,atI]
 · by_cases h10:k.val = 10
   · rw [h10,i6,i6]
     have h₀:(0:Fin 10) ∈ eE e k:= by simp [eE,extra,hk,h10]
     have h₂:(2:Fin 10) ∈ eE e k:= by simp [eE,extra,hk,h10]
     simp [keep,h₀,h₂]
   · rw [lu _ _ (by omega),lu _ _ (by omega)]
private lemma mi {a b:Bool} (h:a ≤ b):R [a] [b]:= by
 refine ⟨rfl,?_⟩
 intro i
 cases i with
 | zero => exact h
 | succ i =>
     rw [List.getD_eq_default _ _ (by simp),List.getD_eq_default _ _ (by simp)] <;> exact le_refl _
private def iW (k:Fin 12) (x:Fin 10 → Bool) (hint:Bool):List Bool:=
 (List.ofFn x ++ [hint]) ++ [!(base x).getD k.val false]
private lemma jk (k:Fin 12) (y x:Fin 10 → Bool) (ha hb:Bool)
   (hy: ∀ i,y i ≤ x i) (hh:ha ≤ hb)
   (seed:(base y).getD k.val false = (base x).getD k.val false):
   R (iW k y ha) (iW k x hb):=
 mD (mD (tk y x hy) (mi hh))
   (mi (by rw [seed] <;> exact le_refl _))
def em (k:Fin 12):Prop:= k.val = 0 ∨ k.val = 2 ∨ k.val = 10
def cV (k:Fin 12) (x:Fin 10 → Bool):List Bool:=
 iW k x false
private lemma nS: ∀ e:Fin 10 × Fin 10,e ∈ edges →
   ¬ ((0:Fin 10) ∈ ({e.1,e.2}:Finset (Fin 10)) ∧
     (2:Fin 10) ∈ ({e.1,e.2}:Finset (Fin 10))):= by
 decide +kernel
private lemma ni (k:Fin 12) (ordinary: ¬em k):
   (0:Fin 10) ∉ extra k ∧ (2:Fin 10) ∉ extra k:= by
 have h₀:k.val ≠ 0:= fun h => ordinary (Or.inl h)
 have h₂:k.val ≠ 2:= fun h => ordinary (Or.inr (Or.inl h))
 have h₁₀:k.val ≠ 10:= fun h => ordinary (Or.inr (Or.inr h))
 by_cases hk:k.val < 10
 · have zero:(0:Fin 10) ≠ ⟨k.val,hk⟩:= by
     intro h
     exact h₀ (congrArg Fin.val h).symm
   have two:(2:Fin 10) ≠ ⟨k.val,hk⟩:= by
     intro h
     exact h₂ (congrArg Fin.val h).symm
   simp [extra,hk,zero,two]
 · simp [extra,hk,h₁₀]
private lemma mq (e:Fin 10 × Fin 10) (he:e ∈ edges) (k:Fin 12)
   (ordinary: ¬em k) (x:Fin 10 → Bool):
   (keep e k x 0 && keep e k x 2) = false:= by
 apply Bool.eq_false_iff.mpr
 intro h
 simp only [Bool.and_eq_true] at h
 obtain ⟨h₀,h₂⟩:= h
 change (x 0 && decide ((0:Fin 10) ∈ eE e k)) = true at h₀
 change (x 2 && decide ((2:Fin 10) ∈ eE e k)) = true at h₂
 simp only [Bool.and_eq_true,decide_eq_true_eq] at h₀ h₂
 have zero:= h₀.2
 have two:= h₂.2
 have blocked:= ni k ordinary
 exact nS e he
   ⟨(Finset.mem_union.mp zero).resolve_right blocked.1,
     (Finset.mem_union.mp two).resolve_right blocked.2⟩
lemma lj (C:Circuit) (k:Fin 12) (mono:Monotone2 C)
   (ordinary: ¬em k) (fits: ∀ x,C.eval (inputs k x) = target x):
   ∀ x,C.eval (cV k x) = target x:= by
 intro x
 cases h:target x with
 | false =>
     have relation:R (cV k x) (inputs k x):=
       jk k x x false _ (fun _ => le_refl _) (Bool.false_le _) rfl
     have order:= lM C mono _ _ relation
     rw [fits x,h] at order
     exact le_antisymm order (Bool.false_le _)
 | true =>
     obtain ⟨e,he,ha,hb⟩:= (og x).mp h
     let y:= keep e k x
     have same:cV k y = inputs k y:= by
       change iW k y false = iW k y (y 0 && y 2)
       rw [mq e he k ordinary x]
     have yFit:C.eval (cV k y) = true:=
       (congrArg C.eval same).trans ((fits y).trans (pk e k x he ha hb))
     have relation:R (cV k y) (cV k x):=
       jk k y x false false (ux e k x) (le_refl _) (rl e k x)
     have order:= lM C mono _ _ relation
     rw [yFit] at order
     exact Bool.eq_true_of_true_le order
def ExceptionalCase:Prop:=
 ∀ (C:Circuit) (k:Fin 12),em k → Monotone2 C → C.size ≤ 17 →
   ∃ x,C.eval (inputs k x) ≠ target x
def OrdinaryCase:Prop:=
 ∀ (C:Circuit) (k:Fin 12),¬em k → Monotone2 C → C.size ≤ 17 →
   ∃ x,C.eval (cV k x) ≠ target x
end PEqualNP.Outside.L_meta_4817.ir
namespace PEqualNP.Outside.L_meta_4817.cf
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4817.eg (Wire aS Row)
private lemma lg {R:Type} (seed:List (Wire R))
   (gs:List Gate) (count pin:ℕ)
   (earlier:pin < (aB seed (gs.take count)).length):
   (aB seed (gs.take count)).getD pin aP =
     (aB seed gs).getD pin aP:= by
 let prior:= bk seed (gs.take count) []
 obtain ⟨tail,ext,_⟩:= dj seed prior (gs.drop count)
 have eq:aB seed gs = aB seed (gs.take count) ++ tail:= by
   unfold aB
   conv_lhs => rw [← List.take_append_drop count gs,fq]
   change seed ++ bk seed (gs.drop count) prior = (seed ++ prior) ++ tail
   rw [ext,List.append_assoc]
 rw [eq,List.getD_append _ _ _ _ earlier]
lemma m3 (C:Circuit) (k:Fin 12) (v:Fin 10)
   (i j:Fin C.gates.length) (ordered:i.val < j.val)
   (aliasesPrimary: ∀ x,(C.wires (ae k true x)).getD (12 + i.val) false = x v)
   (reads:12 + i.val ∈ (C.gates.get j).inputs):
   Free (aB (aK k true v) (C.gates.take j.val)) (C.gates.get j):= by
 let seed:= aK k true v
 have earlier:12 + i.val < (aB seed (C.gates.take j.val)).length:= by
   rw [jx,show seed.length = 12 from seedColumns_length k true v,List.length_take]
   rw [Nat.min_eq_left j.isLt.le]
   omega
 refine .inr (.inr ⟨12 + i.val,reads,false,?_⟩)
 change (aB seed (C.gates.take j.val)).getD (12 + i.val) aP = fun _ => false
 rw [lg _ _ _ _ earlier]
 funext r
 have value:= List.getD_map (l:= aB seed C.gates) (n:= 12 + i.val)
   (d:= aP) (fun f:Wire Row => f r)
 rw [om,gy] at value
 rw [← value]
 change (C.wires (ae k true (restrictedAll v r))).getD (12 + i.val) false = false
 exact (aliasesPrimary _).trans (restrictedAll_self v r)
end PEqualNP.Outside.L_meta_4817.cf
namespace PEqualNP.Outside.L_meta_4817.ce
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.cf
lemma h8 (C:Circuit) (a:ℕ):
   cl C a ↔ ∃ i:bf C,Reads C i a:= by
 constructor
 · rintro ⟨g,mem,read⟩
   obtain ⟨i,eq⟩:= List.mem_iff_get.mp mem
   refine ⟨i,?_⟩
   change a ∈ (C.gates.get i).inputs
   rwa [eq]
 · rintro ⟨i,reads⟩
   exact ⟨C.gates.get i,List.get_mem C.gates i,reads⟩
lemma jt (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (hintFixed:useHint = false ∨ v = 0 ∨ v = 2)
   (negativeFixed:k.val = v.val ∨ k.val = 11 ∨ (k.val = 10 ∧ (v = 0 ∨ v = 2)))
   (mono:Monotone2 C) (fits:Fits C k useHint)
   (i j:bf C) (distinct:i ≠ j)
   (hi:cg C i {v.val,10,11}) (hj:cg C j {v.val,10,11}):
   18 ≤ C.size:= by
 have free (g:bf C) (h:cg C g {v.val,10,11}):
     Free (aB (aK k useHint v) (C.gates.take g.val)) (C.gates.get g):= by
   obtain ⟨pin,member,reads⟩:= h
   simp only [Finset.mem_insert,Finset.mem_singleton] at member
   apply eU C k useHint v g pin reads
   · rcases member with rfl | rfl | rfl
     · have:= v.isLt
       omega
     · decide
     · decide
   · rcases member with rfl | rfl | rfl
     · exact eK _ _ _
     · exact jq _ _ _ hintFixed
     · exact lD _ _ _ negativeFixed
 exact dl C k useHint v mono (cI C k useHint fits).1
   (m6 C k useHint v (.inl hintFixed) (.inl negativeFixed)) fits
   i j distinct (free i hi) (free j hj)
end PEqualNP.Outside.L_meta_4817.ce
namespace PEqualNP.Outside.L_meta_4817.ce
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.aJ (target)
open PEqualNP.Outside.L_meta_4817.cf
private lemma hM (C:Circuit) (k:Fin 12):
   ct C k false 10:=
 .inl ⟨false,fun x => by rw [dm];rfl⟩
private lemma eH (C:Circuit) (k:Fin 12) (useHint:Bool) (v:Fin 10)
   (index:k.val = v.val) (hintFixed:useHint = false ∨ v = 0 ∨ v = 2)
   (mono:Monotone2 C) (fits:Fits C k useHint):18 ≤ C.size:= by
 classical
 by_cases used:cl C 11 ∨ (useHint = true ∧ cl C 10)
 · obtain ⟨i,hi⟩:= eF C k useHint v mono fits
   have inPins:cg C i {v.val,10,11}:= ⟨v.val,by simp,hi⟩
   rcases kk C _ i inPins with ⟨j,ne,hj⟩ | unique
   · exact jt C k useHint v hintFixed (.inl index) mono fits i j ne.symm inPins hj
   · have untouched (j:bf C) (ne:j ≠ i): ¬ cg C j {v.val,10,11}:=
       fun h => ne (unique j h)
     rcases used with negative | ⟨hintOn,positive⟩
     · obtain ⟨j,hj⟩:= (h8 C 11).mp negative
       have eq:= unique j ⟨11,by simp,hj⟩
       subst j
       have pins:= fi (hI C mono i).2 hi hj (by have:= v.isLt;omega)
       exact (eJ C k useHint v index mono fits i untouched pins).elim
     · subst useHint
       have endpoint:v = 0 ∨ v = 2:= hintFixed.resolve_left (by decide)
       obtain ⟨j,hj⟩:= (h8 C 10).mp positive
       have eq:= unique j ⟨10,by simp,hj⟩
       subst j
       have pins:= fi (hI C mono i).2 hi hj (by have:= v.isLt;omega)
       obtain ⟨wire,q,order,reads⟩:= ln C k v i endpoint pins untouched mono fits
       have v12:v.val < 12:= by have:= v.isLt;omega
       exact dl C k true v mono (cI C k true fits).1
         (m6 C k true v (.inl (.inr endpoint)) (.inl (.inl index))) fits
         i q (fun eq => (Nat.ne_of_lt order) (congrArg Fin.val eq))
         (eU C k true v i v.val hi v12 (eK _ _ _))
         (m3 C k v i q order wire reads)
 · have h10:ct C k useHint 10:= by
     cases useHint
     · exact hM C k
     · exact .inr (fun h => used (.inr ⟨rfl,h⟩))
   exact dc C k useHint mono fits h10 (.inr (fun h => used (.inl h)))
private lemma nu (C:Circuit) (mono:Monotone2 C) (fits:Fits C 10 true):
   18 ≤ C.size:= by
 classical
 by_cases extras:cl C 10 ∨ cl C 11
 · obtain ⟨pin,hp,use⟩: ∃ a:ℕ,(a = 10 ∨ a = 11) ∧ cl C a:= by
     rcases extras with h | h
     · exact ⟨10,.inl rfl,h⟩
     · exact ⟨11,.inr rfl,h⟩
   obtain ⟨i,read⟩:= (h8 C pin).mp use
   obtain ⟨u,ru⟩:= eF C 10 true 0 mono fits
   obtain ⟨w,rw⟩:= eF C 10 true 2 mono fits
   have lower (v:Fin 10) (endpoint:v = 0 ∨ v = 2)
       (j:bf C) (rj:Reads C j v.val) (ne:j ≠ i):18 ≤ C.size:= by
     apply jt C 10 true v (.inr endpoint) (.inr (.inr ⟨rfl,endpoint⟩))
       mono fits j i ne
     · exact ⟨v.val,by simp,rj⟩
     · exact ⟨pin,by simp [hp],read⟩
   by_cases hu:u = i
   · by_cases hw:w = i
     · subst u
       subst w
       have form:= fi (hI C mono i).2 ru rw (by decide)
       have bad:pin = 0 ∨ pin = 2:= by
         change pin ∈ (C.gates.get i).inputs at read
         rcases form with h | h
         · rw [h] at read
           simpa using read
         · rw [h] at read
           simpa [or_comm] using read
       rcases hp with rfl | rfl <;> simp at bad
     · exact lower 2 (.inr rfl) w rw hw
   · exact lower 0 (.inl rfl) u ru hu
 · exact dc C 10 true mono fits
     (.inr (fun h => extras (.inl h))) (.inr (fun h => extras (.inr h)))
lemma iN:ir.ExceptionalCase:= by
 intro C k exceptional mono cap
 by_contra missing
 have fits:Fits C k true:= by
   intro x
   by_contra differs
   exact missing ⟨x,differs⟩
 have lower:18 ≤ C.size:= by
   rcases exceptional with first | second | both
   · exact eH C k true 0 first (.inr (.inl rfl)) mono fits
   · exact eH C k true 2 second (.inr (.inr rfl)) mono fits
   · have eq:k = 10:= Fin.ext both
     subst k
     exact nu C mono fits
 omega
lemma ko:ir.OrdinaryCase:= by
 intro C k ordinary mono cap
 by_contra missing
 have fits:Fits C k false:= by
   intro x
   by_contra differs
   exact missing ⟨x,differs⟩
 have lower:18 ≤ C.size:= by
   by_cases small:k.val < 10
   · exact eH C k false ⟨k.val,small⟩ rfl (.inl rfl) mono fits
   · rcases dw k small with rfl | rfl
     · exact (ordinary (.inr (.inr rfl))).elim
     · exact dc C 11 false mono fits (hM C 11)
         (.inl ⟨true,eB false⟩)
 omega
end PEqualNP.Outside.L_meta_4817.ce
namespace PEqualNP.Outside.L_meta_4817
lemma monotoneMismatch
   (C:PEqualNP.CircuitLowerBounds.Circuit) (k:Fin 12)
   (fan:PEqualNP.MetaComplexity.FanInTwo C)
   (pure: ∀ g ∈ C.gates,g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not)
   (size:C.size ≤ 17):
   ∃ x:Fin 10 → Bool,
     C.eval (PEqualNP.Outside.L_meta_4817.aJ.inputs k x) ≠
       PEqualNP.Outside.L_meta_4817.aJ.target x:= by
 classical
 by_contra missing
 have mono:PEqualNP.MetaComplexity.Monotone2 C:= by
   intro g hg
   have ops:g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
       g.op = PEqualNP.CircuitLowerBounds.GateOp.not:= by
     simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan g hg).1
   have bK:g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       g.op = PEqualNP.CircuitLowerBounds.GateOp.or:= by
     rcases ops with a | b | c
     · exact Or.inl a
     · exact Or.inr b
     · exact (pure g hg c).elim
   exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using bK,(fan g hg).2⟩
 have fits (x:Fin 10 → Bool):
     C.eval (PEqualNP.Outside.L_meta_4817.aJ.inputs k x) =
       PEqualNP.Outside.L_meta_4817.aJ.target x:= by
   by_contra different
   exact missing ⟨x,different⟩
 by_cases hk:PEqualNP.Outside.L_meta_4817.ir.em k
 · obtain ⟨x,hx⟩:= PEqualNP.Outside.L_meta_4817.ce.iN C k hk mono size
   exact hx (fits x)
 · obtain ⟨x,hx⟩:= PEqualNP.Outside.L_meta_4817.ce.ko C k hk mono size
   exact hx (PEqualNP.Outside.L_meta_4817.ir.lj C k mono hk fits x)
end PEqualNP.Outside.L_meta_4817

namespace PEqualNP.Outside.L_meta_4817.aJ
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
noncomputable def paid (g:Gate):Bool:= GateOp.rec true true false (fun _ => true) true g.op
private lemma accounting (C:Circuit):C.gates.countP paid + PEqualNP.NotBracket.notCount C = C.size:= by
 unfold PEqualNP.NotBracket.notCount Circuit.size
 induction C.gates with
 | nil => rfl
 | cons g gs ih =>
   cases g with
   | mk op ins =>
     cases op <;> simp [paid,List.countP_cons] <;> omega
end PEqualNP.Outside.L_meta_4817.aJ
namespace PEqualNP.Outside.L_meta_4817.bQ
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.eg
open PEqualNP.Outside.L_meta_4817.aJ (target)
def cz (r:Row):Fin 10 → Bool:=
 ![false,cn r 4,cn r 0,cn r 1,cn r 6,
   cn r 7,cn r 3,cn r 5,cn r 2,cn r 8]
def original:List (Wire Row):= inputs.map aF
private lemma zzzy (i:Fin 10):
   ad true original (fun r => cz r i):= by
 have col (j:Fin 9):ad true original (fun r => cn r j):= by
   have inList:j.val < inputs.length:= by
     have same:inputs.length = 9:= rfl
     rw [same]
     exact j.isLt
   left
   unfold original
   refine List.mem_map.mpr ⟨inputs[j.val],List.getElem_mem inList,?_⟩
   funext r
   exact (congrArg (bit r) (List.getD_eq_getElem _ _ inList)).symm
 fin_cases i
 · exact Or.inr (Or.inl ⟨false,rfl⟩)
 · exact col 4
 · exact col 0
 · exact col 1
 · exact col 6
 · exact col 7
 · exact col 3
 · exact col 5
 · exact col 2
 · exact col 8
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
lemma ff: ∀ r:Row,target (cz r) = aF graph r:= by
 decide +kernel
end PEqualNP.Outside.L_meta_4817.bQ
namespace PEqualNP.Outside.L_meta_4817.cq
inductive iu (n:ℕ) where
 | literal (v:Fin n)
 | hint
 deriving DecidableEq
inductive sy (n:ℕ) where
 | source (s:iu n)
 | earlier (j:ℕ)
 | constant (b:Bool)
 deriving DecidableEq
structure aQ (n:ℕ) where
 origin:sy n
 negated:Bool
 deriving DecidableEq
structure Join (n:ℕ) where
 isOr:Bool
 left:aQ n
 right:aQ n
def bF {n:ℕ} (p q:Fin n) (x:Fin n → Bool):iu n → Bool
 | .literal v => x v
 | .hint => x p && x q
def aA {n:ℕ} (p q:Fin n) (x:Fin n → Bool) (past:List Bool)
   (a:aQ n):Bool:=
 let value:= match a.origin with
   | .source s => bF p q x s
   | .earlier j => past.getD j false
   | .constant b => b
 if a.negated then !value else value
def cE {n:ℕ} (p q:Fin n) (x:Fin n → Bool) (past:List Bool) (g:Join n):
   Bool:=
 let a:= aA p q x past g.left
 let b:= aA p q x past g.right
 if g.isOr then a || b else a && b
def run {n:ℕ} (p q:Fin n) (x:Fin n → Bool) (gs:List (Join n))
   (past:List Bool):List Bool:=
 gs.foldl (fun values g => values ++ [cE p q x values g]) past
def output {n:ℕ} (p q:Fin n) (x:Fin n → Bool) (gs:List (Join n))
   (out:aQ n):Bool:=
 aA p q x (run p q x gs []) out
def reads {n:ℕ} (g:Join n) (s:iu n):Prop:=
 g.left.origin = .source s ∨ g.right.origin = .source s
private lemma eX {n:ℕ} (p q:Fin n) (x y:Fin n → Bool) (past:List Bool)
   (a:aQ n)
   (same: ∀ s,a.origin = .source s → bF p q x s = bF p q y s):
   aA p q x past a = aA p q y past a:= by
 cases a with
 | mk origin negated =>
   cases origin with
   | source s =>
     have equal:= same s rfl
     simp [aA,equal]
   | earlier j => rfl
   | constant b => rfl
private lemma nZ {n:ℕ} (p q:Fin n) (x y:Fin n → Bool) (gs:List (Join n))
   (same: ∀ g ∈ gs,∀ s,reads g s → bF p q x s = bF p q y s)
   (past:List Bool):
   run p q x gs past = run p q y gs past:= by
 induction gs generalizing past with
 | nil => rfl
 | cons g gs ih =>
   have l:= eX p q x y past g.left
     (fun s eq => same g List.mem_cons_self s (Or.inl eq))
   have r:= eX p q x y past g.right
     (fun s eq => same g List.mem_cons_self s (Or.inr eq))
   have joinEq:cE p q x past g = cE p q y past g:= by
     simp [cE,l,r]
   change run p q x gs (past ++ [cE p q x past g]) =
     run p q y gs (past ++ [cE p q y past g])
   rw [joinEq]
   exact ih (fun h hg => same h (List.mem_cons_of_mem _ hg)) _
lemma lJ {n:ℕ} (p q:Fin n) (gs:List (Join n)) (out:aQ n)
   (outGate: ∃ j,out.origin = .earlier j) (s:iu n) (x y:Fin n → Bool)
   (same: ∀ t,t ≠ s → bF p q x t = bF p q y t)
   (changes:output p q x gs out ≠ output p q y gs out):
   ∃ j:Fin gs.length,reads (gs.get j) s:= by
 by_contra none
 have stable (g:Join n) (hg:g ∈ gs) (t:iu n) (use:reads g t):
     bF p q x t = bF p q y t:= by
   apply same t
   rintro rfl
   obtain ⟨j,eq⟩:= List.mem_iff_get.mp hg
   exact none ⟨j,by simpa only [eq] using use⟩
 have runSame:= nZ p q x y gs stable []
 apply changes
 unfold output
 rw [runSame]
 obtain ⟨j,eq⟩:= outGate
 apply eX
 intro t ht
 rw [eq] at ht
 cases ht
private lemma mu {n:ℕ} (g:Join n) (p q:Fin n) (ne:p ≠ q)
   (h:reads g .hint) (a:reads g (.literal p)) (b:reads g (.literal q)):False:= by
 unfold reads at h a b
 rcases h with h | h <;> rcases a with a | a <;> rcases b with b | b <;>
   simp_all
lemma ix {n:ℕ} (gs:List (Join n)) (p q:Fin n) (ne:p ≠ q)
   (readHint: ∃ j:Fin gs.length,reads (gs.get j) .hint)
   (readP: ∃ j:Fin gs.length,reads (gs.get j) (.literal p))
   (readQ: ∃ j:Fin gs.length,reads (gs.get j) (.literal q)):
   ∃ v:Fin n,(v = p ∨ v = q) ∧
     ∃ a b:Fin gs.length,a ≠ b ∧
       (reads (gs.get a) .hint ∨ reads (gs.get a) (.literal v)) ∧
       (reads (gs.get b) .hint ∨ reads (gs.get b) (.literal v)):= by
 obtain ⟨hint,hh⟩:= readHint
 obtain ⟨first,hf⟩:= readP
 obtain ⟨second,hs⟩:= readQ
 by_cases hp:hint = first
 · by_cases hq:hint = second
   · subst first
     subst second
     exact (mu (gs.get hint) p q ne hh hf hs).elim
   · exact ⟨q,Or.inr rfl,hint,second,hq,Or.inl hh,Or.inr hs⟩
 · exact ⟨p,Or.inl rfl,hint,first,hp,Or.inl hh,Or.inr hf⟩
lemma hY {n:ℕ} {R:Type} (p q v:Fin n)
   (endpoint:v = p ∨ v = q) (xs:R → Fin n → Bool) (cold: ∀ r,xs r v = false)
   (past:R → List Bool) (g:Join n)
   (h:reads g .hint ∨ reads g (.literal v)):
   (∃ b:Bool,(fun r => aA p q (xs r) (past r) g.left) = fun _ => b) ∨
   (∃ b:Bool,(fun r => aA p q (xs r) (past r) g.right) = fun _ => b):= by
 have hintZero (r:R):bF p q (xs r) .hint = false:= by
   rcases endpoint with rfl | rfl <;> simp [bF,cold]
 have const (a:aQ n) (origin:a.origin = .source .hint ∨ a.origin = .source (.literal v)):
     ∃ b:Bool,(fun r => aA p q (xs r) (past r) a) = fun _ => b:= by
   refine ⟨a.negated,?_⟩
   funext r
   rcases origin with eq | eq
   · cases hneg:a.negated <;> simp [aA,eq,hintZero,hneg]
   · cases hneg:a.negated <;> simp [aA,eq,bF,cold,hneg]
 rcases h with h | h <;> rcases h with h | h
 · exact Or.inl (const _ (Or.inl h))
 · exact Or.inr (const _ (Or.inl h))
 · exact Or.inl (const _ (Or.inr h))
 · exact Or.inr (const _ (Or.inr h))
end PEqualNP.Outside.L_meta_4817.cq
namespace PEqualNP.Outside.L_meta_4817.cq
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def nf {n:ℕ} (i:Fin n):aQ n:= ⟨.source (.literal i),false⟩
def qu (n:ℕ):aQ n:= ⟨.source .hint,false⟩
def en (n:ℕ) (b:Bool):aQ n:= ⟨.constant b,false⟩
def cZ {n:ℕ} (a:aQ n):aQ n:= ⟨a.origin,!a.negated⟩
def bO {n:ℕ} (refs:List (aQ n)) (i:ℕ):aQ n:=
 refs.getD i (en n false)
def bz {n:ℕ} (limit:ℕ) (a:aQ n):Prop:=
 match a.origin with
 | .earlier i => i < limit
 | _ => True
def cR {n:ℕ} (a:aQ n):Option Bool:=
 match a.origin with
 | .constant c => some (if a.negated then !c else c)
 | _ => none
def ee {n:ℕ} (limit:ℕ) (g:Join n):Prop:=
 bz limit g.left ∧ bz limit g.right ∧ cR g.left = none ∧
   cR g.right = none ∧ g.left.origin ≠ g.right.origin
def a0 {n:ℕ}:ℕ → List (Join n) → Prop
 | _,[] => True
 | limit,g::gs => ee limit g ∧ a0 (limit + 1) gs
noncomputable def nonNot (g:Gate):Bool:= GateOp.rec true true false (fun _ => true) true g.op
private def dz (isOr a b:Bool):Bool:= if isOr then a || b else a && b
private lemma nt (isOr a b:Bool):dz isOr a b = dz isOr b a:= by
 cases isOr <;> simp [dz,Bool.or_comm,Bool.and_comm]
private lemma ou {n:ℕ} {limit limit':ℕ} {a:aQ n}
   (le:limit ≤ limit') (ok:bz limit a):bz limit' a:= by
 cases a with
 | mk src sign =>
   cases src with
   | source i => trivial
   | constant b => trivial
   | earlier i => exact Nat.lt_of_lt_of_le ok le
private lemma cH {n:ℕ} {limit:ℕ} {refs:List (aQ n)}
   (ok: ∀ a ∈ refs,bz limit a) (i:ℕ):bz limit (bO refs i):= by
 by_cases bound:i < refs.length
 · rw [bO,List.getD_eq_getElem _ _ bound]
   exact ok _ (List.getElem_mem bound)
 · rw [bO,List.getD_eq_default _ _ (Nat.le_of_not_lt bound)]
   trivial
@[simp] private lemma valueConstant {n:ℕ} (p q:Fin n) (x:Fin n → Bool)
   (past:List Bool) (c:Bool):
   aA p q x past (en n c) = c:= rfl
@[simp] private lemma valueComplement {n:ℕ} (p q:Fin n) (x:Fin n → Bool)
   (past:List Bool) (a:aQ n):
   aA p q x past (cZ a) = !(aA p q x past a):= by
 cases a with
 | mk src s => cases s <;> cases src <;> simp [cZ,aA]
private lemma qp {n:ℕ} {a:aQ n} {c:Bool} (fixed:cR a = some c)
   (p q:Fin n) (x:Fin n → Bool) (past:List Bool):
   aA p q x past a = c:= by
 cases a with
 | mk src s => cases src <;> simp_all [cR,aA]
private lemma pn {n:ℕ} (p q:Fin n) (x:Fin n → Bool) (past extra:List Bool)
   (a:aQ n) (ok:bz past.length a):
   aA p q x (past ++ extra) a = aA p q x past a:= by
 cases a with
 | mk src s =>
   cases src with
   | source root => rfl
   | constant b => rfl
   | earlier j =>
     change j < past.length at ok
     simp only [aA,List.getD_append _ _ _ _ ok]
private lemma ki {n:ℕ} (p q:Fin n) (x:Fin n → Bool) (past:List Bool)
   (refs:List (aQ n)) (i:ℕ):
   aA p q x past (bO refs i) =
     (refs.map (aA p q x past)).getD i false:= by
 simp only [bO,List.getD_eq_getElem?_getD,List.getElem?_map]
 cases refs[i]? <;> rfl
private lemma pO {n:ℕ} (p q:Fin n) (x:Fin n → Bool)
   (l r:List (Join n)) (past:List Bool):
   run p q x (l ++ r) past = run p q x r (run p q x l past):= by
 simp [run,List.foldl_append]
private lemma qa {n:ℕ} (p q:Fin n) (x:Fin n → Bool)
   (gs:List (Join n)) (past:List Bool):
   ∃ suffix,run p q x gs past = past ++ suffix ∧ suffix.length = gs.length:= by
 induction gs generalizing past with
 | nil => exact ⟨[],by simp [run],rfl⟩
 | cons g gs ih =>
   obtain ⟨suffix,hrun,hlen⟩:= ih (past ++ [cE p q x past g])
   exact ⟨cE p q x past g::suffix,by simpa [run,List.append_assoc] using hrun,by simp [hlen]⟩
private lemma ll {n:ℕ}:
   ∀ (l r:List (Join n)) (base:ℕ),a0 base l →
     a0 (base + l.length) r → a0 base (l ++ r):= by
 intro l
 induction l with
 | nil =>
   intro r base _ right
   simpa using right
 | cons g gs ih =>
   intro r base left right
   change ee base g ∧ a0 (base + 1) gs at left
   change ee base g ∧ a0 (base + 1) (gs ++ r)
   refine ⟨left.1,ih r (base + 1) left.2 ?_⟩
   have e:base + 1 + gs.length = base + (g::gs).length:= by simp;omega
   rw [e]
   exact right
lemma uj {n:ℕ} {gs:List (Join n)} {base:ℕ}
   (ok:a0 base gs) (j:Fin gs.length):
   ee (base + j.val) (gs.get j):= by
 induction gs generalizing base with
 | nil => exact j.elim0
 | cons g gs ih =>
   change ee base g ∧ a0 (base + 1) gs at ok
   rcases j with ⟨j,hj⟩
   cases j with
   | zero => simpa using ok.1
   | succ j =>
     have small:j < gs.length:= by simpa using hj
     have got:= ih ok.2 ⟨j,small⟩
     have count:base + j.succ = base + 1 + j:= by omega
     change ee (base + j.succ) (gs.get ⟨j,small⟩)
     rw [count]
     exact got
private lemma mc {n:ℕ} {a b:aQ n}
   (origin:a.origin = b.origin) (sign:a.negated = b.negated):a = b:= by
 cases a
 cases b
 simp_all
private lemma jv {n:ℕ} (base:ℕ) (isOr c:Bool)
   (a b:aQ n) (aFixed:cR a = some c) (bOk:bz base b):
   ∃ (out:aQ n),bz base out ∧
     ∀ p q:Fin n,∀ (x:Fin n → Bool) (past:List Bool),
       aA p q x past out = dz isOr (aA p q x past a) (aA p q x past b):= by
 let out:= if c = isOr then en n isOr else b
 refine ⟨out,?_,?_⟩
 · dsimp [out]
   split
   · trivial
   · exact bOk
 · intro p q x past
   rw [qp aFixed p q x past]
   cases c <;> cases isOr <;> simp [out,dz]
private lemma nw {n:ℕ} (base:ℕ) (isOr:Bool) (a b:aQ n)
   (aOk:bz base a) (bOk:bz base b):
   ∃ (extra:List (Join n)) (out:aQ n),
     extra.length ≤ 1 ∧ a0 base extra ∧ bz (base + extra.length) out ∧
     ∀ p q:Fin n,∀ (x:Fin n → Bool) (past:List Bool),past.length = base →
       aA p q x (run p q x extra past) out =
         dz isOr (aA p q x past a) (aA p q x past b):= by
 cases aa:cR a with
 | some c =>
   obtain ⟨out,valid,ev⟩:= jv base isOr c a b aa bOk
   exact ⟨[],out,by simp,trivial,by simpa using valid,fun p q x past _ => ev p q x past⟩
 | none =>
   cases bb:cR b with
   | some c =>
     obtain ⟨out,valid,ev⟩:= jv base isOr c b a bb aOk
     refine ⟨[],out,by simp,trivial,by simpa using valid,?_⟩
     intro p q x past _
     exact (ev p q x past).trans (nt _ _ _)
   | none =>
     by_cases same:a.origin = b.origin
     · by_cases sameSign:a.negated = b.negated
       · have eq:= mc same sameSign
         subst b
         refine ⟨[],a,by simp,trivial,by simpa using aOk,?_⟩
         intro p q x past _
         cases isOr <;> simp [dz,run]
       · have opposite:b.negated = !(a.negated):= by
           cases sa:a.negated <;> cases sb:b.negated <;> simp_all
         have eq:b = cZ a:= mc same.symm opposite
         subst b
         refine ⟨[],en n isOr,by simp,trivial,trivial,?_⟩
         intro p q x past _
         cases h:aA p q x past a <;> cases isOr <;> simp [dz,run,h]
     · let gate:Join n:= ⟨isOr,a,b⟩
       let out:aQ n:= ⟨.earlier base,false⟩
       refine ⟨[gate],out,by simp,⟨⟨aOk,bOk,aa,bb,same⟩,trivial⟩,?_,?_⟩
       · change base < base + 1
         omega
       · intro p q x past len
         change (past ++ [cE p q x past gate]).getD base false = _
         rw [← len]
         simp [cE,gate,dz]
private lemma gu {n:ℕ} (base:ℕ) (refs:List (aQ n))
   (refOk: ∀ a ∈ refs,bz base a) (isOr:Bool) (args:List ℕ) (arity:args.length ≤ 2):
   ∃ (extra:List (Join n)) (out:aQ n),
     extra.length ≤ 1 ∧ a0 base extra ∧ bz (base + extra.length) out ∧
     ∀ p q:Fin n,∀ (x:Fin n → Bool) (past:List Bool),past.length = base →
       aA p q x (run p q x extra past) out =
         (if isOr then GateOp.or else GateOp.and).eval
           (args.map fun i => aA p q x past (bO refs i)):= by
 cases args with
 | nil =>
   refine ⟨[],en n (!isOr),by simp,trivial,trivial,?_⟩
   intro p q x past _
   cases isOr <;> rfl
 | cons i args =>
   cases args with
   | nil =>
     refine ⟨[],bO refs i,by simp,trivial,?_,?_⟩
     · simpa using cH refOk i
     · intro p q x past _
       cases isOr <;> simp [GateOp.eval,run]
   | cons j args =>
     cases args with
     | nil =>
       obtain ⟨extra,out,hlen,hnormal,valid,ev⟩:= nw base isOr
         (bO refs i) (bO refs j) (cH refOk i) (cH refOk j)
       refine ⟨extra,out,hlen,hnormal,valid,?_⟩
       intro p q x past len
       rw [ev p q x past len]
       cases isOr <;> simp [GateOp.eval,dz]
     | cons k rest =>
       simp only [List.length_cons] at arity
       omega
private lemma ny {n:ℕ} (base:ℕ) (refs:List (aQ n))
   (refOk: ∀ a ∈ refs,bz base a) (g:Gate)
   (legal:(g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2):
   ∃ (extra:List (Join n)) (out:aQ n),
     extra.length ≤ (if nonNot g then 1 else 0) ∧
     a0 base extra ∧ bz (base + extra.length) out ∧
     ∀ p q:Fin n,∀ (x:Fin n → Bool) (past:List Bool),past.length = base →
       aA p q x (run p q x extra past) out =
         g.op.eval (g.inputs.map fun i => aA p q x past (bO refs i)):= by
 rcases g with ⟨op,args⟩
 obtain ⟨bK,arity⟩:= legal
 change op = .and ∨ op = .or ∨ op = .not at bK
 rcases bK with rfl | rfl | rfl
 · exact gu base refs refOk false args arity
 · exact gu base refs refOk true args arity
 · cases args with
   | nil => exact ⟨[],en n true,by simp [nonNot],trivial,trivial,fun _ _ _ _ _ => rfl⟩
   | cons i args =>
     refine ⟨[],cZ (bO refs i),by simp [nonNot],trivial,?_,?_⟩
     · change bz base (bO refs i)
       exact cH refOk i
     · intro p q x past _
       exact valueComplement p q x past (bO refs i)
lemma kc {n:ℕ} (gs:List Gate)
   (legal: ∀ g ∈ gs,(g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
   (base:ℕ) (refs:List (aQ n)) (refOk: ∀ a ∈ refs,bz base a):
   ∃ (js:List (Join n)) (outRefs:List (aQ n)),
     js.length ≤ gs.countP nonNot ∧ a0 base js ∧
     (∀ a ∈ outRefs,bz (base + js.length) a) ∧
     ∀ p q:Fin n,∀ (x:Fin n → Bool) (past:List Bool),past.length = base →
       outRefs.map (aA p q x (run p q x js past)) =
         (⟨gs,0⟩:Circuit).wires (refs.map (aA p q x past)):= by
 induction gs generalizing base refs with
 | nil =>
   exact ⟨[],refs,by simp,trivial,by simpa using refOk,fun _ _ _ _ _ => rfl⟩
 | cons g gs ih =>
   obtain ⟨extra,nextRef,extraBound,norma,nextOk,ev⟩:=
     ny base refs refOk g (legal g List.mem_cons_self)
   have valid (a:aQ n) (member:a ∈ refs ++ [nextRef]):bz (base + extra.length) a:= by
     rcases List.mem_append.mp member with orig | added
     · exact ou (Nat.le_add_right _ _) (refOk a orig)
     · rw [List.mem_singleton.mp added]
       exact nextOk
   obtain ⟨tail,outRefs,tailBound,normb,outOk,tailEv⟩:=
     ih (fun h hh => legal h (List.mem_cons_of_mem _ hh)) (base + extra.length) (refs ++ [nextRef]) valid
   refine ⟨extra ++ tail,outRefs,?_,ll extra tail base norma normb,?_,?_⟩
   · have count:(g::gs).countP nonNot =
         gs.countP nonNot + (if nonNot g then 1 else 0):= by
       cases h:nonNot g <;> simp [List.countP_cons,h]
     rw [List.length_append,count]
     omega
   · simpa only [List.length_append,Nat.add_assoc] using outOk
   · intro p q x past pastLen
     obtain ⟨suffix,extension,suffixLen⟩:= qa p q x extra past
     have newLen:(run p q x extra past).length = base + extra.length:= by
       rw [extension,List.length_append,pastLen,suffixLen]
     have oldRefs:refs.map (aA p q x (run p q x extra past)) =
         refs.map (aA p q x past):= by
       apply List.map_congr_left
       intro a member
       rw [extension]
       exact pn p q x past suffix a (by rw [pastLen];exact refOk a member)
     have gateInput:g.inputs.map (fun i => aA p q x past (bO refs i)) =
         g.inputs.map (fun i => (refs.map (aA p q x past)).getD i false):=
       List.map_congr_left (fun i _ => ki p q x past refs i)
     rw [pO,tailEv p q x (run p q x extra past) newLen,List.map_append,oldRefs,
       List.map_singleton,ev p q x past pastLen,gateInput] <;> rfl
lemma lN {n:ℕ} (C:Circuit) (fan:FanInTwo C)
   (refs:List (aQ n)) (refOk: ∀ a ∈ refs,bz 0 a):
   ∃ (js:List (Join n)) (out:aQ n),
     js.length ≤ C.gates.countP nonNot ∧ a0 0 js ∧ bz js.length out ∧
     ∀ p q:Fin n,∀ x:Fin n → Bool,
       output p q x js out = C.eval (refs.map (aA p q x [])):= by
 have legal (g:Gate) (h:g ∈ C.gates):
     (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2:= by
   simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fan g h
 obtain ⟨js,outRefs,bound,normal,valid,ev⟩:= kc C.gates legal 0 refs refOk
 have validOut:bz js.length (bO outRefs C.output):= by
   exact cH (by simpa using valid) C.output
 refine ⟨js,bO outRefs C.output,bound,normal,validOut,?_⟩
 intro p q x
 unfold output
 rw [ki,ev p q x [] rfl] <;> rfl
private def hF (n:ℕ):List (aQ n):=
 List.ofFn (fun i:Fin n => nf i) ++ [qu n]
private lemma jr (n:ℕ): ∀ a ∈ hF n,bz 0 a:= by
 intro a ha
 change a ∈ (List.ofFn (fun i:Fin n => nf i)) ++ [qu n] at ha
 rcases List.mem_append.mp ha with listed | hint
 · obtain ⟨i,rfl⟩:= List.mem_ofFn.mp listed
   trivial
 · have eq:= List.mem_singleton.mp hint
   subst a
   trivial
private lemma ov {n:ℕ} (p q:Fin n) (x:Fin n → Bool):
   (hF n).map (aA p q x []) = List.ofFn x ++ [x p && x q]:= by
 unfold hF
 rw [List.map_append,List.map_singleton,List.map_ofFn] <;> rfl
def iH (n:ℕ) (k:Fin (n + 2)):List (aQ n):=
 hF n ++ [cZ (bO (hF n) k.val)]
private lemma my (n:ℕ) (k:Fin (n + 2)):
   ∀ a ∈ iH n k,bz 0 a:= by
 intro a ha
 change a ∈ hF n ++ [cZ (bO (hF n) k.val)] at ha
 rcases List.mem_append.mp ha with listed | last
 · exact jr n a listed
 · rw [List.mem_singleton.mp last]
   exact cH (jr n) k.val
private lemma m1 {n:ℕ} (k:Fin (n + 2)) (p q:Fin n) (x:Fin n → Bool):
   (iH n k).map (aA p q x []) =
     (List.ofFn x ++ [x p && x q]) ++ [!((List.ofFn x ++ [x p && x q]).getD k.val false)]:= by
 unfold iH
 rw [List.map_append,List.map_singleton,valueComplement,ki,ov]
lemma fk {n:ℕ} (C:Circuit) (fan:FanInTwo C) (k:Fin (n + 2)):
   ∃ (js:List (Join n)) (out:aQ n),
     js.length ≤ C.gates.countP nonNot ∧ a0 0 js ∧ bz js.length out ∧
     ∀ p q:Fin n,∀ x:Fin n → Bool,
       output p q x js out =
         C.eval ((List.ofFn x ++ [x p && x q]) ++ [!((List.ofFn x ++ [x p && x q]).getD k.val false)]):= by
 obtain ⟨js,out,bound,norm,valid,ev⟩:=
   lN C fan (iH n k) (my n k)
 refine ⟨js,out,bound,norm,valid,?_⟩
 intro p q x
 rw [ev,m1]
end PEqualNP.Outside.L_meta_4817.cq
namespace PEqualNP.Outside.L_meta_4817.bQ
open PEqualNP.Outside.L_meta_4817.eg
open PEqualNP.Outside.L_meta_4817.aJ (target)
private def bl:Fin 10 → Fin 10:= ![1,2,3,4,0,6,7,8,9,5]
private def bI:Fin 10 → Fin 10:= ![5,7,9,6,8,0,2,4,1,3]
private def dr:Fin 10 → Fin 10:= ![4,0,1,2,3,9,5,6,7,8]
private def eG:Fin 10 → Fin 10:= ![5,8,6,9,7,0,3,1,4,2]
private lemma hC (x:Fin 10 → Bool):
   target (fun i => x (bl i)) = target x:= by
 change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
     (x 0 && x 1) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
     (x 4 && x 9) || (x 0 && x 5) || (x 6 && x 8) || (x 8 && x 5) ||
     (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6)) = target x
 unfold target
 ac_rfl
private lemma gw (x:Fin 10 → Bool):
   target (fun i => x (bI i)) = target x:= by
 change ((x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) ||
     (x 8 && x 5) || (x 5 && x 0) || (x 7 && x 2) || (x 9 && x 4) ||
     (x 6 && x 1) || (x 8 && x 3) || (x 0 && x 4) || (x 4 && x 3) ||
     (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0)) = target x
 unfold target
 ac_rfl
private lemma oi:Function.LeftInverse dr bl:= by
 show ∀ i:Fin 10,dr (bl i) = i
 decide +kernel
private lemma ns:Function.RightInverse dr bl:= by
 show ∀ i:Fin 10,bl (dr i) = i
 decide +kernel
private lemma ri:Function.LeftInverse eG bI:= by
 show ∀ i:Fin 10,eG (bI i) = i
 decide +kernel
private lemma qm:Function.RightInverse eG bI:= by
 show ∀ i:Fin 10,bI (eG i) = i
 decide +kernel
private def bn (v:Fin 10):ℕ:=
 (5 - (if v.val < 5 then v.val else (bI v).val)) % 5
def cG (v i:Fin 10):Fin 10:=
 (bl^[bn v]) (if v.val < 5 then i else bI i)
def gx (v i:Fin 10):Fin 10:=
 let w:= (dr^[bn v]) i
 if v.val < 5 then w else eG w
lemma hR: ∀ v:Fin 10,cG v v = 0:= by
 decide +kernel
lemma mv (v i:Fin 10):gx v (cG v i) = i:= by
 by_cases h:v.val < 5
 · simpa only [gx,cG,if_pos h] using (oi.iterate (bn v)) i
 · have e:= (oi.iterate (bn v)) (bI i)
   simp only [gx,cG,if_neg h]
   rw [e]
   exact ri i
lemma sp (v i:Fin 10):cG v (gx v i) = i:= by
 by_cases h:v.val < 5
 · simpa only [cG,gx,if_pos h] using (ns.iterate (bn v)) i
 · simp only [cG,gx,if_neg h]
   rw [qm ((dr^[bn v]) i)]
   exact (ns.iterate (bn v)) i
lemma ui (v:Fin 10):gx v 0 = v:= by
 have e:= mv v v
 rwa [hR v] at e
private lemma cc (n:ℕ) (x:Fin 10 → Bool):
   target (fun i => x ((bl^[n]) i)) = target x:= by
 induction n with
 | zero => rfl
 | succ n ih =>
   simp only [Function.iterate_succ_apply]
   exact (hC (fun i => x ((bl^[n]) i))).trans ih
lemma h5 (v:Fin 10) (x:Fin 10 → Bool):
   target (fun i => x (cG v i)) = target x:= by
 by_cases h:v.val < 5
 · simpa only [cG,if_pos h] using cc (bn v) x
 · simpa only [cG,if_neg h] using
     (gw (fun i => x ((bl^[bn v]) i))).trans
       (cc (bn v) x)
def restrictedAll (v:Fin 10) (r:Row) (i:Fin 10):Bool:=
 cz r (cG v i)
lemma restrictedAll_self (v:Fin 10) (r:Row):restrictedAll v r v = false:= by
 change cz r (cG v v) = false
 rw [hR] <;> rfl
lemma allCofactorCorrect (v:Fin 10) (r:Row):
   target (restrictedAll v r) = aF graph r:=
 (h5 v (cz r)).trans (ff r)
def pU (v:Fin 10):List (Wire Row):=
 List.ofFn (fun i:Fin 10 => fun r => restrictedAll v r i)
lemma rawSupply (v:Fin 10):co true original (pU v):= by
 intro f h
 obtain ⟨i,rfl⟩:= List.mem_ofFn.mp h
 exact zzzy (cG v i)
def kd (v:Fin 10):Wire Row:=
 fun r => restrictedAll v r 0 && restrictedAll v r 2
lemma hintZero (v:Fin 10) (endpoint:v = 0 ∨ v = 2):
   kd v = fun _ => false:= by
 funext r
 rcases endpoint with rfl | rfl
 · simp only [kd,restrictedAll_self,Bool.false_and]
 · simp only [kd,restrictedAll_self,Bool.and_false]
end PEqualNP.Outside.L_meta_4817.bQ
namespace PEqualNP.Outside.L_meta_4817.cq
open PEqualNP.Outside.L_meta_4817.aJ (target)
open PEqualNP.Outside.L_meta_4817.ch
lemma oW (gs:List (Join 10)) (out:aQ 10)
   (computes: ∀ x,output 0 2 x gs out = target x):
   ∃ j,out.origin = .earlier j:= by
 cases kind:out.origin with
 | earlier j => exact ⟨j,rfl⟩
 | constant b =>
   obtain ⟨x,diff⟩:= target_not_constant (if out.negated then !b else b)
   apply (diff ?_).elim
   simpa only [output,aA,kind] using (computes x).symm
 | source src =>
   cases src with
   | literal u =>
     obtain ⟨x,diff⟩:= target_not_signed_primary u out.negated
     apply (diff ?_).elim
     simpa only [output,aA,kind,bF] using (computes x).symm
   | hint =>
     obtain ⟨x,diff⟩:= target_not_signed_hint out.negated
     apply (diff ?_).elim
     simpa only [output,aA,kind,bF] using (computes x).symm
private lemma hK (gs:List (Join 10)) (out:aQ 10)
   (outGate: ∃ j,out.origin = .earlier j)
   (computes: ∀ x,output 0 2 x gs out = target x)
   (v other:Fin 10) (opposite:(v = 0 ∧ other = 2) ∨ (v = 2 ∧ other = 0)):
   ∃ j:Fin gs.length,reads (gs.get j) (.literal v):= by
 have ne:v ≠ other:= by
   rcases opposite with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
 obtain ⟨x,y,_,_,xc,yc,agree,tx,ty⟩:= dependence_at_value v other ne false
 apply lJ 0 2 gs out outGate (.literal v) x y
 · intro s not
   cases s with
   | literal i => exact agree i (fun e => not (congrArg iu.literal e))
   | hint =>
     rcases opposite with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [bF,xc,yc]
 · rw [computes,computes,tx,ty]
   decide
private lemma oD (g:Join 10) (normal:ee 0 g)
   (noHint: ¬ reads g .hint):
   ∃ p q:Fin 10,p ≠ q ∧ g.left.origin = .source (.literal p) ∧
     g.right.origin = .source (.literal q):= by
 have origin (a:aQ 10) (v:bz 0 a) (free:cR a = none)
     (no:a.origin ≠ .source .hint): ∃ p,a.origin = .source (.literal p):= by
   cases e:a.origin with
   | earlier j => simp [bz,e] at v
   | constant b => simp [cR,e] at free
   | source src =>
     cases src with
     | hint => exact (no e).elim
     | literal p => exact ⟨p,rfl⟩
 obtain ⟨p,hp⟩:= origin g.left normal.1 normal.2.2.1 (fun e => noHint (Or.inl e))
 obtain ⟨q,hq⟩:= origin g.right normal.2.1 normal.2.2.2.1 (fun e => noHint (Or.inr e))
 refine ⟨p,q,?_,hp,hq⟩
 intro eq
 subst q
 exact normal.2.2.2.2 (hp.trans hq.symm)
private lemma lE (gs:List (Join 10)) (out:aQ 10)
   (normal:a0 0 gs) (valid:bz gs.length out)
   (outGate: ∃ j,out.origin = .earlier j)
   (computes: ∀ x,output 0 2 x gs out = target x)
   (noHint: ∀ g ∈ gs,¬ reads g .hint):
   ∃ v:Fin 10,∃ i j:Fin gs.length,i ≠ j ∧
     reads (gs.get i) (.literal v) ∧ reads (gs.get j) (.literal v):= by
 cases gs with
 | nil =>
   obtain ⟨j,eq⟩:= outGate
   simp [bz,eq] at valid
 | cons g gs =>
   obtain ⟨u,v,ne,hu,hv⟩:= oD g normal.1 (noHint g List.mem_cons_self)
   let b:Bool:= if g.isOr then !g.right.negated else g.right.negated
   obtain ⟨x,y,_,_,xb,yb,agree,tx,ty⟩:= dependence_at_value u v ne b
   have firstEq:cE 0 2 x [] g = cE 0 2 y [] g:= by
     unfold cE
     cases hOr:g.isOr <;> cases hsign:g.right.negated <;>
       simp [aA,hv,bF,xb,yb,b,hOr,hsign]
   have again: ∃ h ∈ gs,reads h (.literal u):= by
     by_contra no
     have same (h:Join 10) (hg:h ∈ gs) (s:iu 10) (hs:reads h s):
         bF 0 2 x s = bF 0 2 y s:= by
       cases s with
       | literal z =>
         apply agree z
         rintro rfl
         exact no ⟨h,hg,hs⟩
       | hint => exact (noHint h (List.mem_cons_of_mem _ hg) hs).elim
     have runEq:run 0 2 x (g::gs) [] = run 0 2 y (g::gs) []:= by
       change run 0 2 x gs [cE 0 2 x [] g] = run 0 2 y gs [cE 0 2 y [] g]
       rw [firstEq]
       exact nZ 0 2 x y gs same _
     have outputEq:output 0 2 x (g::gs) out = output 0 2 y (g::gs) out:= by
       unfold output
       rw [runEq]
       obtain ⟨j,e⟩:= outGate
       apply eX
       intro src hs
       rw [e] at hs
       cases hs
     rw [computes,computes,tx,ty] at outputEq
     exact Bool.false_ne_true outputEq
   obtain ⟨h,hh,uses⟩:= again
   obtain ⟨label,e⟩:= List.mem_iff_get.mp hh
   let idx:Fin (g::gs).length:= ⟨label.val + 1,by simp⟩
   refine ⟨u,⟨0,by simp⟩,idx,?_,Or.inl hu,?_⟩
   · intro eq
     have val:= congrArg Fin.val eq
     change 0 = label.val + 1 at val
     omega
   · have same:(g::gs).get idx = gs.get label:= rfl
     simpa only [same,e] using uses
lemma iP (gs:List (Join 10)) (out:aQ 10)
   (normal:a0 0 gs) (valid:bz gs.length out)
   (computes: ∀ x,output 0 2 x gs out = target x):
   (∃ j,out.origin = .earlier j) ∧
   ∃ v:Fin 10,((v = 0 ∨ v = 2) ∨ ∀ g ∈ gs,¬ reads g .hint) ∧
     ∃ i j:Fin gs.length,i ≠ j ∧
       (reads (gs.get i) .hint ∨ reads (gs.get i) (.literal v)) ∧
       (reads (gs.get j) .hint ∨ reads (gs.get j) (.literal v)):= by
 classical
 have outGate:= oW gs out computes
 refine ⟨outGate,?_⟩
 by_cases hasHint: ∃ j:Fin gs.length,reads (gs.get j) .hint
 · obtain ⟨v,isEndpoint,i,j,ne,useI,useJ⟩:= ix gs 0 2 (by decide)
     hasHint (hK gs out outGate computes 0 2 (Or.inl ⟨rfl,rfl⟩))
     (hK gs out outGate computes 2 0 (Or.inr ⟨rfl,rfl⟩))
   exact ⟨v,Or.inl isEndpoint,i,j,ne,useI,useJ⟩
 · have noHint (g:Join 10) (hg:g ∈ gs): ¬ reads g .hint:= by
     intro uses
     obtain ⟨j,eq⟩:= List.mem_iff_get.mp hg
     exact hasHint ⟨j,by simpa only [eq] using uses⟩
   obtain ⟨v,i,j,ne,useI,useJ⟩:= lE gs out normal valid outGate computes noHint
   exact ⟨v,Or.inr noHint,i,j,ne,Or.inr useI,Or.inr useJ⟩
end PEqualNP.Outside.L_meta_4817.cq
namespace PEqualNP.Outside.L_meta_4817.cq
open PEqualNP.Outside.L_meta_4817.eg
 (Wire aS ad Reach co inv bH ik cC da Row aF graph nY)
def bR {n:ℕ} (v:Fin n) (g:Join n):Bool:=
 @decide (reads g .hint ∨ reads g (.literal v)) (by unfold reads;infer_instance)
lemma dv {n:ℕ} (v:Fin n) (g:Join n):
   bR v g = true ↔ reads g .hint ∨ reads g (.literal v):= by
 simp only [bR,decide_eq_true_eq,iff_self]
private lemma eb {α:Type} (p:α → Bool):
   ∀ l:List α,l.countP p =
     (Finset.univ.filter fun i:Fin l.length => p (l.get i) = true).card
 | [] => by simp
 | a::l => by
   have ih:= eb p l
   have split:(Finset.univ.filter fun i:Fin (a::l).length => p ((a::l).get i) = true).card =
       (if p a = true then 1 else 0) +
         (Finset.univ.filter fun i:Fin l.length => p (l.get i) = true).card:= by
     rw [show (Finset.univ.filter fun i:Fin (a::l).length => p ((a::l).get i) = true).card =
         (Finset.univ.filter fun i:Fin (l.length + 1) => p ((a::l).get i) = true).card from rfl,
       Fin.card_filter_univ_succ (n:= l.length) (fun i:Fin (l.length + 1) => p ((a::l).get i) = true)]
     by_cases h:p a = true
     · simp [h,Function.comp_def,add_comm]
     · simp [h,Function.comp_def]
   rw [split,← ih,List.countP_cons,add_comm]
lemma kn {n:ℕ} (v:Fin n) (gs:List (Join n)) (i j:Fin gs.length)
   (ne:i ≠ j) (hi:reads (gs.get i) .hint ∨ reads (gs.get i) (.literal v))
   (hj:reads (gs.get j) .hint ∨ reads (gs.get j) (.literal v)):
   2 ≤ gs.countP (bR v):= by
 rw [eb]
 exact Finset.one_lt_card.mpr
   ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(dv _ _).mpr hi⟩,
     j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(dv _ _).mpr hj⟩,ne⟩
private def io {n:ℕ} {R:Type} (p q:Fin n) (xs:R → Fin n → Bool)
   (s:iu n):Wire R:=
 fun r => bF p q (xs r) s
private def gq {n:ℕ} {R:Type} (p q:Fin n)
   (xs:R → Fin n → Bool) (cols:List (Wire R)):sy n → Wire R
 | .source s => io p q xs s
 | .earlier j => cols.getD j (fun _ => false)
 | .constant b => fun _ => b
private def ft {R:Type} (negated:Bool) (w:Wire R):Wire R:=
 if negated then inv w else w
private def bt {n:ℕ} {R:Type} (p q:Fin n)
   (xs:R → Fin n → Bool) (cols:List (Wire R)) (a:aQ n):Wire R:=
 ft a.negated (gq p q xs cols a.origin)
private def hE {n:ℕ} {R:Type} (p q:Fin n)
   (xs:R → Fin n → Bool) (cols:List (Wire R)) (g:Join n):Wire R:=
 bH g.isOr (bt p q xs cols g.left) (bt p q xs cols g.right)
private def e7 {n:ℕ} {R:Type} (p q:Fin n) (xs:R → Fin n → Bool):
   List (Join n) → List (Wire R) → List (Wire R)
 | [],cols => cols
 | g::gs,cols => e7 p q xs gs (cols ++ [hE p q xs cols g])
private lemma eQ {n:ℕ} {R:Type} (p q:Fin n)
   (xs:R → Fin n → Bool) (cols:List (Wire R)) (a:aQ n) (r:R):
   bt p q xs cols a r =
     aA p q (xs r) (cols.map (fun f => f r)) a:= by
 rcases a with ⟨origin,sign⟩
 cases origin with
 | source s => cases sign <;> rfl
 | constant b => cases sign <;> rfl
 | earlier j =>
   have get:(cols.map (fun f => f r)).getD j false = (cols.getD j (fun _ => false)) r:=
     List.getD_map (l:= cols) (n:= j) (d:= fun _:R => false) (fun f:Wire R => f r)
   cases sign
   · exact get.symm
   · exact congrArg (fun b:Bool => !b) get.symm
private lemma ec {n:ℕ} {R:Type} (p q:Fin n)
   (xs:R → Fin n → Bool) (cols:List (Wire R)) (a:aQ n):
   bt p q xs cols a =
     fun r => aA p q (xs r) (cols.map (fun f => f r)) a:= by
 funext r
 exact eQ p q xs cols a r
private lemma nx {n:ℕ} {R:Type} (p q:Fin n)
   (xs:R → Fin n → Bool) (cols:List (Wire R)) (g:Join n) (r:R):
   hE p q xs cols g r =
     cE p q (xs r) (cols.map (fun f => f r)) g:= by
 cases h:g.isOr <;> simp [hE,bH,cE,h,eQ]
private lemma mY {n:ℕ} {R:Type} (p q:Fin n)
   (xs:R → Fin n → Bool) (gs:List (Join n)) (cols:List (Wire R)) (r:R):
   (e7 p q xs gs cols).map (fun f => f r) =
     run p q (xs r) gs (cols.map (fun f => f r)):= by
 induction gs generalizing cols with
 | nil => rfl
 | cons g gs ih =>
   change (e7 p q xs gs (cols ++ [hE p q xs cols g])).map (fun f => f r) =
     run p q (xs r) gs (cols.map (fun f => f r) ++
       [cE p q (xs r) (cols.map (fun f => f r)) g])
   rw [ih,List.map_append,List.map_singleton,nx]
private lemma ng {R:Type} {bank cols:List (Wire R)}
   (past:co true bank cols) (j:ℕ):
   ad true bank (cols.getD j (fun _ => false)):= by
 rw [List.getD_eq_getElem?_getD]
 cases h:cols[j]? with
 | none => exact Or.inr (Or.inl ⟨false,rfl⟩)
 | some f => exact past f (List.mem_of_getElem? h)
private lemma eN {n:ℕ} {R:Type} (p q:Fin n)
   (xs:R → Fin n → Bool) {bank cols:List (Wire R)} (past:co true bank cols)
   (a:aQ n)
   (ready: ∀ s,a.origin = .source s → ad true bank (io p q xs s)):
   ad true bank (bt p q xs cols a):= by
 have unsigned:ad true bank (gq p q xs cols a.origin):= by
   cases h:a.origin with
   | source s => exact ready s h
   | earlier j => exact ng past j
   | constant c => exact Or.inr (Or.inl ⟨c,rfl⟩)
 cases h:a.negated
 · simpa only [bt,ft,h,Bool.false_eq_true,if_false] using unsigned
 · simpa [bt,ft,h] using ik rfl unsigned
private lemma fx {R:Type} {bank cols:List (Wire R)} {w:Wire R}
   (old:co true bank cols) (new:ad true bank w):
   co true bank (cols ++ [w]):= by
 intro f h
 rcases List.mem_append.mp h with h | h
 · exact old f h
 · rw [List.mem_singleton.mp h]
   exact new
private lemma jh {n:ℕ} {R:Type} (p q v:Fin n)
   (xs:R → Fin n → Bool) (gs:List (Join n))
   {roots bank cols:List (Wire R)} {used:ℕ}
   (reach:Reach true roots used bank) (past:co true bank cols)
   (ready: ∀ g ∈ gs,∀ s,reads g s → ad true bank (io p q xs s))
   (fixed: ∀ g ∈ gs,bR v g = true → ∀ prev:List (Wire R),
     aS (bt p q xs prev g.left) ∨ aS (bt p q xs prev g.right)):
   ∃ spent next,Reach true roots spent next ∧
     co true next (e7 p q xs gs cols) ∧
     spent + gs.countP (bR v) ≤ used + gs.length:= by
 induction gs generalizing used bank cols with
 | nil => exact ⟨used,bank,reach,past,by simp⟩
 | cons g gs ih =>
   have left:= eN p q xs past g.left (fun s h => ready g List.mem_cons_self s (Or.inl h))
   have right:= eN p q xs past g.right (fun s h => ready g List.mem_cons_self s (Or.inr h))
   let result:= hE p q xs cols g
   have oR: ∃ k extended,Reach true roots k extended ∧
       co true extended (cols ++ [result]) ∧
       (∀ w,ad true bank w → ad true extended w) ∧
       k + (if bR v g then 1 else 0) ≤ used + 1:= by
     by_cases skip:bR v g = true
     · have h:= fixed g List.mem_cons_self skip cols
       have value:ad true bank result:= da g.isOr h left right
       exact ⟨used,bank,reach,fx past value,fun _ h => h,by simp [skip]⟩
     · have value:ad true (result::bank) result:= Or.inl List.mem_cons_self
       refine ⟨used + 1,result::bank,Reach.two g.isOr reach left right,
         fx (fun w h => cC result (past w h)) value,
         fun _ h => cC result h,?_⟩
       simp [skip]
   obtain ⟨k,extended,advanced,past',transfer,paid⟩:= oR
   obtain ⟨spent,next,reach',supplied,count⟩:= ih advanced past'
     (fun j hj s hjr => transfer _ (ready j (List.mem_cons_of_mem _ hj) s hjr))
     (fun j hj => fixed j (List.mem_cons_of_mem _ hj))
   refine ⟨spent,next,reach',supplied,?_⟩
   simp only [List.countP_cons,List.length_cons]
   cases h:bR v g <;> simp [h] at paid ⊢ <;> omega
private lemma fs (v:Fin 10) (cols:List (Wire Row)) (a:aQ 10)
   (h:a.origin = .source (.literal v)):
   aS (bt 0 2 (bQ.restrictedAll v) cols a):= by
 refine ⟨a.negated,?_⟩
 funext r
 cases hs:a.negated <;> simp [bt,gq,ft,io,bF,
   inv,h,hs,bQ.restrictedAll_self]
private lemma iS (v:Fin 10) (gs:List (Join 10))
   (whereHint:(v = 0 ∨ v = 2) ∨ ∀ g ∈ gs,¬ reads g .hint)
   (g:Join 10) (member:g ∈ gs) (discounted:bR v g = true)
   (cols:List (Wire Row)):
   aS (bt 0 2 (bQ.restrictedAll v) cols g.left) ∨
   aS (bt 0 2 (bQ.restrictedAll v) cols g.right):= by
 have read:= (dv v g).mp discounted
 rcases whereHint with endpoint | unused
 · rw [ec,ec]
   exact hY 0 2 v endpoint (bQ.restrictedAll v)
     (bQ.restrictedAll_self v) (fun r => cols.map (fun f => f r)) g read
 · rcases read.resolve_left (unused g member) with left | right
   · exact Or.inl (fs v cols g.left left)
   · exact Or.inr (fs v cols g.right right)
private lemma kg (v:Fin 10) (gs:List (Join 10))
   (whereHint:(v = 0 ∨ v = 2) ∨ ∀ g ∈ gs,¬ reads g .hint)
   (g:Join 10) (member:g ∈ gs) (s:iu 10) (read:reads g s):
   ad true bQ.original (io 0 2 (bQ.restrictedAll v) s):= by
 cases s with
 | literal i =>
   change ad true bQ.original (fun r => bQ.restrictedAll v r i)
   exact bQ.rawSupply v _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
 | hint =>
   rcases whereHint with endpoint | unused
   · exact Or.inr (Or.inl ⟨false,bQ.hintZero v endpoint⟩)
   · exact (unused g member read).elim
lemma ky (gs:List (Join 10)) (out:aQ 10) (v:Fin 10)
   (outGate: ∃ j,out.origin = .earlier j)
   (whereHint:(v = 0 ∨ v = 2) ∨ ∀ g ∈ gs,¬ reads g .hint)
   (correct: ∀ x:Fin 10 → Bool,output 0 2 x gs out = aJ.target x):
   15 + gs.countP (bR v) ≤ gs.length:= by
 obtain ⟨spent,bank,reach,available,count⟩:=
   jh 0 2 v (bQ.restrictedAll v) gs (cols:= []) Reach.start
     (by intro w h;simp at h)
     (kg v gs whereHint) (iS v gs whereHint)
 have ready:= eN 0 2 (bQ.restrictedAll v) available out (by
   intro s impossible
   obtain ⟨j,atGate⟩:= outGate
   rw [atGate] at impossible
   cases impossible)
 have corr:bt 0 2 (bQ.restrictedAll v)
     (e7 0 2 (bQ.restrictedAll v) gs []) out = aF graph:= by
   funext r
   rw [eQ,mY]
   exact (correct (bQ.restrictedAll v r)).trans (bQ.allCofactorCorrect v r)
 rw [corr] at ready
 have floor:= nY spent bank reach ready
 omega
end PEqualNP.Outside.L_meta_4817.cq
namespace PEqualNP.Outside.L_meta_4817
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4817.cq
lemma eT (C:Circuit) (k:Fin 12) (fan:FanInTwo C)
   (computes: ∀ x,C.eval (aJ.inputs k x) = aJ.target x):
   17 ≤ C.gates.countP aJ.paid:= by
 obtain ⟨js,out,cap,normal,valid,eval⟩:= fk (n:= 10) C fan k
 have fits (x:Fin 10 → Bool):output 0 2 x js out = aJ.target x:= by
   exact (eval 0 2 x).trans (computes x)
 obtain ⟨j,⟨v,hint,i,l,ne,hi,hl⟩⟩:= iP js out normal valid fits
 have floor:= ky js out v j hint fits
 have saving:= kn v js i l ne hi hl
 change js.length ≤ C.gates.countP aJ.paid at cap
 omega
lemma lT (C:Circuit) (k:Fin 12) (fan:FanInTwo C)
   (size:C.size ≤ 17) (someNot:1 ≤ PEqualNP.NotBracket.notCount C):
   ∃ x:Fin 10 → Bool,C.eval (aJ.inputs k x) ≠ aJ.target x:= by
 by_contra noMismatch
 have eq (x:Fin 10 → Bool):C.eval (aJ.inputs k x) = aJ.target x:= by
   by_contra differs
   exact noMismatch ⟨x,differs⟩
 have paid:= eT C k fan eq
 have count:= aJ.accounting C
 omega
end PEqualNP.Outside.L_meta_4817
theorem PEqualNP.Outside.L_meta_4817:∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5:= by
 classical
 intro C k fan bound
 by_cases none: ∀ g ∈ C.gates,g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not
 · simpa only [PEqualNP.Outside.L_meta_4817.aJ.inputs,
     PEqualNP.Outside.L_meta_4817.aJ.base,
     PEqualNP.Outside.L_meta_4817.aJ.target] using
     PEqualNP.Outside.L_meta_4817.monotoneMismatch C k fan none bound
 · push_neg at none
   obtain ⟨g,member,op⟩:= none
   have hasNot:1 ≤ PEqualNP.NotBracket.notCount C:= by
     unfold PEqualNP.NotBracket.notCount
     apply List.length_pos_iff.mpr
     apply List.ne_nil_of_mem (a := g)
     simp [List.mem_filter,member,op]
   simpa only [PEqualNP.Outside.L_meta_4817.aJ.inputs,
     PEqualNP.Outside.L_meta_4817.aJ.base,
     PEqualNP.Outside.L_meta_4817.aJ.target] using
     PEqualNP.Outside.L_meta_4817.lT C k fan bound hasNot
