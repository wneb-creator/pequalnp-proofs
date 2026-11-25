import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1890.BoundsNine
open PEqualNP.CircuitLowerBounds
abbrev Sig:= BitVec 512
def zero:Sig:= 0
def one:Sig:= BitVec.allOnes 512
def neg (a:Sig):Sig:= ~~~a
def bin (d:Nat) (a b:Sig):Sig:=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def qcQ (a:Sig):Prop:= a ≠ zero ∧ a ≠ one
def q0N (u:Bool) (d:Nat):Prop:= d<2 ∨ (u=true ∧ d<4)
theorem q0Q {u d} (h:q0N u d):d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3):= by
  rcases h with h | ⟨h,j⟩
  · omega
  · have:d=0 ∨ d=1 ∨ d=2 ∨ d=3:= by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
def Live (u:Bool) (target:Sig):Nat → Finset Sig → Prop
  | 0,S=> S={target} ∧ qcQ target
  | k+1,S=> ∃ (U:Finset Sig) (a b:Sig) (d:Nat),q0N u d ∧ S=insert a (insert b U) ∧
      qcQ a ∧ qcQ b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target:Sig} (hp:qcQ target):Live u target 0 {target}:= ⟨rfl,hp⟩
theorem Live.binary {u} {target:Sig} {k:Nat} {U:Finset Sig} {a b:Sig} {d:Nat} (hd:q0N u d)
    (ha:qcQ a) (hb:qcQ b) (hab:a ≠ b)
    (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live u target k (insert (bin d a b) U)):
    Live u target (k+1) (insert a (insert b U)):=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target:Sig} {motive:∀ (k:Nat) (S:Finset Sig),Live u target k S → Prop}
    (stop:∀ (hp:qcQ target),motive 0 {target} (Live.stop hp))
    (binary:∀ {k:Nat} {U:Finset Sig} {a b:Sig} {d:Nat} (hd:q0N u d)
      (ha:qcQ a) (hb:qcQ b) (hab:a ≠ b)
      (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k:Nat} {S:Finset Sig} (h:Live u target k S):motive k S h:= by
  induction k generalizing S with
  | zero=>
    obtain ⟨rfl,hp⟩:= h
    exact stop hp
  | succ k ih=>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩:= h
    exact binary hd ha hb hab hf tail (ih tail)
private lemma q95 {u target k S} (h:Live u target k S):∀ a ∈ S,qcQ a:= by
  induction h using Live.ind with
  | stop hp=> simpa using hp
  | binary hd ha hb hab hf _ ih=>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h=> ih a (Finset.mem_insert_of_mem h)⟩
def bit (i:Fin 512) (a:Sig):Bool:= a.getLsbD i.val
private lemma q1v (i):bit i zero=false:= by simp [bit,zero]
private lemma q1p (i):bit i one=true:= by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma q1o (i) (a:Sig):bit i (neg a)= !(bit i a):= by simp [bit,neg,i.isLt]
private lemma q1i (i d) (a b:Sig):bit i (bin d a b)=
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b):= by
  unfold bin
  split_ifs <;> simp [bit]
theorem q1j {a b:Sig} (h:∀ i,bit i a=bit i b):a=b:=
  BitVec.eq_of_getLsbD_eq fun j hj=> h ⟨j,hj⟩
def nrm (u:Bool) (a:Sig):Sig:= if u && bit 0 a then neg a else a
theorem qbn (a:Sig):nrm false a=a:= rfl
theorem qbm (a:Sig):bit 0 (nrm true a)=false:= by
  cases h:bit 0 a <;> simp [nrm,h,q1o]
theorem qbo {u} {a:Sig} (h:bit 0 a=false):nrm u a=a:= by simp [nrm,h]
theorem qbc (a:Sig):neg (neg a)=a:= by simp [neg]
theorem qbq (a:Sig):nrm true (neg a)=nrm true a:= by
  cases h:bit 0 a <;> simp [nrm,h,q1o,qbc]
theorem qcT {a:Sig} (h:qcQ (neg a)):qcQ a:= by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem qcU {u} {a:Sig} (h:qcQ (nrm u a)):qcQ a:= by
  unfold nrm at h
  split at h
  · exact qcT h
  · exact h
def qcM (d:Bool) (a b:Sig):= if d then a ||| b else a &&& b
theorem q1q (i) (d:Bool) (a b:Sig):bit i (qcM d a b)=
    (if d then bit i a || bit i b else bit i a && bit i b):= by cases d <;> simp [qcM,bit]
theorem qbr (d:Bool) (a b:Sig):
    ∃ e,e<4 ∧ nrm true (qcM d a b)=bin e (nrm true a) (nrm true b):= by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply q1j
    intro i
    cases d <;> cases ha:bit 0 a <;> cases hb:bit 0 b <;>
      simp only [nrm,q1q,ha,hb,q1i,q1o,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx:bit i a <;> cases hy:bit i b <;> simp [hx,hy,q1o,q1q]
def gv (w:List Sig) (g:Gate):Sig:=
  let xs:= g.inputs.map (fun i=> w.getD i zero)
  match g.op with
  | .and=> xs.foldr (qcM false) one
  | .or=> xs.foldr (qcM true) zero
  | .not=> neg (xs.headD zero)
  | _=> zero
def q36 (gs:List Gate) (w:List Sig):List Sig:=
  gs.foldl (fun l g=> l ++ [gv l g]) w
def qdd (w:List Sig) (v:Sig):Prop:= v ∈ w ∨ ¬qcQ v
def Repr (u:Bool) (w:List Sig) (v:Sig):Prop:= qdd w (nrm u v)
private lemma q1f (a:Sig):
    bin 0 a one=a ∧ bin 1 a zero=a ∧
    bin 0 a zero=zero ∧ bin 1 a one=one ∧
    bin 0 a a=a ∧ bin 1 a a=a ∧ bin 2 a a=zero ∧ bin 3 a a=zero ∧ bin 2 a zero=a ∧
    bin 3 zero a=a ∧ bin 2 zero a=zero ∧ bin 3 a zero=zero ∧ bin 0 zero a=zero ∧ bin 1 zero a=a ∧
    bin 0 one a=a ∧ bin 1 one a=one:= by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply q1j <;> intro i <;>
    simp [q1i,q1v,q1p]
private lemma qbb:neg zero=one ∧ neg one=zero:= by simp [neg,zero,one]
private lemma qbE {w:List Sig} {a:Sig} (h:qdd w a):
    a=zero ∨ a=one ∨ a ∈ w ∧ qcQ a:= by
  by_cases hz:a=zero
  · exact Or.inl hz
  by_cases ho:a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x=> x ⟨hz,ho⟩),hz,ho⟩)
def qgT (u:Bool) (w:List Sig) (z:Sig):Prop:=
  ∃ d a b,q0N u d ∧ a ∈ w ∧ b ∈ w ∧ qcQ a ∧ qcQ b ∧ a ≠ b ∧ z=bin d a b
private lemma q1g {u w a b} (d:Nat) (hd:q0N u d) (ha:qdd w a) (hb:qdd w b)
    (no:u=true → a ≠ one ∧ b ≠ one):
    qdd w (bin d a b) ∨ qgT u w (bin d a b):= by
  have rz:qdd w zero:= Or.inr (fun h=> h.1 rfl)
  have ro:qdd w one:= Or.inr (fun h=> h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩:= q1f a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩:= q1f b
  by_cases he:a=b
  · subst b
    left
    rcases q0Q hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases qbE ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases q0Q hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases q0Q hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases qbE hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases q0Q hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases q0Q hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
theorem qbl (a:Sig):nrm true a ≠ one:= by
  intro h
  have:= qbm a
  rw [h,q1p] at this
  exact Bool.noConfusion this
theorem qcN {u w a b} (d:Bool) (ha:Repr u w a) (hb:Repr u w b):
    Repr u w (qcM d a b) ∨ qgT u w (nrm u (qcM d a b)):= by
  cases u
  · have e:qcM d a b=bin (if d then 1 else 0) a b:= by cases d <;> rfl
    have h:= q1g (u:= false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [qbn] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩:= qbr d a b
    unfold Repr
    rw [eq]
    exact q1g e (Or.inr ⟨rfl,he⟩) ha hb (fun _=> ⟨qbl a,qbl b⟩)
theorem qdb {u w} {v:Sig} (h:v=zero ∨ v=one):Repr u w v:= by
  refine Or.inr fun hp=> ?_
  have:= qcU hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma q5B {u} (w:List Sig) (i:Nat):Repr u (w.map (nrm u)) (w.getD i zero):= by
  simp only [List.getD_eq_getElem?_getD]
  cases h:w[i]? with
  | none=> exact qdb (Or.inl rfl)
  | some a=> exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem qdc {w a} (h:Repr true w a):Repr true w (neg a):= by
  unfold Repr
  rwa [qbq]
def q75 (g:Gate):Bool:= match g.op with
  | .not=> true
  | _=> false
private lemma q5i (u:Bool) (w:List Sig) (g:Gate)
    (h:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2)
    (mono:u=false → q75 g=false):
    Repr u (w.map (nrm u)) (gv w g) ∨ (q75 g=false ∧ qgT u (w.map (nrm u)) (nrm u (gv w g))):= by
  obtain ⟨o,l⟩:= g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩:= h
  have prim (d:Bool):Repr u (w.map (nrm u)) ((l.map (fun i=> w.getD i zero)).foldr (qcM d) (if d then zero else one)) ∨
      qgT u (w.map (nrm u)) (nrm u ((l.map (fun i=> w.getD i zero)).foldr (qcM d) (if d then zero else one))):= by
    have unit (v:Sig):qcM d v (if d then zero else one)=v:= by
      apply q1j
      intro i
      cases d <;> simp [q1q,q1v,q1p]
    cases l with
    | nil=> exact Or.inl (qdb (by cases d <;> simp))
    | cons i l=>
      cases l with
      | nil=>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (q5B w i)
      | cons j l=>
        cases l with
        | cons a l=> simp at hl
        | nil=>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact qcN d (q5B w i) (q5B w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h=> ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h=> ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [q75])
    left
    cases l with
    | nil=> exact qdb (Or.inr (by simp [gv,qbb]))
    | cons i l=> exact qdc (q5B w i)
private lemma qcW {u target} {w:List Sig} {z:Sig} {k S c} (h:Live u target k S)
    (hz:qdd w z ∨ (c=1 ∧ qgT u w z)) (sub:∀ a ∈ S,a ∈ w++[z]):
    ∃ k' S',k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S',a ∈ w:= by
  by_cases hm:z ∈ S
  · by_cases hw:z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu:a ∈ w ∨ a=z:= by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:= q95 h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:= S.erase (bin d a b)
        have ht:Live u target k (insert (bin d a b) U):= by simpa [U,Finset.insert_erase hm] using h
        have hu:∀ v ∈ U,v ∈ w:= by
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
    have hn:a ≠ z:= fun hh=> hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma q3c {u target} (gs:List Gate) (w:List Sig)
    (legal:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2)
    (mono:u=false → ∀ g ∈ gs,q75 g=false)
    (hp:qcQ target) (hout:target ∈ (q36 gs w).map (nrm u)):
    ∃ k S,k ≤ gs.countP (fun g=> !q75 g) ∧ Live u target k S ∧ ∀ a ∈ S,a ∈ w.map (nrm u):= by
  induction gs generalizing w with
  | nil=> exact ⟨0,{target},by simp,Live.stop hp,by simpa [q36] using hout⟩
  | cons g gs ih=>
    obtain ⟨k,S,hk,ht,hs⟩:= ih (w++[gv w g]) (fun a ha=> legal a (by simp [ha]))
      (fun hu a ha=> mono hu a (by simp [ha])) hout
    have rep:= q5i u w g (legal g (by simp)) (fun hu=> mono hu g (by simp))
    rw [List.map_append] at hs
    have rep':qdd (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if q75 g then 0 else 1)=1 ∧ qgT u (w.map (nrm u)) (nrm u (gv w g))):=
      rep.imp id (fun h=> ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩:= qcW ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn:q75 g <;> simp [hn] at hl ⊢ <;> omega
private lemma q13 (i) (w:List Sig) (j:Nat):
    (w.map (bit i)).getD j false=bit i (w.getD j zero):= by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none=> exact (q1v _).symm
  | some a=> rfl
private lemma qds (i) (g:Gate) (w:List Sig)
    (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)):
    bit i (gv w g)=g.op.eval (g.inputs.map fun j=> (w.map (bit i)).getD j false):= by
  obtain ⟨o,l⟩:= g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [q13]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil=> exact q1p _
    | cons a l ih=>
      change bit i (qcM false _ _)=(_ && _)
      rw [q1q]; exact congrArg (fun x=> bit i (w.getD a zero) && x) ih
  · induction l with
    | nil=> exact q1v _
    | cons a l ih=>
      change bit i (qcM true _ _)=(_ || _)
      rw [q1q]; exact congrArg (fun x=> bit i (w.getD a zero) || x) ih
  · cases l with
    | nil=>
      change bit i (neg zero)= !false
      rw [q1o,q1v]
    | cons a l=> exact q1o _ _
private lemma q37 (gs:List Gate) (i) (w:List Sig)
    (hg:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)):
    (q36 gs w).map (bit i)=
    gs.foldl (fun (l:List Bool) g=> l++[g.op.eval (g.inputs.map fun j=> l.getD j false)]) (w.map (bit i)):= by
  induction gs generalizing w with
  | nil=> rfl
  | cons g gs ih=>
    change (q36 gs (w++[gv w g])).map _=_
    rw [ih _ (fun a ha=> hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,qds i g w (hg g (by simp))]
abbrev Wire (R:Type):= R → Bool
def inv {R} (a:Wire R):Wire R:= fun r=> !(a r)
def q29 {R} (isOr:Bool) (a b:Wire R):Wire R:=
  if isOr then fun r=> a r || b r else fun r=> a r && b r
def comb {R} (d:Nat) (a b:Wire R):Wire R:=
  if d=0 then q29 false a b else if d=1 then q29 true a b else
    if d=2 then q29 false a (inv b) else q29 false (inv a) b
def q05 {R} (a:Wire R):Prop:= ∃ b:Bool,a=fun _=> b
def q00 {R} (u:Bool) (pool:List (Wire R)) (v:Wire R):Prop:=
  v ∈ pool ∨ q05 v ∨ (u=true ∧ inv v ∈ pool)
def Reach {R} (u:Bool) (roots:List (Wire R)):Nat → List (Wire R) → Prop
  | 0,b=> b=roots
  | p+1,c=> ∃ (op:Bool) (bank:List (Wire R)) (a b:Wire R),Reach u roots p bank ∧ q00 u bank a ∧
      q00 u bank b ∧ c=q29 op a b::bank
theorem Reach.start {R u} {roots:List (Wire R)}:Reach u roots 0 roots:= rfl
theorem Reach.two {R u} {roots:List (Wire R)} {p bank a b} (op:Bool) (h:Reach u roots p bank)
    (ha:q00 u bank a) (hb:q00 u bank b):Reach u roots (p+1) (q29 op a b::bank):=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots:List (Wire R)} {motive:∀ p bank,Reach u roots p bank → Prop}
    (start:motive 0 roots Reach.start)
    (two:∀ {p bank a b} (op:Bool) (h:Reach u roots p bank) (ha:q00 u bank a)
      (hb:q00 u bank b),motive p bank h →
      motive (p+1) (q29 op a b::bank) (Reach.two op h ha hb))
    {p bank} (h:Reach u roots p bank):motive p bank h:= by
  induction p generalizing bank with
  | zero=>
    obtain rfl:= h
    exact start
  | succ p ih=>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩:= h
    exact two op h ha hb (ih h)
def kept {α:Type} (save:Bool) (x:α) (xs:List α):= if save then x::xs else xs
def Run {R} (u:Bool) (goal:Wire R):Nat → List (Wire R) → Prop
  | 0,zs=> List.Perm [goal] zs
  | s+1,zs=> ∃ (op:Nat) (ka kb:Bool) (a b:Wire R) (rest:List (Wire R)),q0N u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b::kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal:Wire R}:Run u goal 0 [goal]:= List.Perm.refl _
theorem Run.perm {R u} {goal:Wire R} {s:Nat} {xs zs:List (Wire R)} (p:xs.Perm zs)
    (h:Run u goal s xs):Run u goal s zs:= by
  cases s with
  | zero=> exact List.Perm.trans h p
  | succ s=>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩:= h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal:Wire R} {s:Nat} {a b:Wire R} {rest:List (Wire R)} (op:Nat) (hd:q0N u op) (ka kb:Bool)
    (h:Run u goal s (comb op a b::kept ka a (kept kb b rest))):Run u goal (s+1) (a::b::rest):=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal:Wire R} {motive:∀ s ws,Run u goal s ws → Prop}
    (stop:motive 0 [goal] Run.stop)
    (perm:∀ {s xs zs} (p:List.Perm xs zs) (h:Run u goal s xs),motive s xs h → motive s zs (Run.perm p h))
    (two:∀ {s a b rest} (op:Nat) (hd:q0N u op) (ka kb:Bool) (h:Run u goal s (comb op a b::kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h:Run u goal s ws):motive s ws h:= by
  induction s generalizing ws with
  | zero=> exact perm h Run.stop stop
  | succ s ih=>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩:= h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
abbrev Row:= Fin 512
def qcD (a:Sig):Bool:= !(bit 0 a)
theorem qbp {u} {w:List Sig} (h:w.all qcD=true):w.map (nrm u)=w:= by
  have e:w.map (nrm u)=w.map id:= by
    apply List.map_congr_left
    intro a ha
    exact qbo (by simpa [qcD] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem q97 {u T k S} (h:Live u T k S) {r s:Row}
    (diff:bit r T ≠ bit s T):∃ a ∈ S,bit r a ≠ bit s a:= by
  induction h using Live.ind with
  | stop hp=> exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih=>
    obtain ⟨v,hv,hd⟩:= ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq:bit r a=bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [q1i,q1i,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem qd1 {u T k S} (h:Live u T k S) (roots:List Sig) (a:Sig)
    (sub:∀ v ∈ S,v ∈ roots) (r s:Row) (diff:bit r T ≠ bit s T)
    (isolated:∀ v ∈ roots,v ≠ a → bit r v=bit s v):a ∈ S:= by
  obtain ⟨v,hv,hd⟩:= q97 h diff
  by_cases veq:v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs:List Sig:= [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph:Sig:= 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def qdv (r:Row) (j:Fin 9):= bit r (inputs.getD j.val zero)
def edge (x:Fin 9 → Bool):Bool:=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem q2X:∀ r:Row,bit r graph=edge (qdv r):= by decide +kernel
theorem q5E:qcQ graph:= by unfold qcQ; decide +kernel
theorem q71:List.ofFn (fun j:Fin 9=> inputs.getD j.val zero)=inputs:= rfl
theorem qdw (r:Row):List.ofFn (qdv r)=inputs.map (bit r):= by
  rw [←q71]
  rw [List.map_ofFn]
  rfl
theorem qf9 (C:Circuit) (h:PEqualNP.MetaComplexity.FanInTwo C)
    (i:Nat) (r:Row):bit r ((q36 C.gates inputs).getD i zero)=
      (C.wires (List.ofFn (qdv r))).getD i false:= by
  rw [←q13,q37 _ _ _ (fun g hg=> (h g hg).1),qdw]
  rfl
def Impossible (u:Bool) (T:Sig) (cap:Nat) (S:Finset Sig):Prop:=
  ∀ k,k ≤ cap → ¬Live u T k S
abbrev q04:= Nat × Nat × Nat × Nat × Nat
abbrev q02:= Sig × Nat × Nat × List Sig
def q02.wires (c:q02):List Sig:= c.2.2.2
abbrev Bits:= BitVec 152
abbrev q0g:= Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
abbrev q0a:= Nat × Nat × (Nat → Bits × Bits) × List q04 × List (List Nat) ×
  (Nat → q0g) × (Nat → Nat → Option (Nat × Nat))
def q0a.cap (g:q0a):Nat:= g.2.1
def qbd (i:Fin 9):Nat:= [4,2,1,2,3,0,1,2,3].getD i.val 0
def q0o (i:Fin 9):Row:= Fin.ofNat 512 (1 <<< qbd i)
def qcL (i:Fin 9):Row:= Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< qbd i))
set_option maxHeartbeats 1000000 in
theorem qde:
    (∀ i:Fin 9,bit (q0o i) graph ≠ bit (qcL i) graph) ∧
    (∀ i j:Fin 9,i ≠ j →
      bit (q0o i) (inputs.getD j.val zero)=
      bit (qcL i) (inputs.getD j.val zero)):= by decide +kernel
theorem signedRealize (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) :
    ∃ k, k ≤ C.gates.countP (fun g => !q75 g) ∧ Live true graph k inputs.toFinset := by
  have goalEq : (q36 C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (qf9 C legal C.output r).trans ((congrFun computes (qdv r)).trans (q2X r).symm)
  have out := q5B (u:=true) (q36 C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [qbo pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := q3c C.gates inputs legal (by intro h; cases h) q5E
    (out.resolve_right (fun h => h q5E))
  have ns : inputs.all qcD = true := by decide +kernel
  rw [qbp ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [←q71] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply qd1 run inputs (inputs.getD i.val zero) sub (q0o i) (qcL i)
        (qde.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply qde.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem minor_lower15 (hroot : Impossible true graph 14 inputs.toFinset) (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) : 15 ≤ C.size := by
  obtain ⟨k,hk,run⟩ := signedRealize C legal computes
  have bound : 15 ≤ k := by
    by_contra h
    exact hroot k (by omega) run
  exact bound.trans (hk.trans List.countP_le_length)
end PEqualNP.Outside.L_meta_1890.BoundsNine
