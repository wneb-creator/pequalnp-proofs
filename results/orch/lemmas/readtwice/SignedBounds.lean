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
def q3v (d:Nat):= if d=2 then 3 else if d=3 then 2 else d
theorem q0Q {u d} (h:q0N u d):d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3):= by
  rcases h with h | ⟨h,j⟩
  · omega
  · have:d=0 ∨ d=1 ∨ d=2 ∨ d=3:= by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem q1e {u d} (h:q0N u d) (a b:Sig):bin d a b=bin (q3v d) b a:= by
  rcases q0Q h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,q3v,BitVec.and_comm,BitVec.or_comm]
theorem q3w {u d} (h:q0N u d):q0N u (q3v d) ∧ q3v (q3v d)=d:= by
  rcases q0Q h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [q3v,q0N]
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
private lemma q98 {u target k S} (h:Live u target k S):S.card ≤ k+1:= by
  induction h using Live.ind with
  | stop hp=> simp
  | @binary k U a b d hd ha hb hab hf _ ih=>
    have hu:bin d a b ∉ U:= fun hm=> hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:= Finset.card_insert_le (a:= a) (s:= insert b U)
    have h2:= Finset.card_insert_le (a:= b) (s:= U)
    omega
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
noncomputable def cost {R} (a:Wire R):Nat:= by
  classical exact if q05 a then 1 else 0
noncomputable def mass {R} (xs:List (Wire R)):Nat:= (xs.map cost).sum
def q00 {R} (u:Bool) (pool:List (Wire R)) (v:Wire R):Prop:=
  v ∈ pool ∨ q05 v ∨ (u=true ∧ inv v ∈ pool)
def qf0 {R} (u:Bool) (pool xs:List (Wire R)):= ∀ a ∈ xs,q00 u pool a
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
theorem qaw {R} (a:Wire R) (xs):mass (a::xs)=cost a + mass xs:= by
  simp [mass]
theorem qay {R} (a:Wire R) (xs) (k:Bool):mass xs ≤ mass (kept k a xs):= by
  cases k <;> simp [kept,qaw]
theorem q72 {R} {a:Wire R} (h:q05 a):q05 (inv a):= by
  obtain ⟨v,rfl⟩:= h
  exact ⟨!v,rfl⟩
theorem q73 {R} (a:Wire R):inv (inv a)=a:= by
  funext r
  simp [inv]
theorem q2r {R} (a:Wire R):cost (inv a)=cost a:= by
  have:q05 (inv a) ↔ q05 a:= ⟨fun h=> q73 a ▸ q72 h,q72⟩
  by_cases h:q05 a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x=> h (this.mp x))]
theorem q0Y {R u} {bank:List (Wire R)} {a} (hu:u=true) (h:q00 u bank a):q00 u bank (inv a):= by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(q73 a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (q72 h))
  · exact Or.inl h
theorem q1A {R} {a b:Wire R} (op) (h:q05 a) (g:q05 b):
    q05 (q29 op a b):= by
  obtain ⟨v,rfl⟩:= h
  obtain ⟨w,rfl⟩:= g
  cases op <;> exact ⟨_,rfl⟩
theorem q3R {R u} (op) {a b:Wire R} {bank}
    (h:q05 a ∨ q05 b) (ha:q00 u bank a) (hb:q00 u bank b):
    q00 u bank (q29 op a b):= by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false,by funext x; simp [q29]⟩)
    · simpa [q29] using hb
    · simpa [q29] using hb
    · exact Or.inr (Or.inl ⟨true,by funext x; simp [q29]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false,by funext x; simp [q29]⟩)
    · simpa [q29] using ha
    · simpa [q29] using ha
    · exact Or.inr (Or.inl ⟨true,by funext x; simp [q29]⟩)
theorem q11 {R u} {bank v} (w:Wire R) (h:q00 u bank v):
    q00 u (w::bank) v:=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem q3b {R u} (roots:List (Wire R)) {p bank a b} (op) (hp:Reach u roots p bank)
    (ha:q00 u bank a) (hb:q00 u bank b):
    ∃ q next,Reach u roots q next ∧ q00 u next (q29 op a b) ∧
        (∀ v,q00 u bank v → q00 u next v) ∧
        q+cost a+cost b ≤ p+1+cost (q29 op a b):= by
  classical
  by_cases c:q05 a ∨ q05 b
  · refine ⟨p,bank,hp,q3R op c ha hb,fun _ h=> h,?_⟩
    by_cases ca:q05 a <;> by_cases cb:q05 b
    · simp [cost,ca,cb,q1A op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca:¬q05 a:= fun h=> c (Or.inl h)
    have cb:¬q05 b:= fun h=> c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h=> q11 _ h,
      by simp [cost,ca,cb]⟩
theorem q28 {R u} {bank:List (Wire R)} {d a b} (hd:q0N u d) (ha:q00 u bank a) (hb:q00 u bank b):
    ∃ op x y,comb d a b=q29 op x y ∧ q00 u bank x ∧ q00 u bank y ∧ cost x=cost a ∧ cost y=cost b:= by
  rcases q0Q hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,q0Y hu hb,rfl,q2r b⟩
  · exact ⟨false,inv a,b,rfl,q0Y hu ha,hb,q2r a,rfl⟩
theorem q39 {R u} (roots:List (Wire R)) {p bank a b} (d) (hd:q0N u d) (hp:Reach u roots p bank)
    (ha:q00 u bank a) (hb:q00 u bank b):
    ∃ q next,Reach u roots q next ∧ q00 u next (comb d a b) ∧
        (∀ v,q00 u bank v → q00 u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b):= by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩:= q28 hd ha hb
  rw [e,←cx,←cy]
  exact q3b roots op hp hx hy
theorem qaC {α:Type} {k:Bool} {x a:α} {xs} (h:x ∈ kept k a xs):
    x=a ∨ x∈xs:= by cases k <;> simp_all [kept]
theorem q2h {R u} {goal:Wire R} (nc:¬q05 goal) {s ws}
    (h:Run u goal s ws) (roots:List (Wire R)) {p bank}
    (hp:Reach u roots p bank) (hs:qf0 u bank ws):
    ∃ q next,Reach u roots q next ∧ q00 u next goal ∧ q+mass ws ≤ p+s:= by
  classical
  induction h using Run.ind generalizing p bank with
  | stop=>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih=>
    have hsub:qf0 u bank _:= fun v hv=> hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩:= ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih=>
    obtain ⟨r,T,hT,hz,inc,le⟩:= q39 roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht:qf0 u T (comb op a b::kept ka a (kept kb b rest)):= by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases qaC hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (qaC hh))
    obtain ⟨q,W,hW,hv,hl⟩:= ih hT ht
    have hlen:= qay a (kept kb b rest) ka
    have hlen':= qay b rest kb
    rw [qaw] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [qaw,qaw]
    omega
def qdg {R S:Type} (rows:S → R) (a:Wire R):Wire S:=
  fun r=> a (rows r)
theorem qdi {R S:Type} (rows:S → R) (k:Bool) (a:Wire R) (ws):
    (kept k a ws).map (qdg rows)=
    kept k (qdg rows a) (ws.map (qdg rows)):= by
  cases k <;> simp [kept]
theorem qdh {R S:Type} (rows:S → R) (d) (a b:Wire R):
    qdg rows (comb d a b)=comb d (qdg rows a) (qdg rows b):= by
  unfold comb
  split_ifs <;> rfl
theorem qdj {R S:Type} {u} (rows:S → R) {goal s ws} (h:Run u goal s ws):
    Run u (qdg rows goal) s (ws.map (qdg rows)):= by
  induction h using Run.ind with
  | stop=> exact Run.stop
  | perm p _ ih=> exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih=>
    simp only [List.map_cons,qdi,qdh] at ih ⊢
    exact Run.two op hd ka kb ih
theorem qcO {R S:Type} {u} (rows:S → R) {goal s ws} (h:Run u goal s ws)
    (nc:¬q05 (qdg rows goal)) {roots:List (Wire S)} {p bank L}
    (hp:Reach u roots p bank) (hs:qf0 u bank (ws.map (qdg rows)))
    (hl:∀ q bs,Reach u roots q bs → q00 u bs (qdg rows goal) → L ≤ q):
    L + mass (ws.map (qdg rows)) ≤ p+s:= by
  obtain ⟨q,bs,hq,ht,hle⟩:= q2h nc (qdj rows h) roots hp hs
  have hqle:= hl q bs hq ht
  omega
abbrev Row:= Fin 512
def qbu (a:Sig):Wire Row:= fun r=> bit r a
def qf8 (f:Wire Row):Sig:=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem q1t (f:Wire Row) (r:Row):bit r (qf8 f)=f r:= by
  simp only [bit,qf8,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem qfb (v:Sig):qf8 (qbu v)=v:= by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact q1t (qbu v) ⟨j,hj⟩
theorem qbx (f:Wire Row):qbu (qf8 f)=f:= by
  funext r
  exact q1t f r
theorem qbt (a:Sig):qbu (neg a)=inv (qbu a):= by
  funext r
  exact q1o _ _
theorem qbs (d:Nat) (a b:Sig):
    qbu (bin d a b)=comb d (qbu a) (qbu b):= by
  funext r
  simp only [qbu,q1i,comb]
  split_ifs <;> rfl
theorem qan {α β:Type} (f:α → β) (d:Bool) (a:α) (l:List α):
    (kept d a l).map f=kept d (f a) (l.map f):= by cases d <;> rfl
theorem q7b {α:Type} (k:Bool) (a:α) (l:List α)
    (hn:l.Nodup) (ha:a ∉ l):(kept k a l).Nodup:= by cases k <;> simp [kept,hn,ha]
theorem q7a (k:Bool) (a:Sig) (l:List Sig):
    (kept k a l).toFinset=if k then insert a l.toFinset else l.toFinset:= by
  cases k <;> simp [kept]
theorem q94 {u} {T:Sig} {k S} (h:Live u T k S) (v:List Sig)
    (hv:v.Nodup) (eqv:v.toFinset=S):Run u (qbu T) k (v.map qbu):= by
  classical
  induction h using Live.ind generalizing v with
  | stop hp=>
    have eq:[T].Perm v:= by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih=>
    let rest:= ((U.erase a).erase b).toList
    let ka:= decide (a ∈ U)
    let kb:= decide (b ∈ U)
    let mid:= kept kb b rest
    let tail:= kept ka a mid
    have er:rest.toFinset=(U.erase a).erase b:= by simp [rest]
    have ar:a ∉ rest:= by simp [rest]
    have br:b ∉ rest:= by simp [rest]
    have hr:rest.Nodup:= Finset.nodup_toList _
    have bm:= q7b kb b rest hr br
    have am:a ∉ mid:= by cases h:kb <;> simp [mid,kept,h,hab,ar]
    have nd:= q7b ka a mid bm am
    have ht:tail.toFinset=U:= by
      change (kept ka a (kept kb b rest)).toFinset=U
      rw [q7a,q7a,er]
      ext j
      by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases aj:j=a <;>
        by_cases bj:j=b <;> simp_all [ka,kb]
    have hf:bin d a b ∉ tail:= by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:= ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map qbu) at progress
    rw [List.map_cons,qan,qan,qbs] at progress
    have perm:(a::b::rest).Perm v:= by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja:j=a <;> by_cases jb:j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
theorem qfa (f:Wire Row):qf8 (inv f)=neg (qf8 f):= by
  rw [←qfb (neg (qf8 f)),qbt,qbx]
theorem qfc (d:Bool) (f g:Wire Row):
    qf8 (q29 d f g)=qcM d (qf8 f) (qf8 g):= by
  apply q1j
  intro r
  rw [q1t,q1q,q1t,q1t]
  cases d <;> rfl
theorem q12 {u} {bank:List (Wire Row)} {a} (h:q00 u bank a):
    Repr u ((bank.map qf8).map (nrm u)) (qf8 a):= by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply qdb
    cases b
    · exact Or.inl (q1j fun i=> (q1t _ i).trans (q1v i).symm)
    · exact Or.inr (q1j fun i=> (q1t _ i).trans (q1p i).symm)
  · have:= qfa a
    refine Or.inl ?_
    rw [←qbq,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)
theorem qd3 {u} {roots:List (Wire Row)} {p bank}
    (h:Reach u roots p bank) {T k S} (run:Live u T k S)
    (sub:∀ a ∈ S,a ∈ (bank.map qf8).map (nrm u)):
    ∃ l V,l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V,a ∈ (roots.map qf8).map (nrm u):= by
  induction h using Reach.ind generalizing k S with
  | start=> exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih=>
    rw [List.map_cons,List.map_cons,qfc] at sub
    have rep:= qcN d (q12 ha) (q12 hb)
    obtain ⟨k',S',hk,run',sub'⟩:= qcW (c:= 1) run (rep.imp id (fun h=> ⟨rfl,h⟩))
      (fun a hm=> by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩:= ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩
def qcD (a:Sig):Bool:= !(bit 0 a)
theorem qbp {u} {w:List Sig} (h:w.all qcD=true):w.map (nrm u)=w:= by
  have e:w.map (nrm u)=w.map id:= by
    apply List.map_congr_left
    intro a ha
    exact qbo (by simpa [qcD] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem qd2 {u} {roots:List Sig} {p bank T} (hp:qcQ T) (nT:qcD T=true) (nR:roots.all qcD=true)
    (h:Reach u (roots.map qbu) p bank) (hit:q00 u bank (qbu T)):
    ∃ k S,k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S,a ∈ roots:= by
  have hm:= q12 hit
  rw [qfb] at hm
  unfold Repr at hm
  rw [qbo (by simpa [qcD] using nT)] at hm
  have mem:= hm.resolve_right (fun hn=> hn hp)
  obtain ⟨l,V,hl,hr,hs⟩:= qd3 h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e:(roots.map qbu).map qf8=roots:= by simp [List.map_map,Function.comp_def,qfb]
  rw [e,qbp nR] at hs
  exact hs
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
def qd7 (f:Row → Row) (a:Sig):= qf8 fun r=> bit (f r) a
theorem q1r (f:Row → Row) (a:Sig) (r:Row):
    bit r (qd7 f a)=bit (f r) a:= q1t _ _
theorem qbw (f:Row → Row) (a:Sig):
    qbu (qd7 f a)=qdg f (qbu a):= by funext r; exact q1r f a r
theorem qd8 (f:Row → Row) (d:Nat) (a b:Sig):
    qd7 f (bin d a b)=bin d (qd7 f a) (qd7 f b):= by
  apply q1j
  intro r
  simp only [q1r,q1i]
theorem qda (f:Row → Row) (onto:Function.Surjective f):
    Function.Injective (qd7 f):= by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩:= onto ⟨j,hj⟩
  have he:= congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
  rw [q1r,q1r,hr] at he
  exact he
theorem qd9 (f:Row → Row):qd7 f zero=zero ∧ qd7 f one=one:= by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (q1r f zero ⟨j,hj⟩).trans ((q1v _).trans (q1v ⟨j,hj⟩).symm)
  · exact (q1r f one ⟨j,hj⟩).trans ((q1p _).trans (q1p ⟨j,hj⟩).symm)
theorem q96 {u T k S} (h:Live u T k S) (f:Row → Row) (onto:Function.Surjective f):
    Live u (qd7 f T) k (S.image (qd7 f)):= by
  have inj:= qda f onto
  obtain ⟨fz,fo⟩:= qd9 f
  have pp (v) (p:qcQ v):qcQ (qd7 f v):=
    ⟨fun e=> p.1 (inj (e.trans fz.symm)),fun e=> p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp=> simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih=>
    have fresh:qd7 f (bin d a b) ∉ (insert a (insert b U)).image (qd7 f):= by
      intro hm
      obtain ⟨v,hv,eq⟩:= Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,qd8] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh=> hab (inj hh)) fresh ih
theorem qaZ {u T k S} (h:Live u T k S) (none:u=false) {r s:Row}
    (pos:bit r T=true) (negRow:bit s T=false):
    ∃ a ∈ S,bit r a=true ∧ bit s a=false:= by
  induction h using Live.ind with
  | stop hp=> exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih=>
    obtain ⟨v,hv,hp,hn⟩:= ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [q1i] at hp hn
      subst none
      rcases q0Q hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p:bit r a <;> cases q:bit s a <;> cases u:bit r b <;> cases z:bit s b <;> simp_all
      · cases p:bit r a <;> cases q:bit s a <;> cases u:bit r b <;> cases z:bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (u:Bool) (roots:List Sig) (T:Sig) (L:Nat):Prop:=
  ∀ p bank,Reach u (roots.map qbu) p bank → q00 u bank (qbu T) → L ≤ p
def Impossible (u:Bool) (T:Sig) (cap:Nat) (S:Finset Sig):Prop:=
  ∀ k,k ≤ cap → ¬Live u T k S
def q09 (T:Sig) (roots:List Sig) (a:Sig):Prop:=
  ∃ r s:Row,bit r T ≠ bit s T ∧ ∀ v ∈ roots,v ≠ a → bit r v=bit s v
theorem qaf {u roots T L} (hp:qcQ T) (nT:qcD T=true) (nR:roots.all qcD=true)
    (essential:∀ a ∈ roots,q09 T roots a)
    (noRun:Impossible u T L roots.toFinset):Lower u roots T (L+1):= by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩:= qd2 hp nT nR h ha
  have he:roots.toFinset=S:= by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm=> ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩:= essential _ hm
    exact qd1 run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)
theorem qbv {v:Sig} (hv:qcQ v):¬q05 (qbu v):= by
  rintro ⟨b,h⟩
  have hr:Repr false [] v:= by
    apply qdb
    cases b
    · exact Or.inl (q1j fun i=> (congrFun h i).trans (q1v i).symm)
    · exact Or.inr (q1j fun i=> (congrFun h i).trans (q1p i).symm)
  have hr':qdd [] v:= hr
  exact (hr'.resolve_left (by simp)) hv
theorem qav {R} (a b:List (Wire R)):mass (a++b)=mass a + mass b:= by
  simp [mass]
theorem qax {R} (xs:List (Wire R)) (hc:∀ x ∈ xs,q05 x):
    mass xs=xs.length:= by
  induction xs with
  | nil=> simp [mass]
  | cons a xs ih=>
    have ha:= hc a (by simp)
    simp only [qaw,List.length_cons,cost,if_pos ha,ih (fun x hx=> hc x (by simp [hx]))]
    omega
theorem qah {u} {roots other:List Sig} {T G:Sig} (pT:qcQ T) (nT:qcD T=true) (nR:roots.all qcD=true) (pG:qcQ G)
    (r:Row → Row) (eq:qd7 r T=G)
    (q2C:∀ a ∈ roots,q00 u (other.map qbu) (qbu (qd7 r a)))
    (singles:Finset Sig) (necessary:∀ a ∈ singles,q09 T roots a)
    (constant:∀ a ∈ singles,q05 (qbu (qd7 r a)))
    (L:Nat) (prior:Lower u other G L):Lower u roots T (L + singles.card):= by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩:= qd2 pT nT nR hh ha
  have subS:singles ⊆ S:= by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩:= necessary a hs
    exact qd1 run roots a sub i j hd hiso
  let front:= singles.toList ++ (S \ singles).toList
  have nd:front.Nodup:= by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe:front.toFinset=S:= by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run':= q94 run front nd fe
  have gc:qdg r (qbu T)=qbu G:= (qbw _ _).symm.trans (congrArg qbu eq)
  have supp:qf0 u (other.map qbu) ((front.map qbu).map (qdg r)):= by
    intro v hv
    obtain ⟨_,hm,rfl⟩:= List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩:= List.mem_map.mp hm
    rw [←qbw]
    exact q2C a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:= qcO r run' (gc ▸ qbv pG) Reach.start supp
    (L:= L) (gc ▸ prior)
  have massLo:singles.card ≤ mass ((front.map qbu).map (qdg r)):= by
    simp only [front,List.map_append,qav]
    let xs:= (singles.toList.map qbu).map (qdg r)
    have only:∀ v ∈ xs,q05 v:= by
      intro v hv
      obtain ⟨_,hm,rfl⟩:= List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩:= List.mem_map.mp hm
      rw [←qbw]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz:= qax xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega
def q1W (ws:List Sig) (a b:Sig) (d:Nat) (ka kb:Bool):List Sig:=
  bin d a b::kept ka a (kept kb b ((ws.erase a).erase b))
theorem q30 {l:List Sig} (h:l.Nodup) (a:Sig):(l.erase a).toFinset=l.toFinset.erase a:= by
  ext x
  simp [h.mem_erase_iff]
theorem q2Z {u} {T:Sig} {cap:Nat} {ws:List Sig} (hn:ws.Nodup) (out:T ∉ ws)
    (twoStep:∀ a ∈ ws,∀ b ∈ ws,∀ d,q0N u d → ∀ ka kb,a ≠ b → bin d a b ∉ ws →
      qcQ (bin d a b) → (q1W ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (q1W ws a b d ka kb).toFinset):
    Impossible u T cap ws.toFinset:= by
  classical
  intro k hk h
  generalize he:ws.toFinset=S at h
  induction h using Live.ind with
  | stop hp=>
    have mem:T ∈ ws.toFinset:= he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _=>
    have am:a ∈ ws:= List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm:b ∈ ws:= List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh:bin d a b ∉ ws:= fun h=> hf (he ▸ List.mem_toFinset.mpr h)
    have hz:= q95 tail _ (Finset.mem_insert_self _ _)
    let ka:= decide (a ∈ U)
    let kb:= decide (b ∈ U)
    let rest:= (ws.erase a).erase b
    have er:rest.toFinset=(ws.toFinset.erase a).erase b:= by
      rw [show rest=(ws.erase a).erase b by rfl,q30 (hn.erase _) b,
        q30 hn a]
    have ke:(kept ka a (kept kb b rest)).toFinset=U:= by
      rw [q7a,q7a,er,he]
      ext j
      by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases ja:j=a <;>
        by_cases jb:j=b <;> simp_all [ka,kb]
    have rn:rest.Nodup:= (hn.erase _).erase _
    have ar:a ∉ rest:= fun h=> (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br:b ∉ rest:= (hn.erase a).not_mem_erase
    have nk:= q7b kb b rest rn br
    have ax:a ∉ kept kb b rest:= by cases kb <;> simp [kept,ar,hab]
    have nd:(q1W ws a b d ka kb).Nodup:= by
      refine List.nodup_cons.mpr ⟨?_,q7b ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq:(q1W ws a b d ka kb).toFinset=insert (bin d a b) U:= by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_
      simp [ke]
    have sc:= q98 tail
    have len:(q1W ws a b d ka kb).length ≤ cap:= by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
def Sep (T:Sig) (width:Nat) (pos negRow:Fin width → Row)
    (asig:Sig → BitVec width × BitVec width):Prop:=
  (∀ i,bit (pos i) T=true ∧ bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def q26 {n} (oriented:Bool) (s:BitVec n × BitVec n):BitVec n:=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def q2C {n} (oriented:Bool) (sig:Sig → BitVec n × BitVec n):List Sig → BitVec n
  | []=> 0
  | a::ws=> q26 oriented (sig a) ||| q2C oriented sig ws
theorem q2D {n:Nat} {oriented:Bool} {sig:Sig → BitVec n × BitVec n} {ws:List Sig} {i:Fin n}:
    (q2C oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(q26 oriented (sig a)).getLsbD i.val=true:= by
  induction ws with
  | nil=> simp [q2C]
  | cons a ws ih=>
    simp only [q2C,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem q2z {u T k S} (h:Live u T k S) {ws:List Sig} (he:ws.toFinset=S)
    {width:Nat} {r s:Fin width → Row} {sig} (correct:Sep T width r s sig)
    (oriented:Bool) (zeroNot:oriented=true → u=false):
    q2C oriented sig ws=BitVec.allOnes width:= by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i:Fin width:= ⟨j,hj⟩
  have yes:= (correct.1 i).1
  have no:= (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (q2D (i:= i)).mpr
  cases oriented with
  | false=>
    obtain ⟨a,ha,hd⟩:= q97 h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [q26,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx:bit (r i) a <;> cases hy:bit (s i) a <;> simp_all
  | true=>
    obtain ⟨a,ha,hp,hn⟩:= qaZ h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [q26,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem q2y {u T ws k} (h:Live u T k (List.toFinset ws)) {n:Nat} {r s:Fin n → Row} {sig}
    (correct:Sep T n r s sig):
    q2C (!u) sig ws=BitVec.allOnes n:= by
  apply q2z h rfl correct
  simp
def q0l (u:Bool) (raw:List Sig) (T d:Sig) (L:Nat):Prop:=
  ∃ (f:Row → Row) (roots:List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,q00 u (roots.map qbu) (qdg f (qbu a))) ∧
    ¬q05 (qdg f (qbu T)) ∧
    ∀ p bank,Reach u (roots.map qbu) p bank → q00 u bank (qdg f (qbu T)) → L ≤ p
def qaq (d a:Sig):= a &&& d
def q0Z (u:Bool) (d:Sig) (pool:List Sig) (a:Sig):=
  let m:= qaq d a
  m==zero || m==d || (pool.map (qaq d)).any (fun v=> v==m) ||
    (u && (let c:= qaq d (neg a); (pool.map (qaq d)).any (fun v=> v==c)))
theorem qas {f:Row → Row} {d a b:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:qaq d a=qaq d b):
    qdg f (qbu a)=qdg f (qbu b):= by
  funext r
  have h:= congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b
  simpa only [bit,qaq,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
theorem qau {f:Row → Row} {d a:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:qaq d a=zero):qdg f (qbu a)=fun _=> false:= by
  funext r
  have he:= congrArg (bit (f r)) eq
  change bit (f r) a=false
  rw [q1v] at he
  simpa only [bit,qaq,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
theorem qat {f:Row → Row} {d a:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:qaq d a=d):qdg f (qbu a)=fun _=> true:= by
  funext r
  have he:= congrArg (bit (f r)) eq
  change bit (f r) a=true
  rw [dom r] at he
  simpa only [bit,qaq,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def qcH (u:Bool) (f:Row → Row) (bank:List (Wire Row)) (pool:List Sig):=
  ∀ a ∈ pool,q00 u bank (qdg f (qbu a))
theorem q10 {u} {f:Row → Row} {d a:Sig} {bank pool}
    (dom:∀ r,bit (f r) d=true) (supplyB:qcH u f bank pool)
    (check:q0Z u d pool a=true):q00 u bank (qdg f (qbu a)):= by
  simp only [q0Z,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,qau dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,qat dom ho⟩)
  · exact qas dom he ▸ supplyB v hv
  · have h:= q0Y hu (qas dom he ▸ supplyB v hv)
    rw [qbt] at h
    have e:inv (qdg f (inv (qbu a)))=qdg f (qbu a):= by
      funext r
      simp [inv,qdg]
    rwa [e] at h
abbrev q03:= Nat × Sig × Sig
def q1Z (c:q03):= bin c.1 c.2.1 c.2.2
def q0O (u:Bool) (d:Nat):= decide (d<2) || (u && decide (d<4))
theorem q0P {u d} (h:q0O u d=true):q0N u d:= by
  simpa [q0O,q0N] using h
def q1Y (u:Bool) (d:Sig) (pool:List Sig) (c:q03):=
  q0O u c.1 && (q0Z u d pool c.2.1 && q0Z u d pool c.2.2)
theorem qcq {u} {f:Row → Row} {d:Sig} {roots bank pool q}
    (dom:∀ r,bit (f r) d=true) (hp:Reach u roots q bank) (hs:qcH u f bank pool)
    (c:q03) (valid:q1Y u d pool c=true):
    ∃ next,Reach u roots (q+1) next ∧ qcH u f next (q1Z c::pool):= by
  simp only [q1Y,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩:= q28 (q0P valid.1) (q10 dom hs valid.2.1)
    (q10 dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [q1Z,qbs,qdh,e]
    exact Or.inl (by simp)
  · exact q11 _ (hs _ hm)
def qak (u:Bool) (d:Sig) (pool:List Sig):List q03 → Option (List Sig)
  | []=> some pool
  | c::cs=> if q1Y u d pool c then qak u d (q1Z c::pool) cs else none
theorem qal {u} {d:Sig} {f:Row → Row} (dom:∀ r,bit (f r) d=true)
    {roots bank q pool} (hp:Reach u roots q bank) (hs:qcH u f bank pool)
    (cs:List q03) {result} (ok:qak u d pool cs=some result):
    ∃ next,Reach u roots (q+cs.length) next ∧ qcH u f next result:= by
  induction cs generalizing bank q pool with
  | nil=> cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih=>
    simp only [qak] at ok
    split at ok
    next h=>
      obtain ⟨next,hr,sh⟩:= qcq dom hp hs c h
      obtain ⟨out,hr',sh'⟩:= ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next=> contradiction
def q74 (d a:Sig):= qaq d a==zero || qaq d a==d
theorem q2s {d:Sig} {f:Row → Row} (dom:∀ r,bit (f r) d=true)
    (ws:List Sig):ws.countP (q74 d) ≤ mass ((ws.map qbu).map (qdg f)):= by
  classical
  induction ws with
  | nil=> simp [mass]
  | cons a ws ih=>
    simp only [List.countP_cons,List.map_cons,qaw]
    cases h:q74 d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc:q05 (qdg f (qbu a)):= by
        have hh:qaq d a=zero ∨ qaq d a=d:= by simpa only [q74,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,qau dom hz⟩
        · exact ⟨true,qat dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def qcF (u:Bool) (d:Sig) (L k p:Nat) (pool ws:List Sig):=
  decide (k+p < L+ws.countP (q74 d)) && ws.all (q0Z u d pool)
theorem qcG {u raw T d L} (slice:q0l u raw T d L) (cs:List q03)
    {pool ws cap} (built:qak u d raw cs=some pool)
    (nd:ws.Nodup) (cut:qcF u d L cap cs.length pool ws=true):
    Impossible u T cap ws.toFinset:= by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩:= slice
  obtain ⟨bank,hr,hs⟩:= qal dom (Reach.start (roots:= roots.map qbu)) base cs built
  simp only [qcF,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩:= cut
  have coveredS:qf0 u bank ((ws.map qbu).map (qdg f)):= by
    intro v hv
    obtain ⟨_,hm,rfl⟩:= List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hm
    exact q10 dom hs (List.all_eq_true.mp all a ha)
  have b:= qcO f (q94 h ws nd rfl) nc hr coveredS lo
  have massLo:= q2s dom ws
  have hu:= ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move:= Sig × Sig × Row
def qeP (d r:Row):Row:=
  if h:r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def q14 (d:Row):Row:= Fin.ofNat 512 (512-d.val)
def qdp (m:Move) (r:Row):Row:=
  if bit r m.1 then qeP m.2.2 r else if bit r m.2.1 then qeP (q14 m.2.2) r else r
def mux (m a b:Sig):= (m &&& a) ||| (~~~m &&& b)
def qgW (m:Move) (a:Sig):=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (q14 m.2.2).val) a)
theorem q1s (d r:Row) (a:Sig):bit r (a.rotateRight d.val)=bit (qeP d r) a:= by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h:r.val < 512-d.val <;> simp [qeP,h,r.isLt]
theorem q1z (p x y:Bool):(p && x || !p && y)=(if p then x else y):= by cases p <;> simp
theorem q1n (r:Row) (m a b:Sig):
    bit r (mux m a b)=if bit r m then bit r a else bit r b:= by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact q1z _ _ _
theorem q1l (r:Row) (m:Move) (a:Sig):bit r (qgW m a)=bit (qdp m r) a:= by
  simp only [qgW,q1n,q1s,qdp]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def qb4 (ms:List Move) (r:Row):= ms.foldl (fun j m=> qdp m j) r
def qb5 (ms:List Move) (a:Sig):= ms.foldr qgW a
theorem q1m (ms:List Move) (a:Sig) (r:Row):
    bit r (qb5 ms a)=bit (qb4 ms r) a:= by
  induction ms generalizing r with
  | nil=> rfl
  | cons m ms ih=> exact (q1l r m _).trans (ih _)
theorem qb6 (ms:List Move) (a:Sig):qb5 ms a=qd7 (qb4 ms) a:= by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (q1m ms a ⟨j,hj⟩).trans (q1r _ _ ⟨j,hj⟩).symm
def q3P (roots:List Sig) (w:Sig):= w==zero || w==one || roots.contains w
theorem q3Q {u roots w} (ok:q3P roots w=true):
    q00 u (roots.map qbu) (qbu w):= by
  simp only [q3P,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext q1v⟩)
  · exact Or.inr (Or.inl ⟨true,funext q1p⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def q1T (ms:List Move) (raw:List Sig) (T:Sig) (base:List Sig) (G:Sig):=
  qb5 ms T==G && raw.all (fun a=> q3P base (qb5 ms a))
theorem qam {u ms raw T base G} (ok:q1T ms raw T base G=true):
    qd7 (qb4 ms) T=G ∧
    ∀ a ∈ raw,q00 u (base.map qbu) (qbu (qd7 (qb4 ms) a)):= by
  simp only [q1T,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,qb6] at ok
  exact ⟨ok.1,fun a ha=> q3Q (ok.2 a ha)⟩
theorem qag {u ms raw T base G L} (ok:q1T ms raw T base G=true)
    (pT:qcQ T) (nT:qcD T=true) (nR:raw.all qcD=true) (pG:qcQ G)
    (hL:Lower u base G L):Lower u raw T L:= by
  obtain ⟨eq,supp⟩:= qam ok
  simpa using qah pT nT nR pG (qb4 ms) eq supp ∅ (by simp) (by simp) L hL
theorem qeS {u ms raw T base G L d} (ok:q1T ms raw T base G=true)
    (all:qb5 ms d=one) (properG:qcQ G) (hL:Lower u base G L):
    q0l u raw T d L:= by
  obtain ⟨eq,supp⟩:= qam ok
  have obs:qdg (qb4 ms) (qbu T)=qbu G:=
    (qbw _ _).symm.trans (congrArg qbu eq)
  refine ⟨qb4 ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←q1m,all,q1p]
  · intro a ha
    rw [←qbw]
    exact supp a ha
  · rw [obs]
    exact qbv properG
  · rw [obs]
    exact hL
def qgU (T:Sig) (roots:List Sig) (a:Sig) (rs:Row × Row):=
  (bit rs.1 T !=bit rs.2 T) &&
  roots.all (fun w=> w==a || bit rs.1 w==bit rs.2 w)
theorem qgV {T roots a rs} (ok:qgU T roots a rs=true):q09 T roots a:= by
  simp only [qgU,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne=> (ok.2 w hw).resolve_left hne⟩
def q1R (T:Sig) (raw:List Sig) (xs:List (Sig × Row × Row)):=
  qcD T && raw.all qcD && xs.all (fun a=> qgU T raw a.1 a.2)
theorem q32 {T raw xs} (ok:q1R T raw xs=true):
    ∀ a ∈ (xs.map Prod.fst).toFinset,q09 T raw a:= by
  simp only [q1R,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp ha)
  exact qgV (List.all_eq_true.mp ok.2 _ hm)
theorem q33 {T raw xs} (ok:q1R T raw xs=true):
    qcD T=true ∧ raw.all qcD=true:= by
  simp only [q1R,Bool.and_eq_true] at ok
  exact ok.1
theorem qac {u raw T} (properT:qcQ T) (xs:List (Sig × Row × Row))
    (ok:q1R T raw xs=true):
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1):= by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩:= qd2 properT (q33 ok).1 (q33 ok).2 hr hit
  have le:(xs.map Prod.fst).toFinset.card ≤ S.card:= by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩:= q32 ok a ha
    exact qd1 run raw a sub r s hd iso
  have bound:= q98 run
  omega
def q1S (ms:List Move) (T:Sig) (raw:List Sig) (base:List Sig) (G:Sig)
    (xs:List (Sig × Row × Row)):=
  q1T ms raw T base G && q1R T raw xs &&
    xs.all (fun a=> qb5 ms a.1==zero || qb5 ms a.1==one)
theorem q8X {u ms T raw base G xs L} (ok:q1S ms T raw base G xs=true)
    (properT:qcQ T) (properG:qcQ G) (low:Lower u base G L):
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card):= by
  simp only [q1S,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩:= qam ok.1.1
  apply qah properT (q33 ok.1.2).1 (q33 ok.1.2).2 properG _ eq supp _ (q32 ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh:= List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,qb6] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext q1v⟩
  · rw [h]
    exact ⟨true,funext q1p⟩
def qdC (m:Nat):List (Nat × Sig):=
  (List.range 9).filterMap fun i=> if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m:Nat):= (qdC m).map Prod.snd
def qfF (t:Nat):Sig:= bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def qgM (m:Nat):List Sig:= if m<512 then vars m else vars m ++ [qfF (m/512-1)]
def qgN (m j:Nat):= if m.testBit j then inputs.getD j zero else zero
def graphGoal (m:Nat):Sig:=
  let x:= qgN m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def q2E:Nat → Nat
  | 0=> 0xff
  | 1=> 0x55
  | 2=> 0x33
  | 3=> 0x11
  | 4=> 0xf
  | 5=> 0x5
  | 6=> 0x3
  | _=> 0x1
def q2F:Nat → Nat
  | 0=> 0x101010101010101
  | 1=> 0x1000100010001
  | 2=> 0x10100000101
  | 3=> 0x100000001
  | 4=> 0x1010101
  | 5=> 0x10001
  | 6=> 0x101
  | _=> 0x1
def q2G:Nat → Nat
  | 0=> 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1=> 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2=> 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3=> 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4=> 0x1000000000000000100000000000000010000000000000001
  | 5=> 0x100000000000000000000000000000001
  | 6=> 0x10000000000000001
  | _=> 0x1
def qeZ (z o:Nat):Sig:=
  let fixed:= z ||| o
  if z &&& o !=0 then zero else
    BitVec.ofNat 512 ((q2E (fixed &&& 7)*q2F ((fixed >>> 3) &&& 7)*q2G ((fixed >>> 6) &&& 7)) <<< o)
def q3t (z o:Nat):List Move:=
  (List.range 9).filterMap fun j=>
    let x:= inputs.getD j zero
    let step:= Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def qf4 (v:Nat):Move:=
  let i:= v &&& 15
  let j:= v >>> 4
  let a:= inputs.getD i zero
  let b:= inputs.getD j zero
  let d:= (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def qf1 (t:Nat) (mask:Nat):List (Sig × Row × Row):=
  (qdC mask).map fun (i,a)=>
    let r:= if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def q5C (m hints:Nat):List (Sig × Row × Row):=
  (qdC m).map fun (i,a)=>
    let r:= 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def qcR (T:Sig):= T !=zero && T !=one
theorem qcV (T:Sig) (h:qcR T=true):qcQ T:= by
  simpa only [qcR,qcQ,Bool.and_eq_true,bne_iff_ne] using h
abbrev q04:= Nat × Nat × Nat × Nat × Nat
def q24 (m z o:Nat):= m ^^^ (m &&& (z ||| o))
def q1M (m:Nat):Sig:= graphGoal m
def qcZ (m:Nat) (c:q04):Nat:= m % 512+512*(c.1/512)
def q23 (m:Nat) (c:q04) (prior:Nat → Nat):Bool:=
  let (z,o,q,s,L):= c
  let ms:= q3t z o
  let raw:= qcZ m c
  let free:= q24 raw (z % 512) o
  let G:= qb5 ms (q1M m)
  let xs:= qf1 (z/512+80) s
  let count:= (xs.map Prod.fst).toFinset.card
  qcR G && q1T ms (qgM raw) (q1M m) (qgM free) G &&
    (qb5 ms (qeZ z o)==one) &&
    (if q=0 then q1R G (qgM free) xs && decide (L ≤ count-1)
     else qcR (graphGoal q) &&
       q1S (q3t (q24 free q 0) 0) G (qgM free) (qgM q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
theorem q25 {u} {m:Nat} (c:q04) (prior:Nat → Nat)
    (valid:∀ q,Lower u (qgM q) (graphGoal q) (prior q))
    (ok:q23 m c prior=true):q0l u (qgM (qcZ m c)) (q1M m) (qeZ c.1 c.2.1) c.2.2.2.2:= by
  revert ok
  obtain ⟨z,o,q,s,L⟩:= c
  intro ok
  let ms:= q3t z o
  let raw:= qcZ m (z,o,q,s,L)
  let free:= q24 raw (z % 512) o
  let G:= qb5 ms (q1M m)
  let xs:= qf1 (z/512+80) s
  change (((qcR G && q1T ms (qgM raw) (q1M m) (qgM free) G) &&
    (qb5 ms (qeZ z o)==one)) && _)=true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply qeS ok.1.1.2 ok.1.2 (qcV _ ok.1.1.1)
  intro p bank hr ha
  have hh:= ok.2
  by_cases hq:q=0
  · simp only [q23,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (qac (qcV _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [q23,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (q8X hh.1.2 (qcV _ ok.1.1.1) (qcV _ hh.1.1) (valid q) p bank hr ha)
def q1H (old rep:Nat) (swaps:List Nat):=
  (qcR (graphGoal old) && qcD (graphGoal old) && (qgM old).all qcD) && qcR (graphGoal rep) &&
    q1T (swaps.map qf4) (qgM old) (graphGoal old) (qgM rep) (graphGoal rep)
theorem q1I {u old rep L swaps} (ok:q1H old rep swaps=true)
    (h:Lower u (qgM rep) (graphGoal rep) L):Lower u (qgM old) (graphGoal old) L:= by
  simp only [q1H,Bool.and_eq_true] at ok
  exact qag ok.2 (qcV _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (qcV _ ok.1.2) h
def q1B (entries:List (Nat × Nat)) (q:Nat):=
  ((entries.find? (fun a=> a.1==q)).map Prod.snd).getD 0
theorem q1c {u} (entries:List (Nat × Nat))
    (sound:∀ e ∈ entries,Lower u (qgM e.1) (graphGoal e.1) e.2) (q:Nat):
    Lower u (qgM q) (graphGoal q) (q1B entries q):= by
  unfold q1B
  cases h:entries.find? (fun a=> a.1==q) with
  | none=> exact fun _ _ _ _=> Nat.zero_le _
  | some e=>
    have he:= List.mem_of_find?_eq_some h
    have hit:(fun a:Nat × Nat=> a.1==q) e=true:= List.find?_some (p:= fun a:Nat × Nat=> a.1==q) (a:= e) h
    have eq:e.1=q:= beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev q02:= Sig × Nat × Nat × List Sig
def q02.domain (c:q02):Sig:= c.1
def q02.bound (c:q02):Nat:= c.2.1
def q02.paid (c:q02):Nat:= c.2.2.1
def q02.wires (c:q02):List Sig:= c.2.2.2
def q0n (u:Bool) (raw:List Sig) (T:Sig) (c:q02):=
  ∃ (f:Row → Row) (roots:List Sig) (bank:List (Wire Row)),
    (∀ r,bit (f r) c.domain=true) ∧ ¬q05 (qdg f (qbu T)) ∧
    (∀ q ws,Reach u (roots.map qbu) q ws → q00 u ws (qdg f (qbu T)) → c.bound ≤ q) ∧
    Reach u (roots.map qbu) c.paid bank ∧ qcH u f bank c.wires ∧ True
theorem q1G {u raw T d lb} (h:q0l u raw T d lb) (cs:List q03) {ws}
    (build:qak u d raw cs=some ws):q0n u raw T ⟨d,lb,cs.length,ws⟩:= by
  obtain ⟨f,roots,dom,sup,nc,prior⟩:= h
  obtain ⟨bank,hr,hs⟩:= qal dom (Reach.start (roots:= roots.map qbu)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [q02.paid] using hr,hs,trivial⟩
theorem qgL {u raw T c} (valid:q0n u raw T c) (k:Nat) (rest:List Sig)
    (choice:q03) (paid:Bool)
    (known:∀ a ∈ rest,q0Z u c.domain c.wires a=true)
    (buy:if paid then q1Y u c.domain c.wires choice=true
       else q0Z u c.domain c.wires (q1Z choice)=true)
    (bound:k+c.paid+paid.toNat <
      c.bound+(q1Z choice::rest).countP (q74 c.domain))
    (nd:(q1Z choice::rest).Nodup):
    Impossible u T k (q1Z choice::rest).toFinset:= by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:= valid
  let ws:= q1Z choice::rest
  have done (n:Nat) (out:List (Wire Row)) (reach:Reach u (roots.map qbu) n out)
      (zs:qcH u f out (q1Z choice::rest)) (le:n=c.paid+paid.toNat):False:= by
    have q2C:qf0 u out ((ws.map qbu).map (qdg f)):= by
      intro v hv
      obtain ⟨_,hm,rfl⟩:= List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hm
      exact zs _ ha
    have b:= qcO f (q94 run ws nd rfl) nc reach q2C lo
    have cm:= q2s dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (q74 c.domain) at bound
    omega
  cases paid with
  | false=>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact q10 dom hs buy
    · exact q10 dom hs (known _ hm)
  | true=>
    obtain ⟨out,hr,hc⟩:= qcq dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point:∀ v ∈ c.wires,q00 u out (qdg f (qbu v)):=
        fun v hu=> hc v (List.mem_cons_of_mem _ hu)
      exact q10 dom point (known _ hm)
def qdx (u:Bool) (c:q02) (k:Nat) (rest:List Sig) (op:q03):=
  let z:= q1Z op
  let extra:= !(q0Z u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (q74 c.domain)) &&
    rest.all (q0Z u c.domain c.wires)) && (!extra || q1Y u c.domain c.wires op)
theorem qdy {u raw T c} (valid:q0n u raw T c) {k rest op}
    (nd:(q1Z op::rest).Nodup) (cut:qdx u c k rest op=true):
    Impossible u T k (q1Z op::rest).toFinset:= by
  let extra:= !(q0Z u c.domain c.wires (q1Z op))
  apply qgL valid k rest op extra _ _ _ nd
  · simp only [qdx,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [qdx,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he:q0Z u c.domain c.wires (q1Z op) <;> simp_all [extra]
  · simp only [qdx,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def qaz (u:Bool) (raw:List Sig) (cs:List q03) (d:Sig) (lb:Nat):Option q02:=
  (qak u d raw cs).map (fun pool=> ⟨d,lb,cs.length,pool⟩)
theorem qaA {u raw T d L cs c} (slice:q0l u raw T d L)
    (h:qaz u raw cs d L=some c):q0n u raw T c:= by
  unfold qaz at h
  cases he:qak u d raw cs with
  | none=> simp [he] at h
  | some pool=>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact q1G slice cs he
abbrev Bits:= BitVec 152
abbrev q0j:= Bits × Bits
abbrev q08:= Sig × q0j
def qby {n:Nat} (r:Fin n → Row) (v:Sig):BitVec n:=
  (BitVec.ofBoolListLE (List.ofFn (fun i=> bit (r i) v))).cast List.length_ofFn
theorem qbA {n:Nat} (r:Fin n → Row) (v:Sig) (i:Fin n):
    (qby r v).getLsbD i.val=bit (r i) v:= by
  simp only [qby,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def qbP (r s:Fin 152 → Row) (a:Sig):q0j:= (qby r a,qby s a)
def qcS (T:Sig) (r s:Fin 152 → Row):=
  ∀ i,bit (r i) T=true ∧ bit (s i) T=false
theorem qbQ {T r s} (h:qcS T r s):Sep T 152 r s (qbP r s):= by
  exact ⟨h,fun a i=> ⟨qbA _ _ _,qbA _ _ _⟩⟩
def q3i (r s:Fin 152 → Row) (x:q08):= x.2=qbP r s x.1
def bv {n:Nat} (d:Nat) (a b:BitVec n):BitVec n:=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d:Nat) (x y:q08):q08:= (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
theorem qbz {n:Nat} (r:Fin n → Row) (d:Nat) (a b:Sig):
    qby r (bin d a b)=bv d (qby r a) (qby r b):= by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:= qbA r (bin d a b) ⟨j,hj⟩
  rw [q1i,←qbA r a ⟨j,hj⟩,←qbA r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem q3j {r s x y} (d) (hx:q3i r s x) (hy:q3i r s y):
    q3i r s (dbin d x y):= by
  change x.2=_ at hx
  change y.2=_ at hy
  simp only [q3i,dbin,qbP,qbz,hx,hy]
def q2O:q08:= (zero,0,0)
theorem q3k (r s):q3i r s q2O:= by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0:Bits).getLsbD j=(qby r zero).getLsbD j
    rw [show (qby r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from qbA _ _ ⟨j,hj⟩,q1v]
    simp
  · change (0:Bits).getLsbD j=(qby s zero).getLsbD j
    rw [show (qby s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from qbA _ _ ⟨j,hj⟩,q1v]
    simp
theorem q3l {r s ws} (all:∀ v ∈ ws,q3i r s v) (i:Nat):
    q3i r s (List.getD ws i q2O):= by
  simp only [List.getD_eq_getElem?_getD]
  cases e:ws[i]? with
  | none=> exact q3k _ _
  | some v=> exact all _ (List.mem_of_getElem? e)
def q2K (n:Nat) (bits:Nat) (ws:List q08):List q08:=
  match n with
  | 0=> ws
  | k+1=>
    let a:= ws.getD (bits &&& 15) q2O
    let b:= ws.getD ((bits >>> 4) &&& 15) q2O
    q2K k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem q2N (n bits) (ws) (r s) (base:∀ v ∈ ws,q3i r s v):
    ∀ v ∈ q2K n bits ws,q3i r s v:= by
  induction n generalizing ws bits with
  | zero=> exact base
  | succ n ih=>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl:= List.mem_singleton.mp hz
      exact q3j _ (q3l base _) (q3l base _)
def q0V (cols:Nat → Bits) (i:Fin 152):Row:=
  (BitVec.ofBoolListLE (List.ofFn (fun j:Fin 9=> (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem q2i:∀ r:Row,bit r (inputs.getD 0 zero)=r.val.testBit 0:= by decide +kernel
theorem q2j:∀ r:Row,bit r (inputs.getD 1 zero)=r.val.testBit 1:= by decide +kernel
theorem q2k:∀ r:Row,bit r (inputs.getD 2 zero)=r.val.testBit 2:= by decide +kernel
theorem q2l:∀ r:Row,bit r (inputs.getD 3 zero)=r.val.testBit 3:= by decide +kernel
theorem q2m:∀ r:Row,bit r (inputs.getD 4 zero)=r.val.testBit 4:= by decide +kernel
theorem q2n:∀ r:Row,bit r (inputs.getD 5 zero)=r.val.testBit 5:= by decide +kernel
theorem q2o:∀ r:Row,bit r (inputs.getD 6 zero)=r.val.testBit 6:= by decide +kernel
theorem q2p:∀ r:Row,bit r (inputs.getD 7 zero)=r.val.testBit 7:= by decide +kernel
theorem q2q:∀ r:Row,bit r (inputs.getD 8 zero)=r.val.testBit 8:= by decide +kernel
theorem q70:∀ (j:Fin 9) (r:Row),
    bit r (inputs.getD j.val zero)=r.val.testBit j.val:= by
  intro j r
  fin_cases j
  · exact q2i r
  · exact q2j r
  · exact q2k r
  · exact q2l r
  · exact q2m r
  · exact q2n r
  · exact q2o r
  · exact q2p r
  · exact q2q r
theorem q0W (cols:Nat → Bits) (i:Fin 152) (j:Fin 9):
    bit (q0V cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:= by
  rw [q70]
  change (BitVec.ofBoolListLE (List.ofFn (fun h:Fin 9=> (cols h.val).getLsbD i.val))).getLsbD j.val=_
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def qcY (m:Nat) (p q:Nat → Bits):List q08:=
  (qdC m).map (fun (j,a)=> (a,p j,q j))
theorem qdD {m j a} (h:(j,a) ∈ qdC m):
    j<9 ∧ a=inputs.getD j zero:= by
  obtain ⟨v,hv,hh⟩:= List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next=>
    cases hh
    exact ⟨hv,rfl⟩
  next=> contradiction
theorem qd0 (m) (p q:Nat → Bits):
    ∀ a ∈ qcY m p q,q3i (q0V p) (q0V q) a:= by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩:= List.mem_map.mp ha
  obtain ⟨hj,rfl⟩:= qdD hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (q0W p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (qbA _ _ ⟨i,hi⟩).symm
  · exact (q0W q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (qbA _ _ ⟨i,hi⟩).symm
def q8W (m:Nat) (v:Nat → Bits):Bits:=
  let x:= fun j=> if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem q1u (m:Nat) (v:Nat → Bits) (i:Fin 152) (j:Fin 9):
    bit (q0V v i) (qgN m j.val)=
    ((if m.testBit j.val then v j.val else 0):Bits).getLsbD i.val:= by
  by_cases hh:m.testBit j.val=true
  · simpa [qgN,hh] using q0W v i j
  · simp [qgN,hh,q1v]
theorem q1k (m:Nat) (v:Nat → Bits) (i:Fin 152):
    bit (q0V v i) (graphGoal m)=(q8W m v).getLsbD i.val:= by
  have pos (j:Nat) (hj:j<9):(qgN m j).getLsbD (q0V v i).val=((if m.testBit j then v j else 0):Bits).getLsbD i.val:= q1u m v i ⟨j,hj⟩
  simp only [bit,graphGoal,q8W,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:= Bits × Bits × Bits
def q0p (z:Bits) (c:Cov):Cov:=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def q2B (d:Bool) (v:List q08):Cov:=
  v.foldr (fun a c=> q0p (q26 d a.2) c) (0,0,0)
def qft (c:Cov) (a:Bits):Bits:= c.1 &&& ~~~(c.2.1 &&& a)
def qfw (c:Cov) (a b:Bits):Bits:=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem q2t (c:Cov) (a:Bits):qft (q0p a c) a=c.1:= by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [qft,q0p,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem q2v (c:Cov) (a b:Bits):qfw (q0p a (q0p b c)) a b=c.1:= by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [qfw,q0p,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem q0q (c:Cov) (a b:Bits):q0p a (q0p b c)=q0p b (q0p a c):= by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [q0p,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [q0p,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem q2u (d:Bool) {l r:List q08} (h:l.Perm r):q2B d l=q2B d r:= by
  induction h with
  | nil=> rfl
  | cons a _ ih=> exact congrArg (q0p (q26 d a.2)) ih
  | swap a b t=> exact q0q _ _ _
  | trans _ _ h1 h2=> exact h1.trans h2
theorem q2w (d:Bool) (v:List q08) {r s} (good:∀ a ∈ v,q3i r s a):
    (q2B d v).1=q2C d (qbP r s) (v.map Prod.fst):= by
  induction v with
  | nil=> rfl
  | cons a v ih=>
    change (q26 d a.2 ||| (q2B d v).1)=q26 d (qbP r s a.1) ||| _
    rw [show a.2=qbP r s a.1 from good _ (by simp),ih (fun a ha=> good a (by simp [ha]))]
def q2P (ws:List q08) (a:q08) (keep:Bool):=
  if keep then ws else ws.erase a
def q2S (ws:List q08) (a b:q08) (ka kb:Bool):=
  q2P (q2P ws a ka) b kb
theorem q2Q {ws:List q08} (a:q08) (ha:a ∈ ws):
    ws.Perm (a::ws.erase a):= List.perm_cons_erase ha
theorem q2x {ws:List q08} (d:Bool) (a:q08) (ha:a ∈ ws) (keep:Bool):
    (q2B d (q2P ws a keep)).1=
      (if keep then (q2B d ws).1 else qft (q2B d ws) (q26 d a.2)):= by
  cases keep
  · change (q2B d (ws.erase a)).1=qft (q2B d ws) _
    rw [q2u d (q2Q a ha)]
    exact (q2t _ _).symm
  · rfl
theorem q2T {ws:List q08} (a b:q08) (ha:a ∈ ws) (hb:b ∈ ws) (hne:a≠b):
    ws.Perm (a::b::(ws.erase a).erase b):= by
  have hm:b ∈ ws.erase a:= (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (q2Q a ha).trans (List.Perm.cons _ (q2Q b hm))
theorem q2A {ws:List q08} (d:Bool) (a b:q08) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:a ≠ b) (ka kb:Bool):
    (q2B d (q2S ws a b ka kb)).1=
      (if ka then (if kb then (q2B d ws).1 else qft (q2B d ws) (q26 d b.2))
       else if kb then qft (q2B d ws) (q26 d a.2)
       else qfw (q2B d ws) (q26 d a.2) (q26 d b.2)):= by
  cases ka <;> cases kb
  · change (q2B d ((ws.erase a).erase b)).1=qfw (q2B d ws) _ _
    rw [q2u d (q2T a b ha hb ne)]
    exact (q2v _ _ _).symm
  · exact q2x d a ha false
  · exact q2x d b hb false
  · rfl
def qdt (a b:List Sig):= (a.all (fun x=> b.contains x)) && (b.all (fun x=> a.contains x))
theorem qdu {xs ys} (h:qdt xs ys=true):xs.toFinset=ys.toFinset:= by
  simp only [qdt,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def q7f (v:Sig):=
  let n:= v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def q7d (xs:List Sig):= xs.foldl (fun v x=> v+q7f x) 0
def q21 (u:Bool) (pools:List q02) (links:Nat → List (List Sig)) (k:Nat)
    (rest:List Sig) (op:q03):=
  let ws:= q1Z op::rest
  (links (q7d ws)).any (qdt ws) || pools.any (fun p=> qdx u p k rest op)
theorem q22 {u raw T pools links k rest op}
    (pValid:∀ p ∈ pools,q0n u raw T p)
    (lValid:∀ tag xs,xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd:(q1Z op::rest).Nodup)
    (h:q21 u pools links k rest op=true):
    Impossible u T k (q1Z op::rest).toFinset:= by
  simp only [q21,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [qdu ok]
    exact lValid _ _ hx
  · exact qdy (pValid _ hp) nd ok
abbrev q06:= Cov × Bool
def qcI (u:Bool) (ws:List q08):q06:= (q2B (!u) ws,u)
def qdf (v:Cov) (a b:Bits) (ka kb:Bool):=
  if ka then (if kb then v.1 else qft v b) else if kb then qft v a else qfw v a b
theorem q2R (ws:List q08) (a:q08) (k:Bool):(q2P ws a k).Sublist ws:= by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem q78 (ws:List q08) (a b:q08) (ka kb:Bool):
    (q2S ws a b ka kb).Sublist ws:= (q2R _ _ _).trans (q2R _ _ _)
theorem q8V (ws:List q08) (a b:q08) (ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b):
    (q2S ws a b ka kb).length=
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1):= by
  have hm:b ∈ ws.erase a:= (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [q2S,q2P,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def qb2 (op:Nat) (a b:q08):q03:= (op,a.1,b.1)
abbrev q0d:= Nat × Nat × List q08 × q06 × List q02 × (Nat → List (List Sig))
def q34 (c:q0d) (op:Nat) (a b z:q08) (ka kb:Bool):=
  let (cap,n,ws,cov,pools,links):= c
  let len:= 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d:= !cov.2
    let rs:= qdf cov.1 (q26 d a.2) (q26 d b.2) ka kb
    if (rs ||| q26 d z.2) !=BitVec.allOnes 152 then true else
    if !qcR z.1 || ws.any (fun v=> v.1==z.1) then true else
      let rest:= (q2S ws a b ka kb).map Prod.fst
      q21 cov.2 pools links (cap-1) rest (qb2 op a b)
def qb1 (ws:List q08) (op:Nat) (a b:q08) (ka kb:Bool):=
  (dbin op a b).1::(q2S ws a b ka kb).map Prod.fst
theorem q35 {u raw T r s ws pools links cap a b op ka kb}
    (pairs:qcS T r s) (faith:∀ w ∈ ws,q3i r s w)
    (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:a≠b) (hcap:0<cap)
    (pv:∀ p ∈ pools,q0n u raw T p)
    (lv:∀ tag xs,xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro:qcQ (dbin op a b).1) (fresh:(dbin op a b).1 ∉ ws.map Prod.fst)
    (test:q34 (cap,ws.length,ws,qcI u ws,pools,links) op a b (dbin op a b) ka kb=true):
    Impossible u T (cap-1) (qb1 ws op a b ka kb).toFinset:= by
  let z:= dbin op a b
  let rest:= q2S ws a b ka kb
  let child:= z.1::rest.map Prod.fst
  have sub:rest.Sublist ws:= q78 _ _ _ _ _
  have ndc:child.Nodup:= List.nodup_cons.mpr ⟨fun hm=> fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr:ws.any (fun v=> v.1==z.1)=false:= by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩:= List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp:qcR z.1=true:= by simpa [qcR,qcQ] using pro
  have leq:1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1))=child.length:= by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,q8V _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz:= q98 h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len:child.length ≤ cap:= by omega
  unfold q34 at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  have sep:= q2y h (qbQ pairs)
  let d:= !u
  have g:(q2B d rest).1=q2C d (qbP r s) (rest.map Prod.fst):=
    q2w _ _ (fun v hv=> faith _ (sub.subset hv))
  have rz:(q2B d rest).1=qdf (q2B d ws) (q26 d a.2) (q26 d b.2) ka kb:=
    q2A d a b ha hb ne ka kb
  have hf:= q3j op (faith _ ha) (faith _ hb)
  change q26 d (qbP r s z.1) ||| q2C d (qbP r s) (rest.map Prod.fst)=_ at sep
  change z.2=qbP r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be:((qdf (q2B (!u) ws) (q26 (!u) a.2) (q26 (!u) b.2) ka kb ||| q26 (!u) z.2) !=BitVec.allOnes 152)=false:= by
    simpa using sep
  change (if (qdf (q2B (!u) ws) (q26 (!u) a.2) (q26 (!u) b.2) ka kb ||| q26 (!u) z.2) !=BitVec.allOnes 152 then true else if !qcR z.1 || ws.any (fun v=> v.1==z.1) then true else _)=true at test
  rw [be,pp,fr] at test
  exact q22 (op:= qb2 op a b) (rest:= rest.map Prod.fst) pv lv ndc test k hk h
def qfz (ctx:q0d) (a b:q08) (op:Nat):=
  let z:= dbin op a b
  let attempt:= q34 ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def qbF (u:Bool):List Nat:= if u then [0,1,2,3] else [0,1]
theorem qbG {u d} (h:q0N u d):d ∈ qbF u:= by
  rcases q0Q h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [qbF]
  · cases u <;> simp [qbF]
  · simp [qbF]
  · simp [qbF]
def qfB (ctx:q0d) (a:q08) (bs:List q08):=
    bs.all (fun b=> (qbF ctx.2.2.2.1.2).all (qfz ctx a b))
def qfy (ctx:q0d):List q08 → Bool
  | []=> true
  | a::bs=> qfB ctx a bs && qfy ctx bs
theorem q0s {ctx ws} (h:qfy ctx ws=true) {a b:q08} (ha:a∈ws) (hb:b∈ws)
    (ne:a≠b):(∀ d,q0N ctx.2.2.2.1.2 d → qfz ctx a b d=true) ∨
      (∀ d,q0N ctx.2.2.2.1.2 d → qfz ctx b a d=true):= by
  induction ws with
  | nil=> simp at ha
  | cons w ws ih=>
    simp only [qfy,Bool.and_eq_true,qfB,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm:= (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd=> h.1 b bm d (qbG hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd=> h.1 a haTail d (qbG hd)
      · exact ih h.2 haTail hbTail
theorem qfA {ctx a b d} (h:qfz ctx a b d=true) (ka kb:Bool):
    q34 ctx d a b (dbin d a b) ka kb=true:= by
  simp only [qfz,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem q77 {v:List Sig} {w:Sig} (a:Sig) (k:Bool):
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v:= by cases k <;> simp [kept]
theorem qaB {v:List q08} (nd:v.Nodup) (a w:q08) (k:Bool):
    w ∈ q2P v a k ↔ w∈v ∧ (w≠a ∨ k=true):= by
  cases k <;> simp [q2P,nd.mem_erase_iff,and_comm]
theorem qfG {ws:List q08} (nd:(ws.map Prod.fst).Nodup) {a b:q08}
    (ha:a∈ws) (hb:b∈ws) (eq:a.1=b.1):a=b:= by
  induction ws with
  | nil=> simp at ha
  | cons w ws ih=>
    obtain ⟨hn,ht⟩:= List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
theorem q7c {ws:List q08} (nd:(ws.map Prod.fst).Nodup) {a b:q08}
    (ha:a ∈ ws) (hb:b ∈ ws) (ka kb:Bool) (v:Sig):
    v ∈ (q2S ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true):= by
  have wn:= nd.of_map
  have dn:= wn.sublist (q2R ws a ka)
  simp only [q2S,List.mem_map,qaB wn,qaB dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq=> ne (qfG nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq=> ne (qfG nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq=> ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq=> ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem q1h {ws:List q08} (nd:(ws.map Prod.fst).Nodup) {a b:q08}
    (ha:a∈ws) (hb:b∈ws) (ne:a.1≠b.1) (d:Nat) (ka kb:Bool):
    (qb1 ws d a b ka kb).toFinset=
      (q1W (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:= by
  ext v
  have av:= List.mem_map_of_mem (f:= Prod.fst) ha
  have bv':= List.mem_map_of_mem (f:= Prod.fst) hb
  simp only [qb1,q1W,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    q7c nd ha hb,q77,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va:v=a.1 <;> by_cases vb:v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem q1X {u} (v:List Sig) (nd:v.Nodup) (a b:Sig) (d:Nat) (hd:q0N u d) (ka kb:Bool):
    (q1W v a b d ka kb).toFinset=(q1W v b a (q3v d) kb ka).toFinset:= by
  ext x
  simp only [q1W,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    q77,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,q1e hd a b]
  tauto
theorem qbk {u raw T r s ws pools links cap}
    (pairs:qcS T r s) (faith:∀ w ∈ ws,q3i r s w)
    (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst)
    (pv:∀ p ∈ pools,q0n u raw T p)
    (lv:∀ tag xs,xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks:qfy (cap,ws.length,ws,qcI u ws,pools,links) ws=true):
    Impossible u T cap (ws.map Prod.fst).toFinset:= by
  by_cases hc:cap=0
  · intro k hk h
    have ke:k=0:= by omega
    subst k
    generalize he:(ws.map Prod.fst).toFinset=S at h
    obtain ⟨hS,_⟩:= h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc':0<cap:= by omega
  apply q2Z nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩:= List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩:= List.mem_map.mp hb
  have ab:a≠b:= fun e=> ne (congrArg Prod.fst e)
  have one (a b:q08) (d:Nat) (aa:a∈ws) (bb:b∈ws) (ne':a.1≠b.1) (ka kb:Bool)
      (pr:qcQ (bin d a.1 b.1)) (fr:bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test:qfz (cap,ws.length,ws,qcI u ws,pools,links) a b d=true):
      Impossible u T (cap-1) (q1W (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:= by
    rw [←q1h nd aa bb ne']
    exact q35 pairs faith nd aa bb (fun e=> ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (qfA test ka kb)
  rcases q0s checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [q1X _ nd _ _ d hd]
    exact one b a (q3v d) hbW haW (Ne.symm ne) kb ka (q1e hd a.1 b.1 ▸ pro)
      (q1e hd a.1 b.1 ▸ fresh) (hh _ (q3w hd).1)
theorem q0r (r s:Row) (h:∀ a ∈ inputs,bit r a=bit s a):r=s:= by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj:j<9
  · let i:Fin 9:= ⟨j,hj⟩
    have hm:inputs.getD i.val zero ∈ inputs:= by
      rw [← q71]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (q70 i r).symm.trans ((h _ hm).trans (q70 i s))
  · have le:512 ≤ 2^j:= by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def q2b (p q:List Move):= inputs.all (fun a=> qb5 p (qb5 q a)==a)
theorem q2c {p q} (h:q2b p q=true) (r:Row):
    qb4 q (qb4 p r)=r:= by
  apply q0r
  intro a ha
  rw [←q1m,←q1m]
  have eq:= beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def q0X (T:Sig) (p:List Move):=
  (qb5 p T==T) && q2b p p.reverse && q2b p.reverse p
theorem qdl {u T n} {ws:List Sig} (hi:Impossible u T n ws.toFinset)
    (p:List Move) (ok:q0X T p=true):Impossible u T n (ws.map (qb5 p.reverse)).toFinset:= by
  simp only [q0X,Bool.and_eq_true,beq_iff_eq] at ok
  have onto:Function.Surjective (qb4 p):= fun r=> ⟨qb4 p.reverse r,q2c ok.2 r⟩
  intro k hk h
  have run:= q96 h (qb4 p) onto
  have goal:qd7 (qb4 p) T=T:= (qb6 p T).symm.trans ok.1.1
  have inv (x:Sig):qd7 (qb4 p) (qb5 p.reverse x)=x:= by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [q1r,q1m,q2c ok.1.2]
  have back:(ws.map (qb5 p.reverse)).toFinset.image (qd7 (qb4 p))=ws.toFinset:= by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run
abbrev q0g:= Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def q2Y:q0g:= (0,0,0,0,0,0,0,fun _=> 0)
def qbI (word:Nat → Nat) (pos len:Nat):=
  let i:= pos/8192
  let shift:= pos % 8192
  let lo:= word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def q9a (nb slots sw vw iw pw:Nat) (data:Nat → Nat) (h:Nat):Option (Nat × Nat):=
  let a:= h % nb
  let sh:= qbI data (a*sw) sw
  let row:= (h/nb+sh) % slots
  let word:= qbI data (nb*sw+row*vw) vw
  if (word >>> (iw+pw))==h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def q99 (nb slots sw vw iw pw:Nat) (data:Nat → Nat) (h:Nat):Option (Nat × Nat):=
  let a:= h % nb
  let sh:= qbI data (a*sw) sw
  let row:= (h/nb+sh) % slots
  let word:= qbI data (nb*sw+row*vw) vw
  if (word >>> (iw+pw))==h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
abbrev q0a:= Nat × Nat × (Nat → Bits × Bits) × List q04 × List (List Nat) ×
  (Nat → q0g) × (Nat → Nat → Option (Nat × Nat))
def q0a.mask (g:q0a):Nat:= g.1
def q0a.mode (g:q0a):Bool:= !(g.1.testBit 10)
def q0a.cap (g:q0a):Nat:= g.2.1
def q0a.samples (g:q0a):Nat → Bits × Bits:= g.2.2.1
def q0a.cols (g:q0a):List q04:= g.2.2.2.1
def q0a.autos (g:q0a):List (List Nat):= g.2.2.2.2.1
def q0a.levels (g:q0a):Nat → q0g:= g.2.2.2.2.2.1
def q0a.index (g:q0a):Nat → Nat → Option (Nat × Nat):= g.2.2.2.2.2.2
def qgQ (g:q0a):=
  let ws:= qcY g.mask (fun j=> (g.samples j).1) (fun j=> (g.samples j).2)
  ws
theorem qgR (g:q0a):∀ a ∈ qgQ g,
    q3i (q0V fun j=> (g.samples j).1) (q0V fun j=> (g.samples j).2) a:= by
  exact qd0 g.mask (fun j=> (g.samples j).1) (fun j=> (g.samples j).2)
def qfx (g:q0a):= q1M g.mask
def q1N (m:Nat) (v:Nat → Bits):=
  q8W m v
theorem q1O (m:Nat) (v:Nat → Bits) (i:Fin 152):
    bit (q0V v i) (q1M m)=(q1N m v).getLsbD i.val:= by
  exact q1k m v i
theorem q1P {m:Nat} {p q:Nat → Bits}
    (hp:q1N m p=BitVec.allOnes 152) (hq:q1N m q=0):
    qcS (q1M m) (q0V p) (q0V q):= by
  intro i
  simp only [q1O,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def qdz {α:Type} (bits:Nat):List α → List α
  | []=> []
  | w::ws=> if bits &&& 1==1 then w::qdz (bits >>> 1) ws else qdz (bits >>> 1) ws
theorem qdB {α:Type} (bits:Nat) (ws:List α):(qdz bits ws).Sublist ws:= by
  induction ws generalizing bits with
  | nil=> exact List.Sublist.slnil
  | cons a ws ih=>
    unfold qdz
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def qcJ (d:Nat):= 10*(d-1)
def q2W (d flags:Nat):= flags % 16 + (if d=0 then 0 else 10) + flags/16
def q2V (d raw dict:Nat):=
  (dict % 65536)*qcJ d + (dict/65536)*(raw+d)
def q3K (tab:q0g) (raw i:Nat):Nat:=
  let (_,d,_,dict,flags,_,marker,word):= tab
  let width:= 10*d+raw+d
  if marker<1024 then qbI word (i*width) width else
    let off:= q2V d raw dict+i*q2W d flags
    let pre:= qbI word off (flags % 16)
    let lastBits:= if d=0 then 0 else 10
    let last:= qbI word (off+flags % 16) lastBits
    let mask:= qbI word (off+flags % 16+lastBits) (flags/16)
    let base:= (dict % 65536)*qcJ d
    qbI word (pre*qcJ d) (qcJ d) |||
      (last <<< qcJ d) ||| (qbI word (base+mask*(raw+d)) (raw+d) <<< (10*d))
def qeX (_g:q0a) (depth:Nat):= depth
def qd5 (g:q0a) (k i:Nat):Nat × List q08 × List q08:=
  let raw:= qgQ g
  let (_,depth,_,_,_,_,_,data):= g.levels k
  let len:= 10*qeX g depth
  let width:= len+raw.length+depth
  let recp:= q3K (g.levels k) raw.length i
  let stored:= recp &&& ((1 <<< len)-1)
  let ops:= stored
  let bank:= q2K depth ops raw
  (ops,bank,qdz (recp >>> len) bank)
def q5z (x pos width:Nat):= (x >>> pos) &&& ((1 <<< width)-1)
def q20 (bank:List q08) (ops paid:Nat):Nat → List q03
  | 0=> []
  | n+1=>
    let more:= q20 bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1==0 then more else
      (q5z ops 8 2,(bank.getD (ops &&& 15) q2O).1,
        (bank.getD (q5z ops 4 4) q2O).1)::more
def q1E (g:q0a) (ops d:Nat) (bank:List q08) (idx paid:Nat):Option q02:=
  (g.cols[idx]?).bind fun ci=>
    qaz g.mode (qgM (qcZ g.mask ci)) (q20 bank ops paid d) (qeZ ci.1 ci.2.1) ci.2.2.2.2
theorem q1F (g:q0a)
    (cols:∀ ci ∈ g.cols,q0l g.mode (qgM (qcZ g.mask ci)) (qfx g) (qeZ ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h:q1E g ops depth bank i paid=some c):
    q0n g.mode (vars g.mask) (qfx g) c:= by
  unfold q1E at h
  cases e:g.cols[i]? with
  | none=> simp [e] at h
  | some ci=>
    simp only [e,Option.bind_some] at h
    apply qaA _ h
    exact cols ci (List.mem_of_getElem? e)
def q5A (data:Nat → Nat) (w v:Nat):Nat → Nat → List (Nat × Nat)
  | 0,_=> []
  | n+1,pos=>
    let x:= qbI data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w)::q5A data w v n (pos+w+v)
def q3z {α:Type}:Nat → (Nat → α) → α
  | 0,next=> next 0
  | n+1,next=> next (n+1)
def qd6 (data:Nat → Nat) (dict cw d gapBits:Nat):
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_=> []
  | left+1,st,first=>
    q3z st fun pos=> q3z first fun base=>
    q3z (qbI data pos 32) fun head=>
    q3z (Nat.log2 (head ^^^ (head+1))) fun ones=>
    q3z (base+(ones <<< gapBits)+qbI data (pos+ones+1) gapBits) fun key=>
    q3z (qbI data (dict+key*(cw+d)) (cw+d)) fun pair=>
      (pair &&& ((1 <<< cw)-1),pair >>> cw)::
        qd6 data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)
def qcP {α:Type} (a b:Nat) (xs:List α):List α:=
  let rec collect:List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other=> first ++ second ++ other.reverse
    | x::tail,i,first,second,other=>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []
def q3J (tab:q0g) (raw i:Nat):List (Nat × Nat):=
  let (num,d,cw,dict,flags,ow,marker,data):= tab
  if marker<1024 then
    let start:= num*(10*d+raw+d)
    let pos:= start+num*ow+qbI data (start+i*ow) ow
    q5A data cw d (qbI data pos 5) (pos+5+marker)
  else
    let off:= q2V d raw dict + num*q2W d flags
    let pairs:= off+num*ow
    let priority:= decide (4096≤marker)
    let pos:= pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+qbI data (off+i*ow) ow
    let n:= qbI data pos 5
    let gap:= qbI data (pos+5) 3
    if !priority || decide (n≤1) then qd6 data pairs cw d gap n (pos+8) 0 else
      let width:= (n-1).log2+1
      let a:= qbI data (pos+8) width
      let b:= if n=2 then 1-a else qbI data (pos+8+width) width
      let extra:= if n=2 then width else 2*width
      let xs:= qd6 data pairs cw d gap n (pos+8+extra) 0
      qcP a b xs
def qeW (g:q0a) (k i:Nat):= (qd5 g k i).2.2.map Prod.fst
def q91 (g:q0a) (k:Nat) (pair:Nat × Nat):Option (List Sig):=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm=> (qeW g k pair.1).map (qb5 (perm.map qf4).reverse)
theorem q92 (g:q0a) (k:Nat)
    (names:∀ x ∈ g.autos,q0X (qfx g) (x.map qf4)=true)
    (earlier:∀ i < (g.levels k).1,Impossible g.mode (qfx g) k (qeW g k i).toFinset)
    {pair out} (h:q91 g k pair=some out):
    Impossible g.mode (qfx g) k out.toFinset:= by
  unfold q91 at h
  split at h
  · contradiction
  next valid=>
    cases e:g.autos[pair.2]? with
    | none=> simp [e] at h
    | some perm=>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact qdl (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def qbi (g:q0a) (k i:Nat):=
  let raw:= qgQ g
  let (num,depth,cw,iw,pw,offw,lw,data):= g.levels k
  let (ops,bank,ws):= qd5 g k i
  let values:= ws.map Prod.fst
  let rules:= (q3J (g.levels k) raw.length i).filterMap (fun (a,b)=> q1E g ops depth bank a b)
  let ls:= fun tag=> ((g.index k tag).bind (q91 g (k-1))).toList
  decide values.Nodup && !(values.contains (qfx g)) &&
    (if k=0 then true else qfy (k,ws.length,ws,qcI g.mode ws,rules,ls) ws)
theorem qbj (g:q0a) (k i:Nat)
    (samples:qcS (qfx g) (q0V fun j=> (g.samples j).1) (q0V fun j=> (g.samples j).2))
    (cols:∀ ci ∈ g.cols,q0l g.mode (qgM (qcZ g.mask ci)) (qfx g) (qeZ ci.1 ci.2.1) ci.2.2.2.2)
    (names:∀ x ∈ g.autos,q0X (qfx g) (x.map qf4)=true)
    (prior:k>0 → ∀ j < (g.levels (k-1)).1,Impossible g.mode (qfx g) (k-1) (qeW g (k-1) j).toFinset)
    (checked:qbi g k i=true):Impossible g.mode (qfx g) k (qeW g k i).toFinset:= by
  simp only [qbi,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN:= checked.1.1
  have hT:qfx g ∉ qeW g k i:= by simpa [qeW] using checked.1.2
  by_cases h0:k=0
  · subst k
    intro t lo h
    have ht:t=0:= by omega
    subst t
    generalize he:(qeW g 0 i).toFinset=S at h
    obtain ⟨hS,_⟩:= h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply qbk (raw:= vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply q2N _ _ _ _ _ (qgR g) v
    exact (qdB _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:= List.mem_filterMap.mp hp
    exact q1F g cols h
  · intro tag xs hx
    have e:((g.index k tag).bind (q91 g (k-1)))=some xs:= by simpa using hx
    obtain ⟨pair,_,h⟩:= Option.bind_eq_some_iff.mp e
    exact q92 g _ names (prior (by omega)) h
def q1w (g:q0a) (k start:Nat):Nat → Bool
  | 0=> true
  | n+1=> qbi g k (start+n) && q1w g k start n
theorem q1x {g k start n} (h:q1w g k start n=true) (j:Nat) (lo:start≤j) (hi:j<start+n):
    qbi g k j=true:= by
  induction n with
  | zero=> omega
  | succ n ih=>
    simp only [q1w,Bool.and_eq_true] at h
    by_cases eq:j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem q1y {g k start a b} (h:q1w g k start a=true)
    (h':q1w g k (start+a) b=true):q1w g k start (a+b)=true:= by
  induction b with
  | zero=> simpa using h
  | succ b ih=>
    simp only [q1w,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,q1w,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def q1V (g:q0a) (top:Nat):=
  ∀ k ≤ top,q1w g k 0 (g.levels k).1=true
def q5D (g:q0a) (prior:Nat → Nat):=
  (q1N g.mask (fun j=> (g.samples j).1)==BitVec.allOnes 152) &&
  (q1N g.mask (fun j=> (g.samples j).2)==0) &&
  g.cols.all (fun c=> q23 g.mask c prior) &&
  g.autos.all (fun p=> q0X (qfx g) (p.map qf4))
theorem q3L (g:q0a) (top:Nat) (prior:Nat → Nat)
    (lower:∀ q,Lower g.mode (qgM q) (graphGoal q) (prior q))
    (geometry:q5D g prior=true) (rows:q1V g top):
    ∀ k ≤ top,∀ i < (g.levels k).1,Impossible g.mode (qfx g) k (qeW g k i).toFinset:= by
  simp only [q5D,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero=>
    intro hk i hi
    apply qbj g 0 i (q1P geometry.1.1.1 geometry.1.1.2)
      (fun x hx=> q25 _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact q1x (rows 0 hk) i (by omega) (by omega)
  | succ k ih=>
    intro hk i hi
    apply qbj g _ i (q1P geometry.1.1.1 geometry.1.1.2)
      (fun x hx=> q25 _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _=> by simpa using ih (by omega))
    exact q1x (rows _ hk) i (by omega) (by omega)
def q6X (g:q0a) (k i:Nat) (ws:List Sig):=
  decide (i < (g.levels k).1) && qdt (qeW g k i) ws
theorem qdk {g top prior k i ws} (low:∀ q,Lower g.mode (qgM q) (graphGoal q) (prior q))
    (geom:q5D g prior=true) (blocks:q1V g top) (le:k ≤ top)
    (idx:q6X g k i ws=true):Impossible g.mode (qfx g) k ws.toFinset:= by
  simp only [q6X,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←qdu idx.2]
  exact q3L g top prior low geom blocks _ le i idx.1
def Known (u:Bool) (entries:List (Nat × Nat)):= ∀ e ∈ entries,Lower u (qgM e.1) (graphGoal e.1) e.2
def q38 (old:List (Nat × Nat)) (L:Nat) (carries:List (Nat × List Nat)):=
  carries.map (fun v=> (v.1,L)) ++ old
theorem q3a {u old L m carries} (previous:Known u old)
    (main:Lower u (qgM m) (graphGoal m) L)
    (ok:carries.all (fun v=> q1H v.1 m v.2)=true):
    Known u (q38 old L carries):= by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩:= List.mem_map.mp hx
    exact q1I (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem q15:Known true []:= by simp [Known]
def q8O (v:Nat) (upper:Nat):= 2^153*upper+v
def q2a {α:Type} (f:α → Bits):List α → Nat
  | []=> 0
  | x::xs=> q8O (f x).toNat (q2a f xs)
def qfI:Nat → Nat
  | 0=> 0
  | n+1=> q8O 1 (qfI n)
theorem q8P (x:Bits):x.toNat < 2^153:=
  lt_trans x.isLt (by decide +kernel)
theorem qcz (a b:Bits) (u v:Nat):
    q8O a.toNat u &&& q8O b.toNat v=q8O (a &&& b).toNat (u &&& v):= by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [q8O,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (q8P _)]
  by_cases h:i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem qcA (a b:Bits) (u v:Nat):
    q8O a.toNat u ||| q8O b.toNat v=q8O (a ||| b).toNat (u ||| v):= by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [q8O,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (q8P _)]
  by_cases h:i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem qcB (a b:Bits) (u v:Nat):
    q8O a.toNat u ^^^ q8O b.toNat v=q8O (a ^^^ b).toNat (u ^^^ v):= by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [q8O,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (q8P _)]
  by_cases h:i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem q8S {α} (f g:α → Bits) (xs):
    q2a f xs &&& q2a g xs=q2a (fun x=> f x &&& g x) xs:= by
  induction xs with
  | nil=> simp [q2a]
  | cons a xs ih=> simp only [q2a,qcz,ih]
theorem q8T {α} (f g:α → Bits) (xs):
    q2a f xs ||| q2a g xs=q2a (fun x=> f x ||| g x) xs:= by
  induction xs with
  | nil=> simp [q2a]
  | cons a xs ih=> simp only [q2a,qcA,ih]
theorem q8U {α} (f g:α → Bits) (xs):
    q2a f xs ^^^ q2a g xs=q2a (fun x=> f x ^^^ g x) xs:= by
  induction xs with
  | nil=> simp [q2a]
  | cons a xs ih=> simp only [q2a,qcB,ih]
def q3T (r packed:Nat):= ((packed+r) >>> 152) &&& r
theorem qfH (n i:Nat) (hi:i<n):(qfI n).testBit (153*i)=true:= by
  induction n generalizing i with
  | zero=> omega
  | succ n ih=>
    rw [qfI,q8O,Nat.testBit_two_pow_mul_add _ (by decide +kernel:1 < 2^153)]
    cases i with
    | zero=> simp
    | succ i=>
      have di:153*(i+1)-153=153*i:= by omega
      have ge:¬153*(i+1)<153:= by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem q5F (a:Bits):(a.toNat+1).testBit 152=(a==BitVec.allOnes 152):= by
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
theorem qao {α} (f:α → Bits) (xs:List α) (i:Nat) (hi:i<xs.length):
    (q3T (qfI xs.length) (q2a f xs)).testBit (153*i)=
      (f xs[i]==BitVec.allOnes 152):= by
  simp only [q3T,Nat.testBit_and,Nat.testBit_shiftRight,qfH _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil=> simp at hi
  | cons a xs ih=>
    simp only [q2a,List.length_cons,qfI,q8O]
    have sum (u v x:Nat):2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1):= by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have:= (f a).isLt; omega)]
    have hi':i < xs.length+1:= hi
    cases i with
    | zero=> simpa using q5F (f a)
    | succ i=>
      have ge:¬153*(i+1)+152<153:= by omega
      have di:153*(i+1)+152-153=153*i+152:= by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev q0f:= Nat × Nat
abbrev q0e:= Nat × Nat × Nat
def qbM {α} (s:α → q0j) (xs:List α):q0f:=
  (q2a (fun x=> (s x).1) xs,q2a (fun x=> (s x).2) xs)
def qbK {α} (c:α → Cov) (xs:List α):q0e:=
  (q2a (fun x=> (c x).1) xs,q2a (fun x=> (c x).2.1) xs,
   q2a (fun x=> (c x).2.2) xs)
def qbJ (d:Bool) (a:q0f):=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem qjy (a b:Bits):a ^^^ (a &&& b)=a &&& ~~~b:= by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem qbN {α} (s:α → q0j) (xs:List α) (d:Bool):
    qbJ d (qbM s xs)=q2a (fun x=> q26 d (s x)) xs:= by
  cases d <;> simp only [qbJ,qbM,q26,Bool.false_eq_true,ite_false,ite_true,q8S,q8U,qjy]
def qbL (op:Nat) (a b:q0f):q0f:=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem qbO {α} (a b:α → q08) (xs:List α) (op:Nat):
    qbL op (qbM (fun x=> (a x).2) xs) (qbM (fun x=> (b x).2) xs)=
    qbM (fun x=> (dbin op (a x) (b x)).2) xs:= by
  by_cases h0:op=0
  · simp only [qbL,h0,ite_true,qbM,q8S,dbin,bv]
  by_cases h1:op=1
  · simp [qbL,h1,qbM,q8T,dbin,bv]
  by_cases h2:op=2
  · simp [qbL,h2,qbM,q8S,q8U,qjy,dbin,bv]
  · have e (x y:Bits): ~~~x &&& y=y &&& ~~~x:= BitVec.and_comm _ _
    simp only [qbL,h0,h1,h2,ite_false,qbM,q8S,q8U,qjy,dbin,bv,e]
def qfu (c:q0e) (a b:Nat) (ka kb:Bool):=
  let without1:= fun w=> c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2:= c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem qfv {α} (c:α → Cov) (a b:α → Bits) (xs:List α) (ka kb:Bool):
    qfu (qbK c xs) (q2a a xs) (q2a b xs) ka kb=
    q2a (fun x=> qdf (c x) (a x) (b x) ka kb) xs:= by
  cases ka <;> cases kb <;>
    simp only [qfu,qbK,q8S,q8T,q8U,qjy,qdf,qft,qfw,
      Bool.false_eq_true,ite_false,ite_true]
def q2f (c:q0d) (i:Nat):= c.2.2.1.getD i q2O
def q1Q (c:q0d) (i j op:Nat) (ka kb:Bool):=
  let a:= q2f c i
  let b:= q2f c j
  q34 c op a b (dbin op a b) ka kb
def q27 (c:q0d) (d ka kb:Bool) (op i j:Nat):=
  let a:= q2f c i
  let b:= q2f c j
  qdf c.2.2.2.1.1 (q26 d a.2) (q26 d b.2) ka kb |||
    q26 d (dbin op a b).2
def qbB {α:Type} (f:α → Bool) (mask:Nat):List α → Bool
  | []=> true
  | x::xs=> if mask=0 then true else
    ((mask &&& 1==0) || f x) && qbB f (mask >>> 153) xs
theorem qap {α} (f:α → Bool) (mask:Nat) (xs:List α) (i:Nat) (hi:i<xs.length)
    (bitOn:mask.testBit (153*i)=true) (ok:qbB f mask xs=true):f xs[i]=true:= by
  induction xs generalizing mask i with
  | nil=> simp at hi
  | cons x xs ih=>
    have ne:mask≠0:= by intro e; simp [e] at bitOn
    simp only [qbB,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero=>
      have nonzero:mask &&& 1 ≠ 0:= by
        intro he
        have at0:= congrArg (fun n:Nat=> n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i=>
      apply ih (mask:= mask >>> 153) (i:= i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev q01:= Nat × Nat × Nat × List q0f × q0e
def qai (k n:Nat) (xs:List q0d):q01:=
  (k,n,qfI xs.length,(List.range n).map (fun i=> qbM (fun c=> (q2f c i).2) xs),
    qbK (fun c=> c.2.2.2.1.1) xs)
def q8Q (b:q01) (i:Nat):= b.2.2.2.1.getD i (0,0)
theorem q8R (k n) (xs) {i:Nat} (h:i<n):
    q8Q (qai k n xs) i=qbM (fun c=> (q2f c i).2) xs:= by
  simp [q8Q,qai,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem qar (d x:Sig):qaq d (neg x)=d ^^^ qaq d x:= by
  apply q1j
  intro r
  simp only [qaq,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def q2d (p:q08 → Bool) (a:q08) (keep:Bool):=
  if keep then 0 else (p a).toNat
theorem q9b (p:q08 → Bool) (ws:List q08) (a:q08) (keep:Bool):
    ws.countP p ≤ (q2P ws a keep).countP p + q2d p a keep:= by
  cases keep
  · simp only [q2P,Bool.false_eq_true,ite_false,q2d,List.countP_erase]
    split
    next h=> simp [h.2]; omega
    next=> omega
  · simp [q2P,q2d]
theorem q79 (p:q08 → Bool) (ws:List q08) (a b:q08) (ka kb:Bool):
    ws.countP p - q2d p a ka - q2d p b kb ≤
    (q2S ws a b ka kb).countP p:= by
  have h1:= q9b p ws a ka
  have h2:= q9b p (q2P ws a ka) b kb
  simp only [q2S]
  omega
noncomputable def q3x {β:Type} (n:Nat) (f:Nat → β):β:= Nat.rec (f 0) (fun k _=> f (Nat.succ k)) n
theorem q3I {β:Type} (n:Nat) (f:Nat → β):q3x n f=f n:= by cases n <;> rfl
noncomputable def q3C {α β:Type} (f:α → Nat) (l:List α):(List Nat → β) → β:=
  List.rec (fun k=> k []) (fun a _ ih k=> q3x (f a) fun x=> ih fun xs=> k (x::xs)) l
theorem q3D {α β:Type} (f:α → Nat) (l:List α) (k:List Nat → β):q3C f l k=k (l.map f):= by
  induction l generalizing k with
  | nil=> rfl
  | cons a l ih=>
    change q3x (f a) (fun x=> q3C f l fun xs=> k (x::xs))=_
    rw [q3I,ih]
    rfl
def qbg (d:Nat) (a:Sig):Nat:= Nat.land a.toNat d
noncomputable def q0S (m:Nat) (l:List Nat):Bool:= List.rec false (fun v _ ih=> or (Nat.beq m v) ih) l
def qb9 (d m:Nat):Bool:= or (Nat.beq m 0) (Nat.beq m d)
noncomputable def qb7 (u:Bool) (d:Nat) (pm:List Nat) (m:Nat):Bool:=
  or (or (qb9 d m) (q0S m pm)) (and u (q0S (Nat.xor d m) pm))
theorem qbh (d a:Sig):qbg d.toNat a=(qaq d a).toNat:= (BitVec.toNat_and _ _).symm
theorem q1d (a b:Sig):Nat.beq a.toNat b.toNat=(a==b):= by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem qba (d a:Sig):qb9 d.toNat (qbg d.toNat a)=q74 d a:= by
  rw [qbh]
  have e:Nat.beq (qaq d a).toNat 0=(qaq d a==zero):= by
    have z0:zero.toNat=0:= by simp [zero]
    rw [←q1d,z0]
  rw [qb9,e,q1d]
  rfl
theorem q0T (x d:Sig) (pool:List Sig):q0S x.toNat (pool.map (qbg d.toNat))=(pool.map (qaq d)).any (fun v=> v==x):= by
  induction pool with
  | nil=> rfl
  | cons a l ih=>
    change or (Nat.beq x.toNat (qbg d.toNat a)) (q0S x.toNat (l.map (qbg d.toNat)))=_
    rw [ih,qbh,q1d,List.map_cons,List.any_cons,Bool.beq_comm]
theorem qb8 (u:Bool) (d a:Sig) (pool:List Sig):
    qb7 u d.toNat (pool.map (qbg d.toNat)) (qbg d.toNat a)=q0Z u d pool a:= by
  have x:Nat.xor d.toNat (qaq d a).toNat=(qaq d (neg a)).toNat:= by
    rw [qar]
    exact (BitVec.toNat_xor _ _).symm
  rw [qb7,qba,qbh,x,q0T,q0T]
  simp only [q0Z,q74]
def unav (u:Bool) (p:q02) (w:q08):Nat:= cond (q0Z u p.domain p.wires w.1) 0 1
def qeU (u:Bool) (p:q02) (ws:List q08) (k:Nat) (a b:q08) (op:Nat) (ka kb:Bool):Bool:=
  let const:= fun w:q08=> q74 p.domain w.1
  let z:= bin op a.1 b.1
  let cm:= ws.countP const - q2d const a ka - q2d const b kb + (q74 p.domain z).toNat
  (((ws.map (unav u p)).sum==cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!q0Z u p.domain p.wires z).toNat < p.bound+cm)) &&
    (q0Z u p.domain p.wires z || (q0Z u p.domain p.wires a.1 && q0Z u p.domain p.wires b.1))
def zN (op x y:Nat):Nat:= cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem qjz (op:Nat) (d a b:Sig):zN op (qbg d.toNat a) (qbg d.toNat b)=qbg d.toNat (bin op a b):= by
  have tn (x y:Sig):Nat.land x.toNat y.toNat=(x &&& y).toNat:= (BitVec.toNat_and x y).symm
  have tx (x y:Sig):Nat.xor x.toNat y.toNat=(x ^^^ y).toNat:= (BitVec.toNat_xor x y).symm
  have tor (x y:Sig):Nat.lor x.toNat y.toNat=(x ||| y).toNat:= (BitVec.toNat_or x y).symm
  simp only [qbh]
  unfold zN
  by_cases h0:op=0
  · subst h0
    change Nat.land _ _=_
    rw [tn]
    congr 1
    apply q1j
    intro r
    simp only [qaq,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1:op=1
  · subst h1
    change Nat.lor _ _=_
    rw [tor]
    congr 1
    apply q1j
    intro r
    simp only [qaq,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0:Nat.beq op 0=false:= Bool.eq_false_iff.mpr (fun h=> h0 (Nat.eq_of_beq_eq_true h))
  have e1:Nat.beq op 1=false:= Bool.eq_false_iff.mpr (fun h=> h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2:op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _)=_
    rw [tn,tx]
    congr 1
    apply q1j
    intro r
    simp only [qaq,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2:Nat.beq op 2=false:= Bool.eq_false_iff.mpr (fun h=> h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _)=_
  rw [tn,tx]
  congr 1
  apply q1j
  intro r
  simp only [qaq,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def qbe (d x:Nat) (keep:Bool):Nat:= cond keep 0 (cond (qb9 d x) 1 0)
theorem qbf (d:Sig) (a:q08) (keep:Bool):
    qbe d.toNat (qbg d.toNat a.1) keep=q2d (fun w:q08=> q74 d w.1) a keep:= by
  rw [qbe,qba,q2d]
  cases keep
  · cases q74 d a.1 <;> rfl
  · rfl
abbrev QS:= Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def qcX (u:Bool) (k:Nat) (ws:List q08) (p:q02):QS:=
  let d:= p.domain.toNat
  let ms:= ws.map (fun w:q08=> qbg d w.1)
  (d,ms.countP (qb9 d),p.bound,Nat.add k p.paid,(ms.map fun m=> cond (qb7 u d (p.wires.map (qbg d)) m) 0 1).sum,ms,p.wires.map (qbg d),u)
noncomputable def q3y {β:Type} (b:Bool) (f:Bool → β):β:= Bool.rec (f false) (f true) b
noncomputable def q3E {β:Type} (u:Bool) (k:Nat) (ws:List q08) (p:q02) (f:QS → β):β:=
  q3x p.domain.toNat fun d=> q3C (qbg d) p.wires fun pm=> q3C (fun w:q08=> qbg d w.1) ws fun ms=>
  q3x (ms.countP (qb9 d)) fun c=> q3x p.bound fun l=> q3x (Nat.add k p.paid) fun t=>
  q3x (ms.map fun m=> cond (qb7 u d pm m) 0 1).sum fun v=> q3y u fun u=> f (d,c,l,t,v,ms,pm,u)
theorem q3F {β:Type} (u k ws p) (f:QS → β):q3E u k ws p f=f (qcX u k ws p):= by
  have e (b:Bool) (f:Bool → β):q3y b f=f b:= by cases b <;> rfl
  simp only [q3E,q3I,q3D,e]
  rfl
noncomputable def q3G {β:Type} (u:Bool) (k:Nat) (ws:List q08) (ps:List q02):(List QS → β) → β:=
  List.rec (fun f=> f []) (fun p _ ih f=> q3E u k ws p fun q=> ih fun qs=> f (q::qs)) ps
theorem q3H {β:Type} (u k ws ps) (f:List QS → β):q3G u k ws ps f=f (ps.map (qcX u k ws)):= by
  induction ps generalizing f with
  | nil=> rfl
  | cons p ps ih=>
    change q3E u k ws p (fun q=> q3G u k ws ps fun qs=> f (q::qs))=_
    rw [q3F,ih]
    rfl
def kwN (v:Nat):Nat:=
  let n:= v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane:= q0d × Nat × Nat × List QS × List Nat × Nat
noncomputable def q8N (c:q0d):Lane:=
  let ws:= c.2.2.1.map (fun w:q08=> w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (qcX c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def q3A {β:Type} (cs:List q0d):(List Lane → β) → β:=
  List.rec (fun f=> f []) (fun c _ ih f=> q3x c.2.2.1.length fun n=> q3x (cond c.2.2.2.1.2 4 2) fun l=>
    q3C (fun w:q08=> w.1.toNat) c.2.2.1 fun ws=> q3x (ws.map kwN).sum fun t=>
    q3G c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs=> ih fun ys=> f ((c,n,l,qs,ws,t)::ys)) cs
theorem q3B {β:Type} (cs) (f:List Lane → β):q3A cs f=f (cs.map q8N):= by
  induction cs generalizing f with
  | nil=> rfl
  | cons c cs ih=>
    change q3x c.2.2.1.length (fun n=> q3x (cond c.2.2.2.1.2 4 2) fun l=>
      q3C (fun w:q08=> w.1.toNat) c.2.2.1 fun ws=> q3x (ws.map kwN).sum fun t=>
      q3G c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs=> q3A cs fun ys=> f ((c,n,l,qs,ws,t)::ys))=_
    rw [q3I,q3I,q3D,q3I,q3H,ih]
    rfl
noncomputable def q3o (s:QS) (i j op:Nat) (ka kb:Bool):Bool:=
  q3x (s.2.2.2.2.2.1.getD i 0) fun x=> q3x (s.2.2.2.2.2.1.getD j 0) fun y=>
  let av:= qb7 s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi:= Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (qbe s.1 x ka)) (qbe s.1 y kb))
  let lo:= s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (q3x (zN op x y) fun z=> or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (qb9 s.1 (zN op x y)) false))
theorem qeV {d:Nat} (ws:List q08) (i:Nat) (hd:qbg d zero=0):
    (ws.map (fun w:q08=> qbg d w.1)).getD i 0=qbg d (ws.getD i q2O).1:= by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none=> exact hd.symm
  | some v=> rfl
theorem q3s {u k p ws i j op ka kb} (h:q3o (qcX u k ws p) i j op ka kb=true):
    qeU u p ws k (ws.getD i q2O) (ws.getD j q2O) op ka kb=true:= by
  have z0:qbg p.domain.toNat zero=0:= by
    have:zero.toNat=0:= by simp [zero]
    simp [qbg,this]
  have su:(((ws.map (fun w:q08=> qbg p.domain.toNat w.1)).map fun m=> cond (qb7 u p.domain.toNat (p.wires.map (qbg p.domain.toNat)) m) 0 1).sum)=
      (ws.map (unav u p)).sum:= by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (qb7 u p.domain.toNat (p.wires.map (qbg p.domain.toNat)) (qbg p.domain.toNat w.1)) 0 1=_
    rw [qb8]
    rfl
  simp only [q3o,qcX,q3I,qeV _ _ z0,su,List.countP_map,Function.comp_def,qba] at h
  generalize ws.getD i q2O=a at h ⊢
  generalize ws.getD j q2O=b at h ⊢
  replace h:and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((qb7 u p.domain.toNat (p.wires.map (qbg p.domain.toNat))) (qbg p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((qb7 u p.domain.toNat (p.wires.map (qbg p.domain.toNat))) (qbg p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:q08=> q74 p.domain w.1)) (qbe p.domain.toNat (qbg p.domain.toNat a.1) ka)) (qbe p.domain.toNat (qbg p.domain.toNat b.1) kb))))
    (or ((qb7 u p.domain.toNat (p.wires.map (qbg p.domain.toNat))) (zN op (qbg p.domain.toNat a.1) (qbg p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:q08=> q74 p.domain w.1)) (qbe p.domain.toNat (qbg p.domain.toNat a.1) ka)) (qbe p.domain.toNat (qbg p.domain.toNat b.1) kb)))) (and ((qb7 u p.domain.toNat (p.wires.map (qbg p.domain.toNat))) (qbg p.domain.toNat a.1)) ((qb7 u p.domain.toNat (p.wires.map (qbg p.domain.toNat))) (qbg p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:q08=> q74 p.domain w.1)) (qbe p.domain.toNat (qbg p.domain.toNat a.1) ka)) (qbe p.domain.toNat (qbg p.domain.toNat b.1) kb)))) (qb9 p.domain.toNat (zN op (qbg p.domain.toNat a.1) (qbg p.domain.toNat b.1))) false))=true:= h
  rw [qjz,qba,qb8,qb8,qb8,qbf,qbf] at h
  have ca:q74 p.domain (bin op a.1 b.1)=true → q0Z u p.domain p.wires (bin op a.1 b.1)=true:= by
    intro zc
    simp only [q0Z,q74,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩:= h
  simp only [qeU,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w=> q74 p.domain w.1) - q2d (fun w:q08=> q74 p.domain w.1) a ka -
      q2d (fun w:q08=> q74 p.domain w.1) b kb=c at h ⊢
    generalize q74 p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize q0Z u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
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
theorem q0U (m:Nat) (l:List Nat):q0S m l=true ↔ m ∈ l:= by
  induction l with
  | nil=> simp [q0S]
  | cons a l ih=>
    change or (Nat.beq m a) (q0S m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def q8Y (fl:Nat → Option (List Nat)) (l:Lane) (i j op:Nat) (ka kb:Bool):Bool:=
  q3x (l.2.2.2.2.1.getD i 0) fun x=> q3x (l.2.2.2.2.1.getD j 0) fun y=> q3x (zN op x y) fun z=>
  Option.rec false (fun ys=> q3C (fun v=> v) ys fun ys=>
    and (q0S z ys) (and (l.2.2.2.2.1.all fun v=> or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (q0S v ys)))
      (ys.all fun v=> or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (q0S v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem q7e (xs:List Sig):q7d xs=(xs.map q7f).sum:= by
  have go (a:Nat):xs.foldl (fun v x=> v+q7f x) a=a+(xs.map q7f).sum:= by
    induction xs generalizing a with
    | nil=> rfl
    | cons x xs ih=> rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem q2U (f:q08 → Nat) {ws:List q08} {a b:q08} (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b) (ka kb:Bool):
    ((q2S ws a b ka kb).map f).sum=(ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)):= by
  have er {l:List q08} {x:q08} (hx:x ∈ l):(l.map f).sum=f x + ((l.erase x).map f).sum:= by
    have:= ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm:b ∈ ws.erase a:= (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1:= er ha
  have e2:= er hb
  have e3:= er hm
  cases ka <;> cases kb <;> simp only [q2S,q2P,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem q3p {u p k ws a b op ka kb} (ha:a∈ws) (hb:b∈ws) (ne:a≠b) (al:q0O u op=true)
    (h:qeU u p ws k a b op ka kb=true):
    qdx u p k ((q2S ws a b ka kb).map Prod.fst) (qb2 op a b)=true:= by
  let const:= fun w:q08=> q74 p.domain w.1
  let z:= bin op a.1 b.1
  let rest:= q2S ws a b ka kb
  have ck:= q79 const ws a b ka kb
  change ws.countP const - q2d const a ka - q2d const b kb ≤ rest.countP const at ck
  simp only [qeU,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩:= h
  have sum:= q2U (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs:((q2S ws a b ka kb).map (unav u p)).sum=0:= by omega
  have hs:(rest.map Prod.fst).all (q0Z u p.domain p.wires)=true:= by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩:= List.mem_map.mp hm
    have v:= List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e:q0Z u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK:(!(!q0Z u p.domain p.wires z) || q1Y u p.domain p.wires (qb2 op a b))=true:= by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [q1Y,qb2,x,y,al]
  change k+p.paid+(!q0Z u p.domain p.wires z).toNat < p.bound+(ws.countP const - q2d const a ka -
        q2d const b kb+(q74 p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez:q1Z (qb2 op a b)=z:= rfl
  simp only [qdx,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!q0Z u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if q74 p.domain z then 1 else 0)
  cases hc':q74 p.domain z <;> simp [hc'] at hc ⊢ <;> omega
theorem qjA (op:Nat) (a b:Sig):zN op a.toNat b.toNat=(bin op a b).toNat:= by
  have e (v:Sig):qbg one.toNat v=v.toNat:= by
    rw [qbh]
    congr 1
    exact BitVec.and_allOnes
  have:= qjz op one a b
  rwa [e,e,e] at this
theorem getW (ws:List q08) (i:Nat):
    (ws.map (fun w:q08=> w.1.toNat)).getD i 0=(ws.getD i q2O).1.toNat:= by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none=>
    have z0:zero.toNat=0:= by simp [zero]
    exact z0.symm
  | some v=> rfl
theorem qgP {c:q0d} {i j} (nd:(c.2.2.1.map Prod.fst).Nodup)
    (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length) (hij:i≠j):(q2f c i).1 ≠ (q2f c j).1:= by
  have gi:q2f c i=c.2.2.1[i]:= by simp [q2f,List.getD_eq_getElem?_getD,hi]
  have gj:q2f c j=c.2.2.1[j]:= by simp [q2f,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:= by simpa using hi) (hj:= by simpa using hj)).mp
  simpa using e
theorem q8Z {c:q0d} {fl i j op ka kb} (nd:(c.2.2.1.map Prod.fst).Nodup)
    (hfl:∀ tag ys,fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat)
    (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length) (hij:i≠j) (h:q8Y fl (q8N c) i j op ka kb=true):
    (c.2.2.2.2.2 (q7d (q1Z (qb2 op (q2f c i) (q2f c j))::
      (q2S c.2.2.1 (q2f c i) (q2f c j) ka kb).map Prod.fst))).any (qdt
      (q1Z (qb2 op (q2f c i) (q2f c j))::
      (q2S c.2.2.1 (q2f c i) (q2f c j) ka kb).map Prod.fst))=true:= by
  have mem (t) (ht:t<c.2.2.1.length):q2f c t ∈ c.2.2.1:= by
    simp [q2f,List.getD_eq_getElem?_getD,ht]
  have hne:= qgP nd hi hj hij
  have ha:= mem i hi
  have hb:= mem j hj
  have hab:q2f c i ≠ q2f c j:= fun e=> hne (congrArg Prod.fst e)
  have kv (v:Sig):= q7c nd ha hb ka kb v
  have sum:= q2U (fun w:q08=> q7f w.1) ha hb hab ka kb
  have wi:q2f c i=c.2.2.1.getD i q2O:= rfl
  have wj:q2f c j=c.2.2.1.getD j q2O:= rfl
  simp only [q8Y,q8N,q3I,getW,←wi,←wj,qjA] at h
  generalize q2f c i=a at *
  generalize q2f c j=b at *
  change Option.rec false _ (fl (q7f (bin op a.1 b.1)+(((c.2.2.1.map (fun w:q08=> w.1.toNat)).map kwN).sum -
    (cond ka 0 (q7f a.1)) - (cond kb 0 (q7f b.1)))))=true at h
  have tot:((c.2.2.1.map (fun w:q08=> w.1.toNat)).map kwN).sum=(c.2.2.1.map (fun w:q08=> q7f w.1)).sum:= by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag:q7d (q1Z (qb2 op a b)::(q2S c.2.2.1 a b ka kb).map Prod.fst)=
      q7f (bin op a.1 b.1)+((q2S c.2.2.1 a b ka kb).map (fun w:q08=> q7f w.1)).sum:= by
    rw [q7e,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize q7d (q1Z (qb2 op a b)::(q2S c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf:fl t with
  | none=> simp [hf] at h
  | some ys=>
    obtain ⟨xs,hx,rfl⟩:= hfl t ys hf
    rw [hf] at h
    simp only [q3D,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,q0U,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩:= h
    have back {v:Sig} (hv:v.toNat ∈ xs.map BitVec.toNat):v ∈ xs:= by
      obtain ⟨w,hw,e⟩:= List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [qdt,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
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
          · refine Or.inl fun e=> ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e=> ?_
            subst e
            simp at x
noncomputable def q3m (fl:Nat → Option (List Nat)) (l:Lane) (i j op:Nat) (ka kb:Bool):Bool:=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s=> q3o s i j op ka kb) (q8Y fl l i j op ka kb))) (q1Q l.1 i j op ka kb)
theorem q3n {c:q0d} {fl i j op ka kb} (nd:(c.2.2.1.map Prod.fst).Nodup)
    (hfl:∀ tag ys,fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat)
    (h:q3m fl (q8N c) i j op ka kb=true):
    q1Q c i j op ka kb=true:= by
  simp only [q3m,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi:= Nat.ble_eq.mp hi
    have hj:= Nat.ble_eq.mp hj
    have ho:= Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al:q0O c.2.2.2.1.2 op=true:= by
      cases hu:c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [q0O] <;> omega
    have mem (t) (ht:t<c.2.2.1.length):q2f c t ∈ c.2.2.1:= by
      simp [q2f,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩:= List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩:= List.mem_map.mp hm
    have hne:= qgP nd hi hj (fun e=> by simp [e] at hn)
    have closed:= q3p (mem i hi) (mem j hj) (fun e=> hne (congrArg Prod.fst e)) al (q3s ok)
    have cut:c.2.2.2.2.1.any (fun p=> qdx c.2.2.2.1.2 p (c.1-1)
        ((q2S c.2.2.1 (q2f c i) (q2f c j) ka kb).map Prod.fst)
        (qb2 op (q2f c i) (q2f c j)))=true:=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [q1Q,q34,q21,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut:= q8Z nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e=> by simp [e] at hn) h
    simp only [q1Q,q34,q21,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def qf3 (v t:Nat):Nat:= cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def qgK (v:Nat):Bool:= and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem qf6:∀ v:Fin 144,qgK v.val=true → ∀ t:Fin 9,qf3 v.val t.val<9 ∧
    qgW (qf4 v.val) (inputs.getD t.val zero)=inputs.getD (qf3 v.val t.val) zero:= by decide +kernel
theorem qf5 {v t:Nat} (hv:qgK v=true) (ht:t<9):qf3 v t<9 ∧
    qgW (qf4 v) (inputs.getD t zero)=inputs.getD (qf3 v t) zero:= by
  have lt:v<144:= by
    simp only [qgK,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact qf6 ⟨v,lt⟩ hv ⟨t,ht⟩
def q6U (perm:List Nat) (t:Nat):Nat:= perm.foldl (fun t v=> qf3 v t) t
theorem q6V {perm:List Nat} (ok:perm.all qgK=true) {t:Nat} (ht:t<9):
    qb5 (perm.map qf4).reverse (inputs.getD t zero)=inputs.getD (q6U perm t) zero:= by
  rw [qb5,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil=> rfl
  | cons v perm ih=>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩:= qf5 ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def q2L:Nat → Nat → List Nat → List Nat
  | 0,_,ws=> ws
  | n+1,bits,ws=> q3x (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z=> q2L n (bits >>> 10) (ws++[z])
theorem q2M (F:Sig → Nat) (F0:F zero=0) (Fb:∀ op a b,F (bin op a b)=zN op (F a) (F b))
    (n bits:Nat) (ds:List q08):
    (q2K n bits ds).map (fun w=> F w.1)=q2L n bits (ds.map fun w=> F w.1):= by
  have gd (ds:List q08) (i:Nat):(ds.map fun w=> F w.1).getD i 0=F (ds.getD i q2O).1:= by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none=> exact F0.symm
    | some v=> rfl
  induction n generalizing bits ds with
  | zero=> rfl
  | succ n ih=>
    rw [q2L,q3I,q2K,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem qdA {α β:Type} (f:α → β) (bits:Nat) (ws:List α):
    (qdz bits ws).map f=qdz bits (ws.map f):= by
  induction ws generalizing bits with
  | nil=> rfl
  | cons w ws ih=>
    rw [List.map_cons,qdz,qdz]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def q3q (g:q0a) (k i:Nat) (perm:List Nat):List Nat:=
  let raw:= (qdC g.mask).map fun e=> (inputs.getD (q6U perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data):= g.levels k
  let len:= 10*depth
  q3x (q3K (g.levels k) (qdC g.mask).length i) fun rec=>
  qdz (rec >>> len) (q2L depth (rec &&& ((1 <<< len)-1)) raw)
theorem q3r (g:q0a) (k i:Nat) {perm:List Nat} (ok:perm.all qgK=true):
    q3q g k i perm=((qeW g k i).map (qb5 (perm.map qf4).reverse)).map BitVec.toNat:= by
  let ms:= (perm.map qf4).reverse
  let F (a:Sig):Nat:= (qb5 ms a).toNat
  have F0:F zero=0:= by
    change (qb5 ms zero).toNat=0
    rw [qb6,(qd9 _).1]
    simp [zero]
  have Fb (op a b):F (bin op a b)=zN op (F a) (F b):= by
    change (qb5 ms (bin op a b)).toNat=zN op (qb5 ms a).toNat (qb5 ms b).toNat
    rw [qjA,qb6,qd8,qb6,qb6]
  have raw:(qgQ g).map (fun w=> F w.1)=(qdC g.mask).map fun e=> (inputs.getD (q6U perm e.1) zero).toNat:= by
    simp only [qgQ,qcY,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩:= qdD hm
    exact congrArg BitVec.toNat (q6V ok hj)
  have len:(qgQ g).length=(qdC g.mask).length:= by simp [qgQ,qcY]
  unfold q3q qeW qd5
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [q3I,qeX,len]
  rw [List.map_map,List.map_map,qdA,←raw,←q2M F F0 Fb]
  rfl
noncomputable def q90 (g:q0a) (k:Nat) (pair:Nat × Nat):Option (List Nat):=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm=> cond (perm.all qgK) (some (q3q g k pair.1 perm)) none
noncomputable def flOf (g:q0a) (k:Nat):Nat → Option (List Nat):= fun tag=> (g.index k tag).bind (q90 g (k-1))
noncomputable def q16 (fl:Nat → Option (List Nat)) (u:Bool) (b:q01) (xs:List Lane) (i j op:Nat) (ka kb:Bool):=
  let (k,n,r,_,cov):= b
  let len:= 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a:= q8Q b i
    let b':= q8Q b j
    let z:= qbL op a b'
    let mask:= q3T r (qfu cov (qbJ (!u) a) (qbJ (!u) b') ka kb ||| qbJ (!u) z)
    qbB (fun c=> q3m fl c i j op ka kb) mask xs
theorem q17 {fl u} (k n) (xs:List q0d) {i j op:Nat} {ka kb}
    (hi:i<n) (hj:j<n) {q:Nat} (hq:q<xs.length)
    (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl:∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
    (pass:q16 fl u (qai k n xs) (xs.map q8N) i j op ka kb=true):
    q1Q xs[q] i j op ka kb=true:= by
  let len:= 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval:q1Q xs[q] i j op ka kb=
      if len>k then true else if q27 xs[q] (!u) ka kb op i j !=BitVec.allOnes 152 then true
      else if !qcR (dbin op (q2f xs[q] i) (q2f xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v=> v.1==(dbin op (q2f xs[q] i) (q2f xs[q] j)).1)
      then true else q21 u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((q2S xs[q].2.2.1 (q2f xs[q] i) (q2f xs[q] j) ka kb).map Prod.fst)
        (qb2 op (q2f xs[q] i) (q2f xs[q] j)):= by
    simp only [q1Q,q34,budget,arity,mode,len,q27] <;> rfl
  by_cases small:len>k
  · simp [eval,small]
  · let r:= qfI xs.length
    let a:= q8Q (qai k n xs) i
    let b:= q8Q (qai k n xs) j
    let cov:= qbK (fun c:q0d=> c.2.2.2.1.1) xs
    change (if len>k then true else qbB _ (q3T r
       (qfu cov (qbJ (!u) a) (qbJ (!u) b) ka kb |||
        qbJ (!u) (qbL op a b))) (xs.map q8N))=true at pass
    rw [if_neg small] at pass
    have ca:a=_:= q8R k n xs hi
    have cb:b=_:= q8R k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,qbO,qbN,qbN,qbN,qfv,q8T] at pass
    by_cases hit:q27 xs[q] (!u) ka kb op i j=BitVec.allOnes 152
    · apply q3n nd hfl
      have m:= qap _ _ _ q (by simpa using hq) (by
        rw [qao _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def q18 (fl:Nat → Option (List Nat)) (u:Bool) (b:q01) (xs:List Lane) (i j op:Nat):=
  let f:= q16 fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def q19 (fl:Nat → Option (List Nat)) (u:Bool) (b:q01) (xs:List Lane) (i:Nat) (js:List Nat):=
    js.all (fun j=> (qbF u).all (q18 fl u b xs i j))
noncomputable def q1a (fl:Nat → Option (List Nat)) (u:Bool) (b:q01) (xs:List Lane):List Nat → Bool
  | []=> true
  | i::js=> q19 fl u b xs i js && q1a fl u b xs js
theorem q1b {fl u} (k n) (xs:List q0d) {q:Nat} (hq:q<xs.length)
    (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl:∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
    (js:List Nat)
    (bounds:∀ j ∈ js,j<n) (allRows:q1a fl u (qai k n xs) (xs.map q8N) js=true):
    qfy xs[q] (js.map (q2f xs[q]))=true:= by
  induction js with
  | nil=> rfl
  | cons i js ih=>
    simp only [q1a,Bool.and_eq_true,q19,List.all_eq_true] at allRows
    simp only [List.map_cons,qfy,qfB,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:= bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj=> bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj':= bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass:= allRows.1 j hj op hop
    have check:= @q17 fl u k n xs i j op
    simp only [q18,Bool.and_eq_true] at pass
    simp only [qfz,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def qdq (fl:Nat → Option (List Nat)) (u:Bool) (k n:Nat) (xs:List q0d):=
    q1a fl u (qai k n xs) (xs.map q8N) (List.range n)
theorem qdr {fl u k n} {xs:List q0d} {q} (hq:q<xs.length)
    (hb:xs[q].1=k) (ha:xs[q].2.1=n) (hm:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl:∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
    (hn:xs[q].2.2.1.length=n)
    (pass:qdq fl u k n xs=true):qfy xs[q] xs[q].2.2.1=true:= by
  have all:= q1b k n xs hq hb ha hm nd hfl (List.range n) (fun _=> List.mem_range.mp) pass
  have eq:(List.range n).map (q2f xs[q])=xs[q].2.2.1:= by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [q2f,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def q2e (g:q0a) (k i:Nat):q0d:=
  let raw:= qgQ g
  let (num,depth,cw,iw,pw,offw,lw,data):= g.levels k
  let (ops,bank,ws):= qd5 g k i
  let rules:= (q3J (g.levels k) raw.length i).filterMap (fun (a,b)=> q1E g ops depth bank a b)
  let ls:= fun tag=> ((g.index k tag).bind (q91 g (k-1))).toList
  (k,ws.length,ws,qcI g.mode ws,rules,ls)
theorem q3u (g:q0a) (k i tag:Nat) (ys) (h:flOf g k tag=some ys):
    ∃ xs ∈ (q2e g k i).2.2.2.2.2 tag,ys=xs.map BitVec.toNat:= by
  change ∃ xs ∈ ((g.index k tag).bind (q91 g (k-1))).toList,_
  unfold flOf at h
  cases hp:g.index k tag with
  | none=> simp [hp] at h
  | some pair=>
    simp only [hp,Option.bind_some,q90] at h
    simp only [Option.bind_some,q91]
    split at h
    · contradiction
    next v=>
      cases ha:g.autos[pair.2]? with
      | none=> simp [ha] at h
      | some perm=>
        simp only [ha,Option.bind_some] at h
        cases hv:perm.all qgK with
        | false=> simp [hv] at h
        | true=>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(qeW g (k-1) pair.1).map (qb5 (perm.map qf4).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (q3r g _ _ hv)
def qcK (T:Sig) (c:q0d):=
  let ws:= c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem q3S (g:q0a) (k i:Nat):
    qbi g k i=(qcK (qfx g) (q2e g k i) &&
      (if k=0 then true else qfy (q2e g k i) (q2e g k i).2.2.1)):= rfl
theorem qaj {g k start n} (h:∀ (i:Nat),start ≤ i → i < start + n → qbi g k i=true):
    q1w g k start n=true:= by
  induction n with
  | zero=> rfl
  | succ n ih=>
    simp only [q1w,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt=> h i le (by omega))⟩
def q2g (g:q0a) (k start n:Nat):=
  ((List.range n).map (start+·)).map (q2e g k)
def q6Q (g:q0a) (k start n ar:Nat):=
  (q2g g k start n).all (fun c=> c.2.1==ar && qcK (qfx g) c)
noncomputable def qdm (g:q0a) (k start n ar lo len:Nat):=
  let xs:= q2g g k start n
  let b:= qai k ar xs
  q3A xs fun ys=> (List.range len).all (fun d=>
    let i:= lo+d
    q19 (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem qdn {g k start n ar lo len} (h:qdm g k start n ar lo len=true)
    (i:Nat) (l:lo ≤ i) (r:i < lo+len):
    q19 (flOf g k) g.mode (qai k ar (q2g g k start n)) ((q2g g k start n).map q8N)
      i (List.range' (i+1) (ar-(i+1)))=true:= by
  simp only [qdm,q3B] at h
  have ha:= List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem qdo {g k start n ar lo a b}
    (h:qdm g k start n ar lo a=true) (t:qdm g k start n ar (lo+a) b=true):
    qdm g k start n ar lo (a+b)=true:= by
  simp only [qdm,q3B]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt:= List.mem_range.mp hj
  by_cases first:j<a
  · exact qdn h (lo+j) (by omega) (by omega)
  · exact qdn t (lo+j) (by omega) (by omega)
theorem q2J {g k start n ar} (h:qdm g k start n ar 0 ar=true):
    qdq (flOf g k) g.mode k ar (q2g g k start n)=true:= by
  let xs:= q2g g k start n
  have go (lo num:Nat) (eq:lo+num=ar):
      q1a (flOf g k) g.mode (qai k ar xs) (xs.map q8N) (List.range' lo num)=true:= by
    induction num generalizing lo with
    | zero=> rfl
    | succ num ih=>
      simp only [List.range'_succ,q1a,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok:= qdn h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold qdq
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem q2I {g k start n ar} (hd:q6Q g k start n ar=true)
    (h:qdm g k start n ar 0 ar=true):q1w g k start n=true:= by
  apply qaj
  intro i lo hi
  let xs:= q2g g k start n
  have hm:q2e g k i ∈ xs:= by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:= List.getElem_of_mem hm
  have one:= List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb:xs[q].1=k:= by rw [e]; rfl
  have ha:xs[q].2.1=ar:= e ▸ one.1
  have nd:(xs[q].2.2.1.map Prod.fst).Nodup:= by
    have p:= one.2
    simp only [qcK,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl:∀ tag ys,flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat:= by
    rw [e]
    exact fun tag ys h=> q3u g k i tag ys h
  have hm:xs[q].2.2.2.1.2=g.mode:= by rw [e]; rfl
  have hn:xs[q].2.2.1.length=ar:= by rw [e]; exact one.1
  rw [q3S,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ qdr hq hb ha hm nd hfl hn (q2J h)
def q1C (g:q0a) (k start n ar lo num:Nat):Nat → Prop
  | 0=> qdm g k start n ar lo num=true
  | d+1=> q1C g k start n ar lo (num/2) d ∧ q1C g k start n ar (lo+num/2) (num-num/2) d
theorem q1D {g k start n ar lo num d} (h:q1C g k start n ar lo num d):
    qdm g k start n ar lo num=true:= by
  induction d generalizing lo num with
  | zero=> exact h
  | succ d ih=>
    have v:= qdo (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def q1K (g:q0a) (k start n ar rows:Nat):Nat → Prop
  | 0=> q6Q g k start n ar=true ∧ q1C g k start n ar 0 ar rows
  | d+1=> q1K g k start (n/2) ar rows d ∧ q1K g k (start+n/2) (n-n/2) ar rows d
theorem q1L {g k start n ar rows d} (h:q1K g k start n ar rows d):
    q1w g k start n=true:= by
  induction d generalizing start n with
  | zero=> exact q2I h.1 (q1D h.2)
  | succ d ih=>
    have v:= q1y (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def q93 {α} (f:α → Bool) (xs:List α):Nat → Prop
  | 0=> xs.all f=true
  | d+1=> q93 f (xs.take (xs.length/2)) d ∧ q93 f (xs.drop (xs.length/2)) d
theorem qcr {α f xs d} (h:@q93 α f xs d):xs.all f=true:= by
  induction d generalizing xs with
  | zero=> exact h
  | succ d ih=>
    have ap:((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:= by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem q2H {u} {m cap:Nat} {prior:Nat → Nat} {ws:List Sig}
    (low:∀ q,Lower u (qgM q) (graphGoal q) (prior q)) (ci:q04)
    (ok:q23 m ci prior=true)
    (cut:(decide ws.Nodup && qcF u (qeZ ci.1 ci.2.1) ci.2.2.2.2 cap 0 (qgM (qcZ m ci)) ws)=true):
    Impossible u (graphGoal m) cap ws.toFinset:= by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact qcG (q25 ci prior low ok) [] rfl cut.1 cut.2
theorem q6W {u} {g:q0a} {m cap i:Nat} {prior:Nat → Nat} {ws:List Sig}
    (hm:g.mask=m) (hu:g.mode=u) (low:∀ q,Lower u (qgM q) (graphGoal q) (prior q))
    (geom:q5D g prior=true) (blocks:q1V g cap)
    (idx:q6X g cap i ws=true):Impossible u (graphGoal m) cap ws.toFinset:= by
  subst hm
  subst hu
  exact qdk low geom blocks (Nat.le_refl _) idx
def q31 (m hints:Nat):Bool:=
  let xs:= q5C m hints
  qcR (graphGoal m) && q1R (graphGoal m) (vars m) xs && (xs.map Prod.fst==vars m)
theorem qcE {u} {m hints cap:Nat} (ok:q31 m hints=true)
    (a:Impossible u (graphGoal m) cap (vars m).toFinset):Lower u (vars m) (graphGoal m) (cap+1):= by
  simp only [q31,Bool.and_eq_true,beq_iff_eq] at ok
  apply qaf (qcV _ ok.1.1) (q33 ok.1.2).1 (q33 ok.1.2).2 _ a
  intro v hv
  apply q32 ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv
def q48 (i:Nat):Nat:= 0xf
def q4a:q0g:= (1,0,1,0,0,0,0,q48)
def q4c:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffffffffff3,0x62),(0xffffffffffffffffffffffffffffffffffffbf,0xffffffffffffffffffffffffffffffffffff99),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def q47:List q04:= []
def q46:List (List Nat):= [[],[48,33]]
def q4b:Nat → q0g
  | 3=> q4a
  | _=> q2Y
def q49:Nat → Nat → Option (Nat × Nat)
  | _=> fun _=> none
def g15:q0a:= ⟨15,3,fun j=> q4c[j]?.getD (0,0),q47,q46,q4b,q49⟩
set_option maxHeartbeats 0 in
theorem q5k:q5D g15 (q1B [])=true:= by
  simp only [q5D,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qcr (d:= 0) ?_⟩,qcr (d:= 0) ?_⟩
  all_goals simp only [q93]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdG:q1w g15 3 0 1=true:= by decide +kernel
theorem q0v:q1w g15 3 0 1=true:= qdG
theorem qfe:q1V g15 3:= by
  intro k hk
  interval_cases k
  · exact (rfl:q1w g15 0 0 0=true)
  · exact (rfl:q1w g15 1 0 0=true)
  · exact (rfl:q1w g15 2 0 0=true)
  · exact q0v
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9j:Lower true (vars 15) (graphGoal 15) 4:= qcE (hints:= 8449) (by decide +kernel) (q6W (g:= g15) (i:= 0) rfl rfl (q1c [] q15) q5k qfe (by decide +kernel))
def q7n:= q38 [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qfQ:Known true q7n:= q3a (m:= 15) q15 q9j (by decide +kernel)
def q4N (i:Nat):Nat:= 0x11a20bf
def q4T:q0g:= (1,0,3,0,0,0,0,q4N)
def q4P (i:Nat):Nat:= 0x30be670208000065000016357504004755c084
def q4M (i:Nat):Nat:= 0x40828fd20fd10
def q4S:q0g:= (2,1,3,0,0,3,0,q4M)
def q4O (i:Nat):Nat:= 0x300
def q4L (i:Nat):Nat:= 0x5dd4520
def q4R:q0g:= (1,2,3,0,0,0,0,q4L)
def q4V:Array (Bits × Bits):= #[(0x2e44,0x2c52),(0x5a8a,0x5208),(0xffffffffffffffffffffffffffffffffffb4f7,0xffffffffffffffffffffffffffffffffffa0c7),(0xffffffffffffffffffffffffffffffffffcf79,0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def q4K:List q04:= [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def q4J:List (List Nat):= [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def q4U:Nat → q0g
  | 6=> q4T
  | 5=> q4S
  | 4=> q4R
  | _=> q2Y
def q4Q:Nat → Nat → Option (Nat × Nat)
  | 6=> q9a 5 15 3 9 1 4 q4P
  | 5=> q9a 1 3 1 9 1 4 q4O
  | _=> fun _=> none
def g31:q0a:= ⟨31,6,fun j=> q4V[j]?.getD (0,0),q4K,q4J,q4U,q4Q⟩
set_option maxHeartbeats 0 in
theorem q5n:q5D g31 (q1B q7n)=true:= by
  simp only [q5D,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qcr (d:= 0) ?_⟩,qcr (d:= 1) ?_⟩
  all_goals simp only [q93]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdY:q1w g31 6 0 1=true:= by decide +kernel
theorem q0G:q1w g31 6 0 1=true:= qdY
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdX:q1w g31 5 0 2=true:= by decide +kernel
theorem q0F:q1w g31 5 0 2=true:= qdX
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdW:q1w g31 4 0 1=true:= by decide +kernel
theorem q0E:q1w g31 4 0 1=true:= qdW
theorem qfh:q1V g31 6:= by
  intro k hk
  interval_cases k
  · exact (rfl:q1w g31 0 0 0=true)
  · exact (rfl:q1w g31 1 0 0=true)
  · exact (rfl:q1w g31 2 0 0=true)
  · exact (rfl:q1w g31 3 0 0=true)
  · exact q0E
  · exact q0F
  · exact q0G
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9E:Lower true (vars 31) (graphGoal 31) 7:= qcE (hints:= 8449) (by decide +kernel) (q6W (g:= g31) (i:= 0) rfl rfl (q1c q7n qfQ) q5n qfh (by decide +kernel))
def q7I:= q38 q7n 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qgb:Known true q7I:= q3a (m:= 31) qfQ q9E (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9V:Lower true (vars 47) (graphGoal 47) 5:= qcE (hints:= 8449) (by decide +kernel) (q2H (prior:= q1B q7I) (q1c q7I qgb) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def q7Y:= q38 q7I 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qgs:Known true q7Y:= q3a (m:= 47) qgb q9V (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qa3:Lower true (vars 55) (graphGoal 55) 5:= qcE (hints:= 257) (by decide +kernel) (q2H (prior:= q1B q7Y) (q1c q7Y qgs) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def q86:= q38 q7Y 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qgA:Known true q86:= q3a (m:= 55) qgs qa3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qa8:Lower true (vars 63) (graphGoal 63) 8:= qcE (hints:= 8449) (by decide +kernel) (q2H (prior:= q1B q86) (q1c q86 qgA) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def q8b:= q38 q86 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qgF:Known true q8b:= q3a (m:= 63) qgA qa8 (by decide +kernel)
def q3Z (i:Nat):Nat:= 0x7213f
def q43:q0g:= (1,0,2,0,0,0,0,q3Z)
def q40 (i:Nat):Nat:= 0x8000
def q3Y (i:Nat):Nat:= 0x17e51
def q42:q0g:= (1,1,2,0,0,0,0,q3Y)
def q45:Array (Bits × Bits):= #[(0xffffffffffffffffffffffffffffffffffed93,0x2d12),(0xffffffffffffffffffffffffffffffffff9467,0xffffffffffffffffffffffffffffffffff9025),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]
def q3X:List q04:= [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def q3W:List (List Nat):= [[],[32,83]]
def q44:Nat → q0g
  | 6=> q43
  | 5=> q42
  | _=> q2Y
def q41:Nat → Nat → Option (Nat × Nat)
  | 6=> q9a 1 3 1 6 1 1 q40
  | _=> fun _=> none
def g111:q0a:= ⟨111,6,fun j=> q45[j]?.getD (0,0),q3X,q3W,q44,q41⟩
set_option maxHeartbeats 0 in
theorem q5j:q5D g111 (q1B q8b)=true:= by
  simp only [q5D,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qcr (d:= 0) ?_⟩,qcr (d:= 0) ?_⟩
  all_goals simp only [q93]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdF:q1w g111 6 0 1=true:= by decide +kernel
theorem q0u:q1w g111 6 0 1=true:= qdF
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdE:q1w g111 5 0 1=true:= by decide +kernel
theorem q0t:q1w g111 5 0 1=true:= qdE
theorem qfd:q1V g111 6:= by
  intro k hk
  interval_cases k
  · exact (rfl:q1w g111 0 0 0=true)
  · exact (rfl:q1w g111 1 0 0=true)
  · exact (rfl:q1w g111 2 0 0=true)
  · exact (rfl:q1w g111 3 0 0=true)
  · exact (rfl:q1w g111 4 0 0=true)
  · exact q0t
  · exact q0u
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9d:Lower true (vars 111) (graphGoal 111) 7:= qcE (hints:= 16785665) (by decide +kernel) (q6W (g:= g111) (i:= 0) rfl rfl (q1c q8b qgF) q5j qfd (by decide +kernel))
def q7h:= q38 q8b 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qfK:Known true q7h:= q3a (m:= 111) qgF q9d (by decide +kernel)
def q4h (i:Nat):Nat:= 0x163441bf
def q4n:q0g:= (1,0,3,0,0,0,0,q4h)
def q4j (i:Nat):Nat:= 0x42f9f28c08140000000020f801630c00d0
def q4g (i:Nat):Nat:= 0x420a3fa41fd10
def q4m:q0g:= (2,1,3,0,0,3,0,q4g)
def q4i (i:Nat):Nat:= 0x18000
def q4f (i:Nat):Nat:= 0xb7d8d20
def q4l:q0g:= (1,2,3,0,0,0,0,q4f)
def q4p:Array (Bits × Bits):= #[(0xfffffffffffffffffffffffffffffffff55417,0xfffffffffffffffffffffffffffffffff46453),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffc60f7,0x44076),(0xfffffffffffffffffffffffffffffffff0bbcb,0xfffffffffffffffffffffffffffffffff03a89),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]
def q4e:List q04:= [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def q4d:List (List Nat):= [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def q4o:Nat → q0g
  | 7=> q4n
  | 6=> q4m
  | 5=> q4l
  | _=> q2Y
def q4k:Nat → Nat → Option (Nat × Nat)
  | 7=> q9a 9 13 2 9 1 4 q4j
  | 6=> q9a 1 3 1 9 1 4 q4i
  | _=> fun _=> none
def g189:q0a:= ⟨189,7,fun j=> q4p[j]?.getD (0,0),q4e,q4d,q4o,q4k⟩
set_option maxHeartbeats 0 in
theorem q5l:q5D g189 (q1B q7h)=true:= by
  simp only [q5D,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qcr (d:= 1) ?_⟩,qcr (d:= 2) ?_⟩
  all_goals simp only [q93]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdJ:q1w g189 7 0 1=true:= by decide +kernel
theorem q0y:q1w g189 7 0 1=true:= qdJ
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdI:q1w g189 6 0 2=true:= by decide +kernel
theorem q0x:q1w g189 6 0 2=true:= qdI
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdH:q1w g189 5 0 1=true:= by decide +kernel
theorem q0w:q1w g189 5 0 1=true:= qdH
theorem qff:q1V g189 7:= by
  intro k hk
  interval_cases k
  · exact (rfl:q1w g189 0 0 0=true)
  · exact (rfl:q1w g189 1 0 0=true)
  · exact (rfl:q1w g189 2 0 0=true)
  · exact (rfl:q1w g189 3 0 0=true)
  · exact (rfl:q1w g189 4 0 0=true)
  · exact q0w
  · exact q0x
  · exact q0y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9s:Lower true (vars 189) (graphGoal 189) 8:= qcE (hints:= 536879876) (by decide +kernel) (q6W (g:= g189) (i:= 0) rfl rfl (q1c q7h qfK) q5l qff (by decide +kernel))
def q7w:= q38 q7h 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qfZ:Known true q7w:= q3a (m:= 189) qfK q9s (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9g:Lower true (vars 127) (graphGoal 127) 9:= qcE (hints:= 16785665) (by decide +kernel) (q2H (prior:= q1B q7w) (q1c q7w qfZ) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def q7k:= q38 q7w 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qfN:Known true q7k:= q3a (m:= 127) qfZ q9g (by decide +kernel)
def q4s (i:Nat):Nat:= 0x8201ff
def q4C:q0g:= (1,0,5,0,0,0,0,q4s)
def q4x (i:Nat):Nat:= 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def q4w (i:Nat):Nat:= 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def q4G:q0g:= (12,1,5,0,0,10,0,q4w)
def q4A (i:Nat):Nat:= 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def q4v (j:Nat):Nat:= 0x1f80354899e077b024a9159a24b911ac077e0465c892708574212ef090d670221e053c214e043b8235cc808a67d091c046f022c0a32623f7049522d15433a6477b08ce033e84719314e04222c097484381b79046f2083ea431f521b80ae446e02b90c91ffb0022ff500273ff780227d009160ad1a2b008a388648213e1129ec123701bbc02b6031f108e812788527a1372fef00a370177821af58220f98488d80ed11b79e031029f81224fe00116e08ea457911b013808784866ffa009e7c49103fc0098ee0495c8319f848269f5444bf2292df046e02b7ba00a2fc6c027b211cfe48667a04ad80ec912592247ef00ae68147aaa443fce6009d00860143e0495227c608ef0062ec24c9e99123806bc62448287a25ec8251c78110a11258898fc215345209610e8c3700843000414019102020c60a121c5c5ec5844fc4543ec3542cc25c1bc12409bfebf43e8be1bd8bcf3c73b9bae3a7b9eb9838f383b7d373369b6035934fb46b3ab3432bb24b1b311b072fcaf62edae72dc2ce2bf2b02a2294a8da83a7ca70a66a5ea54a4d24423c233a2aa192102069fa9ed9e61de9d29cd1c09b21aa1a399a99498e18397416815a14f94493712b11e91590f1000f10e88dd8d18ca0c08b70ab8a209508407d87606b86505b85104203883182501880d00042a470a82c2e250b1c428051315c2a4b0980c2c730b01c220f0b9942c37098142e430883428431b894240f098cc2a090881424370b12c240d090ac4e43090cc6e650994426530b0d44651090d4242f0b98c2a490b0242c570b1542c490b02c2408c3891ae246b94ba4107b92b6e24e8849aeb66b881ee82a983aa6486b951ae707b831ae0c6bad364307b893a2047b92324287b8ba6e867bb19ae0e6bb51ee2a7b909ae2c6ba49aed66b9c9ae607b8b1ee088a159ae50e9811ee4ea9821eea8c98c2a60c6b921ae086b8b9ee467bb29ee62e9849ae346b8d9ee647baa9ee0e6b993a4146b8caa64e6ba41eea67b89b2a286b959ae4e7bb216e242b9c86e87ffff7f7efefbfdf6ef6f902308821058d53501314c12044020
def q4F:q0g:= (113,2,5,589836,68,12,1057,q4v)
def q4z (i:Nat):Nat:= 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def q4u (i:Nat):Nat:= 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def q4E:q0g:= (116,3,5,0,0,11,0,q4u)
def q4y (i:Nat):Nat:= 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def q4t (i:Nat):Nat:= 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def q4D:q0g:= (12,4,5,0,0,6,0,q4t)
def q4I:Array (Bits × Bits):= #[(0xfffffffffffffffda8e81df4649a4aea03f353,0x1a8209cc44085084a802052),(0xfffffffffffffffe550627bdd1589ea381610f,0xfffffffffffffffe550c023b884896b1415109),(0xb876f0435535c500a8ea8c,0x2872300045166108a00a84),(0x2669d0fd182653b341a80c0,0x2428c0bdd82211a84129140),(0x1554172223bd2f53d4f48e0,0x15416022395ae5314d4aa0),(0x253ba08288d622045549630,0x2509e022805626105509220),(0x0,0x0),(0x38f01c59fba0814d3746c20,0x18701c597ba0892d2056500),(0x0,0x0)]
def q4r:List q04:= [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def q4q:List (List Nat):= [[],[115,84],[32,67,117],[32,83,116]]
def q4H:Nat → q0g
  | 10=> q4C
  | 9=> q4G
  | 8=> q4F
  | 7=> q4E
  | 6=> q4D
  | _=> q2Y
def q4B:Nat → Nat → Option (Nat × Nat)
  | 10=> q9a 16 41 5 10 4 2 q4x
  | 9=> q9a 67 277 6 13 7 2 q4A
  | 8=> q9a 100 251 6 13 7 2 q4z
  | 7=> q9a 4 19 2 10 4 2 q4y
  | _=> fun _=> none
def g191:q0a:= ⟨191,10,fun j=> q4I[j]?.getD (0,0),q4r,q4q,q4H,q4B⟩
set_option maxHeartbeats 0 in
theorem q5m:q5D g191 (q1B q7k)=true:= by
  simp only [q5D,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qcr (d:= 3) ?_⟩,qcr (d:= 0) ?_⟩
  all_goals simp only [q93]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdK:q1w g191 10 0 1=true:= by decide +kernel
theorem q0z:q1w g191 10 0 1=true:= qdK
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdV:q1w g191 9 0 12=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 2)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem q0D:q1w g191 9 0 12=true:= qdV
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdQ:q1w g191 8 0 3=true:= by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdS:q1w g191 8 3 36=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdT:q1w g191 8 39 31=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdU:q1w g191 8 70 36=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdR:q1w g191 8 106 7=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 1)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem q0C:q1w g191 8 0 113=true:= (@q1y g191 8 0 106 7 (@q1y g191 8 0 70 36 (@q1y g191 8 0 39 31 (@q1y g191 8 0 3 36 qdQ qdS) qdT) qdU) qdR)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdM:q1w g191 7 0 13=true:= by
  apply q1L (ar:= 7) (rows:= 0) (d:= 2)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdN:q1w g191 7 13 36=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdO:q1w g191 7 49 36=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdP:q1w g191 7 85 31=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem q0B:q1w g191 7 0 116=true:= (@q1y g191 7 0 85 31 (@q1y g191 7 0 49 36 (@q1y g191 7 0 13 36 qdM qdN) qdO) qdP)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdL:q1w g191 6 0 12=true:= by
  apply q1L (ar:= 7) (rows:= 0) (d:= 2)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem q0A:q1w g191 6 0 12=true:= qdL
theorem qfg:q1V g191 10:= by
  intro k hk
  interval_cases k
  · exact (rfl:q1w g191 0 0 0=true)
  · exact (rfl:q1w g191 1 0 0=true)
  · exact (rfl:q1w g191 2 0 0=true)
  · exact (rfl:q1w g191 3 0 0=true)
  · exact (rfl:q1w g191 4 0 0=true)
  · exact (rfl:q1w g191 5 0 0=true)
  · exact q0A
  · exact q0B
  · exact q0C
  · exact q0D
  · exact q0z
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9t:Lower true (vars 191) (graphGoal 191) 11:= qcE (hints:= 536879361) (by decide +kernel) (q6W (g:= g191) (i:= 0) rfl rfl (q1c q7k qfN) q5m qfg (by decide +kernel))
def q7x:= q38 q7k 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qg0:Known true q7x:= q3a (m:= 191) qfN q9t (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9z:Lower true (vars 251) (graphGoal 251) 8:= qcE (hints:= 1358970881) (by decide +kernel) (q2H (prior:= q1B q7x) (q1c q7x qg0) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def q7D:= q38 q7x 8 [(251,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qg6:Known true q7D:= q3a (m:= 251) qg0 q9z (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9A:Lower true (vars 255) (graphGoal 255) 12:= qcE (hints:= 553656577) (by decide +kernel) (q2H (prior:= q1B q7D) (q1c q7D qg6) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def q7E:= q38 q7D 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qg7:Known true q7E:= q3a (m:= 255) qg6 q9A (by decide +kernel)
def q50 (i:Nat):Nat:= 0x1840804ff
def q5c:q0g:= (1,0,6,0,0,0,0,q50)
def q56 (i:Nat):Nat:= 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def q4Z (i:Nat):Nat:= 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def q5b:q0g:= (6,1,6,0,0,9,0,q4Z)
def q55 (i:Nat):Nat:= 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def q4Y (j:Nat):Nat:= 0x2ff45022545810b0ebed2a0a0caa9a4a646170118bba1216fab28127d3e208a4fd3025756808373fd0139d909a4f77fc6205153e0263c3e095f7f520157b044d77c804c7e9c8080acf700959fa41af7f15139e7a243e4b049e3e72549ef82c4149a9b213cd771046be348414dff0820a1d72484df882050f8046fdd00eb5019eb3818801d311052ae460a7bcd01029a02900f738439afc1100200b730408c90182a2e28830c2c20863024850e8b0a261b081c11808f861e128c0d842217820e140a0933257c918e31461a4187eaf6de1ba2708d81a3b2d618bd16c2b1532a053124b45a834f71d2366648b895627049c860f91c23445d09f1081b43084b06209c0e800eb8beb9aeb83eb98e398eb9cf41aeb8df389e982e39ce41af982fc0bf40bf38de98ce98df39cf18dec0beb89e389fc1af98cec1ae40bfb8dbc23cb858c1a8c0d8c188c1d8c0c8c098c3dcb839c0b8c1c9c1a54180c316c156c104c183c23ffffefbeffbeef7bbebf8c2104c1100c010
def q5a:q0g:= (47,2,6,524294,51,11,1060,q4Y)
def q54 (i:Nat):Nat:= 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def q53 (j:Nat):Nat:= (if j<1 then 0x90c4083f321d6cc55f504646019c44204dfc10cf28937f0432053910ce223b02400980bbc34c65818045e5f095406f016f31822b00f789912c221f5c0114f24249ce0e08c5fc120656c06b2083990d70859f22264171411812e90b633045ad93564ac98ac1927756b1df4473c74045ae40c7bc4213fdaa08c1dec4c97b82425ed04f3d690c2f0864391ec72208d390a7d7c922807c0191010fa1911e02bfb8240e4c43990d011c06bd692267e463b811dee091ec041cc873e3c9046de215e623de216f1097a08640ab2623f9804abea9226f20245bf630932fde02207c2399086b88877f60496e239ac50c021f5491180a7108bc843247a20643ec231f50022efe0c114fda0958225a38918c18c308840c70fd088c0683056b01e8ec1e8cc2c288d0b416286c21c0109148e1a828738784a282029c20384833040b05c2684e0814120e020441e0b05549d41d33d27d1c513d084fe4f74f14e5cdecd84d14ca4c34bccb4cab49f497c8747fc77c70c66c60c57c51442437c2fc26c1ec1440dc02bf9beb3e4bddbd73cc3c23b73b1ba83a139739238c37fb78b73b6635fb58b4ab44338331322317307af72efae7ade2d5ac72bcab6aae2a129328a280a74a6ba5d251a49237a29a1f211a061fb9f29e39dc1cc9be1b89ac1a519918f98618097996c96115894e14513b92b1229191109080fd8f80ef0e18d48c70b88aa8a109788d88187906e06905c05604e04083302901a80c00049718e4c0b36e11290e6d2997424c0b9261cf970e52b97315cb95261d8532e4ab97614cb9ca65cf532e6a997744cc1735c271330008982c5cc02266041130937948c5c8c8266017b0528b970cfc91846550c2628b983612c82e3e58513308c2711a9cabe265d58302aba833c4cc325e51382e23159451dc19c266176322389989d3c83c2e5cc7ce6137946d3c830e65c3372688b976da48ace60cf232a4259095ec14c2662673060a5900054c162a612172f0bd97886cb3afa462c1268bd9189c4b86f5cc2173103d8201fb9848644e7b050369159bc8acde1134322bd78445bc222c61857b271159411bc2251e61f1f2d03d829e140aac6188772e19f924dcc19226608830280998704cb8c2e6194b213c5837e0c0bc2e5c62f2853784553c8182661d7306eb784512c83aca4477f2460998808ca9a4654e3f24c3a970dec13d8cc513f24f0b9815f4bc574c555b0f009973ddc194de1106b22b0998943c9180e51b07291ff6febfbff77deefdbff7f6fddf7bdf77ebfcff7feff5fdbf77def7ddfb7f3fe7dcefdc6309c6308c63061e3060e3060a30606305c6305c2304c630cc6109ce1060e10606105ce104c6101ce10e1130e0530a0530605305c5305c13020530e0d10cc110a0d1060d105cd104c11020d109c43061830604305c4301c43060c10608105cc101cc10 else 0x23fc480cb7845bfa208a1e04c73d81137085d8158ef1090e22602dc5c887112c08e223888e2258134029f023bd8325d2859f446065d28576447019d81200235c08603afc001907c8877046f6022e212f4)
def q5f:q0g:= (136,3,6,1638440,86,12,1083,q53)
def q58 (i:Nat):Nat:= 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def q52 (i:Nat):Nat:= 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def q5e:q0g:= (53,4,6,0,0,9,0,q52)
def q57 (i:Nat):Nat:= 0x834601a000
def q51 (i:Nat):Nat:= 0xa295fdb2e3ca3070852bfb65c79460e30
def q5d:q0g:= (2,5,6,0,0,3,0,q51)
def q5h:Array (Bits × Bits):= #[(0xffffffffffffffd8fd630dda8e8aa61c90014d,0xffffffffffffffd8d42304082801a102900145),(0x2762dfc636db2d3474067090,0x2120d82a34960818c4045090),(0x3ec100918c681557416c0816,0x1ec100818829154701680800),(0x19cee55353e34c9ba0a86e6,0xeea5424062a80ba0284c6),(0x3721940b48c0c06e80091ef8,0x2721140b40c0c04e00091a38),(0x30e98f28487160298718700,0x30a98f08487160298418600),(0xffffffffffffffcace0a51892172a62383f801,0xace02d1892132a62281a800),(0x0,0x0),(0xfffffffffffffffc3135226350618b47fd9801,0xfffffffffffffff43105024250c159053c1001)]
def q4X:List q04:= [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def q4W:List (List Nat):= [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def q5g:Nat → q0g
  | 12=> q5c
  | 11=> q5b
  | 10=> q5a
  | 9=> q5f
  | 8=> q5e
  | 7=> q5d
  | _=> q2Y
def q59:Nat → Nat → Option (Nat × Nat)
  | 12=> q9a 8 37 4 10 3 3 q56
  | 11=> q9a 48 123 4 13 6 3 q55
  | 10=> q9a 79 299 8 15 8 3 q54
  | 9=> q9a 39 99 5 13 6 3 q58
  | 8=> q9a 1 5 1 8 1 3 q57
  | _=> fun _=> none
def g383:q0a:= ⟨383,12,fun j=> q5h[j]?.getD (0,0),q4X,q4W,q5g,q59⟩
set_option maxHeartbeats 0 in
theorem q5o:q5D g383 (q1B q7E)=true:= by
  simp only [q5D,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qcr (d:= 3) ?_⟩,qcr (d:= 1) ?_⟩
  all_goals simp only [q93]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe3:q1w g383 12 0 1=true:= by decide +kernel
theorem q0J:q1w g383 12 0 1=true:= qe3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe2:q1w g383 11 0 6=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 1)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem q0I:q1w g383 11 0 6=true:= qe2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qdZ:q1w g383 10 0 6=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 1)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe1:q1w g383 10 6 13=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 2)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe0:q1w g383 10 19 28=true:= by
  apply q1L (ar:= 10) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem q0H:q1w g383 10 0 47=true:= (@q1y g383 10 0 19 28 (@q1y g383 10 0 6 13 qdZ qe1) qe0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe8:q1w g383 9 0 3=true:= by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qeb:q1w g383 9 3 36=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qec:q1w g383 9 39 36=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qed:q1w g383 9 75 36=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe9:q1w g383 9 111 8=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 1)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qea:q1w g383 9 119 17=true:= by
  apply q1L (ar:= 10) (rows:= 0) (d:= 2)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem q0M:q1w g383 9 0 136=true:= (@q1y g383 9 0 119 17 (@q1y g383 9 0 111 8 (@q1y g383 9 0 75 36 (@q1y g383 9 0 39 36 (@q1y g383 9 0 3 36 qe8 qeb) qec) qed) qe9) qea)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe5:q1w g383 8 0 36=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 3)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe6:q1w g383 8 36 8=true:= by
  apply q1L (ar:= 8) (rows:= 0) (d:= 1)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe7:q1w g383 8 44 9=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 1)
  simp only [q1K,q1C,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem q0L:q1w g383 8 0 53=true:= (@q1y g383 8 0 44 9 (@q1y g383 8 0 36 8 qe5 qe6) qe7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qe4:q1w g383 7 0 2=true:= by decide +kernel
theorem q0K:q1w g383 7 0 2=true:= qe4
theorem qfi:q1V g383 12:= by
  intro k hk
  interval_cases k
  · exact (rfl:q1w g383 0 0 0=true)
  · exact (rfl:q1w g383 1 0 0=true)
  · exact (rfl:q1w g383 2 0 0=true)
  · exact (rfl:q1w g383 3 0 0=true)
  · exact (rfl:q1w g383 4 0 0=true)
  · exact (rfl:q1w g383 5 0 0=true)
  · exact (rfl:q1w g383 6 0 0=true)
  · exact q0K
  · exact q0L
  · exact q0M
  · exact q0H
  · exact q0I
  · exact q0J
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q9F:Lower true (vars 383) (graphGoal 383) 13:= qcE (hints:= 12901687553) (by decide +kernel) (q6W (g:= g383) (i:= 0) rfl rfl (q1c q7E qg7) q5o qfi (by decide +kernel))
def known383:= q38 q7E 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qgc:Known true known383:= q3a (m:= 383) qg7 q9F (by decide +kernel)
def qjr:List (List Nat):= [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def qbd (i:Fin 9):Nat:= [4,2,1,2,3,0,1,2,3].getD i.val 0
def q0o (i:Fin 9):Row:= Fin.ofNat 512 (1 <<< qbd i)
def qcL (i:Fin 9):Row:= Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< qbd i))
set_option maxHeartbeats 1000000 in
theorem qde:
    (∀ i:Fin 9,bit (q0o i) graph ≠ bit (qcL i) graph) ∧
    (∀ i j:Fin 9,i ≠ j →
      bit (q0o i) (inputs.getD j.val zero)=
      bit (qcL i) (inputs.getD j.val zero)):= by decide +kernel
abbrev q0m:= Nat × Nat × Nat × List Nat
def qb0 (rows:List q0m) (base:List (Nat × Nat)):=
  rows.map (fun e=> (e.1,e.2.1)) ++ base
def qfC (base:List (Nat × Nat)) (e:q0m):=
  (q1B base e.2.2.1==e.2.1) && q1H e.1 e.2.2.1 e.2.2.2
theorem qb3 {u base rows} (h:Known u base)
    (cert:rows.all (qfC base)=true):Known u (qb0 rows base):= by
  intro e he
  rcases List.mem_append.mp he with hm | hb
  · obtain ⟨r,hr,rfl⟩:= List.mem_map.mp hm
    have hh:= List.all_eq_true.mp cert r hr
    simp only [qfC,Bool.and_eq_true,beq_iff_eq] at hh
    exact q1I hh.2 (hh.1 ▸ q1c base h r.2.2.1)
  · exact h e hb
def qeR:List q0m:= [(151,5,94,[48,33,133,118]),(173,5,61,[32,83,116]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(247,9,478,[48,33,133,118]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(369,5,94,[16,82,131,100]),(422,5,61,[32,49,128,81,116,100]),(440,5,94,[81,130,118]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116])]
def spri:= qb0 qeR known383
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qgO:Known true spri:= by
  apply qb3 qgc
  apply qcr (d:= 6)
  simp only [q93]
  repeat' apply And.intro
  all_goals decide +kernel
def moA:List (List Nat):= qjr
def sgY:Array (Bits × Bits):= #[(0xf4e2669a6837f027081c0f22055df808222736,0x40209409843f007000c0720001df800000733),(0x601c324b069010597803f9010a2609fbe0181f,0x2080a02e269000187801f800000000fbe0180c),(0x250f0dd0188027ef8024025e13c1fd105e4930,0x22808d1092003e78000000e03c1fd001e4031),(0xc9c0d906874040901240ffc4fc1e1027e41fc0,0xc0c0010ec000000000007fc0fc1e0003e01fc0),(0x1028d4b1279c83fa01f1902f20e021fc806260,0x1028d4b1279c03f801f1800f00e001fc006000),(0x86910025492109002481248fff0841ffff8000,0x9100a343a000000000000fff0001ffff8000),(0x81412a020041fe000ffffffe01001009,0x814120000001fe000ffffffe00000001),(0x28004905ffc0481fffff04000804208c000,0x28004905ffc0001fffff000000000000000),(0x3a518020b05fffffff08400880910680110480,0x20aa0103c5ffffffe00000000000000000000)]
def sgC:List q04:= [(64,0,447,0,13),(128,0,383,0,13),(256,0,255,0,12),(32,0,479,0,12),(4,0,507,0,12),(8,0,503,0,12),(2,0,509,0,12),(17,0,494,0,11),(7,0,504,0,7),(16,0,495,0,13),(3,0,508,0,9),(32,1,460,18,7),(16,2,424,69,7),(9,16,486,0,8),(0,32,94,385,8),(16,4,353,138,7),(4,8,227,272,7),(0,8,227,276,8),(2,1,460,48,7),(256,8,227,20,7),(14,0,497,0,7),(8,4,369,130,7),(5,2,440,64,6),(16,256,135,104,7),(10,4,369,128,6),(258,64,189,0,8),(34,1,460,16,6),(28,0,483,0,8),(0,16,486,9,10),(260,8,227,16,6),(0,64,189,258,10),(9,0,486,0,8),(36,128,347,0,8),(260,0,251,0,8),(35,0,476,0,7),(256,32,94,129,7),(4,2,440,65,7),(0,128,347,36,10),(56,0,455,0,7),(32,256,151,72,7),(1,32,94,384,7),(40,256,151,64,6),(11,16,484,0,5),(15,16,480,0,4),(36,0,347,0,8),(2,4,369,136,7),(258,0,189,0,8),(64,1,396,50,7),(268,0,243,0,7),(8,256,151,96,7),(13,16,482,0,5),(33,0,478,0,9),(11,0,484,0,5),(134,0,377,0,8),(13,0,482,0,5),(8,16,486,1,9),(273,0,238,0,7),(264,0,247,0,9),(44,128,339,0,5),(1,16,486,8,9),(352,0,159,0,8),(289,0,222,0,7),(2,16,484,9,7),(39,128,344,0,4),(256,64,189,2,9),(128,32,94,257,7),(3,128,344,36,6),(20,8,227,256,6),(48,1,460,2,6),(32,128,347,4,9),(37,128,346,0,5),(259,64,188,0,5),(265,16,230,0,5),(2,64,189,256,9),(4,128,347,32,9),(16,8,227,260,7),(296,0,215,0,7),(64,2,440,5,7),(64,256,151,40,7),(72,256,151,32,6),(96,256,151,8,6),(257,32,94,128,6),(41,16,454,0,5),(44,0,339,0,5),(69,2,440,0,5),(266,64,181,0,5),(19,0,492,0,8),(49,0,462,0,8),(152,0,359,0,8),(128,1,332,50,7),(256,16,230,9,7),(4,16,482,9,7),(8,128,339,36,7),(16,64,173,258,7),(6,16,480,9,6),(136,4,369,2,6),(272,8,227,4,6),(384,32,94,1,6),(73,0,422,0,5),(262,64,185,0,5),(265,0,230,0,5),(274,0,173,0,5),(274,64,173,0,5),(276,8,227,0,5),(292,128,91,0,5),(39,0,344,0,4)]
def sgA:= moA
def sgD8 (j:Nat):Nat:= 0x1000090fd30b281002edebeda1759cedd17588f587f42ef25c4befc9513fe9b94549814c153549814c120f055354930483a454d524c120325535493048198edda54c910
def sgD9 (j:Nat):Nat:= 0xd41b34204741039105268403991050687dc08000035a0a59104010c882ef4310000067a320057a1640060818013810000ee00cc600000e06504339883a8461d12300009020000d6071810004e6200037d944cd86b6100008d840000000001b6100007a21b040cbc70497c248c00000000022c200001d6090174194188a0ae1220a46f606496407a0b20804d9158ddc05c25881835e27c1360287f60f012425a06a0fa0547940142720dc000300bc023e00267e0487c048166021c94099e01470075e040680a3a00058063b2e8f8dddf68d834bcf32dc971dc22f3baed6b06b9a667a9ca619664a90a3a87e1783e007d1e072db66b9a5669926297c5b9665494a4b9204490a408f43b0e4370d4330be2d89d2307317054130440f03409c1f05c0089cbc22727089a9c0af06e8ba6b91e9ac6f94ae2e9aa8ba6a4771681fc89d1e9a42bc4899e9a22bc4848f2205ba67d16a5e45a9744f2dc10cb6d8e61a77b665eed987fb65e854d72dc658b71959bb7524e61431c64e8f052a0c949c2e5183b542a54903db8214ea0787a71d7e9c757a71daed063fb814f6e4427c40cf6602a18306960c009cbc46f1af0bcbb46f1ad19c6a05f1e705cb981f2e50dcb8cdf0529fa44a366101bc63c6f18e4ba5353e94c43b62c072ca03cb24ee9c797c703ff0ff63fd2ff0bf6afd63deaf3d39afe5bf7f4deeb7b6debb5fcd7b75ebd6f757ed5bf3afcdbf1efc77b1ddc6ff1afc5ff16fbf4afbabedadedb7aecfda7be9afa5be1ff87f61ef86fe17fea79460530e9b94605306eb94605306cb94605306a794605306d79260530ec59260530e519260530e515260530e63a464d20657a464d20aa7a6605206a7a6605206d79360520ea791605206cf916052064f916052054f9160520ed193605206dba154d206d8a954d206a4a954d20661a54c520edd954c120e91814c12054d814c120549814c120ec5534c1202e5534c120e91524c120e61524c12054d524c120605514c120605314c1206a3a464d10663a464d10ec5a564d10ec1a564d10ed1a960d10aa7a7549106a7a754910e9f9354910ed19354910ec99354910e9d9354910e9d835491064d8254910edda54c91054d52481105495148110
def sgH9 (j:Nat):Nat:= 0xbb000000000000000000000000800000000000c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c500000000000044020000000000000000000000000000000000000000
def qel (j:Nat):Nat:= (if j<2 then (if j<1 then 0x9c72fd9472fd9462fd9454fd24567d9c42dd9c42fd94459cc4421dbc32dd9c325db4258cc422dd8c183d24185d24069cc4089c9c01bdcbf1a5cbf2ddabe83d23e2cdabe8ac0be01dabd01d93d3fdb3c01dabc01d9bc01dc3b01dabb00dd3a00dab900d93900dc3800d93841d43741d2b740d43740d2b740cc3741d23600dc3600dab663d2354fd23511db3419d8b41bd83419d8b31bd83319d8b241d23215d9b100d9b000dc2f00daaf06daae42d42e42cc2e11db2d19d8ad13da2c19d8ac11db2b17d92b13da2a17d92a00dd2914d9a941da2815d9a801d92845d82800daa706d8a708d82700dca600dca500dd2400dd2300dd220cdc2216d9223fdb2101d9a117d92143d8a107d8a145d82109d82101dd1e13da1e08d81c3b5c9b3b549b3adc9b3ad49b00dc9a3bd39900dd1916d91803db9709d81701dd1513da1517d9153bd39500dc9200dd1100dd1014d99016d91001da8f41da0f17d90f43d88f01dc8e03db8e00dd0d32da8b8ea90b2fd90933d88921db8833d88829da0733d88725db062fd90633d88663da0529da0569d9052fd90571db8169c98168c9817ca9818ed9003dd37778a9c07aa900ffe7febff1ff6ffa7fcbfddfeaff37f7bfb7fdafec7f4bf7dfaffbdfdebbfddfdefdf7ebbeddefef776ffb7ddbdebff3fb9fbbfddfdefeb7ddbbfdd7edff3ff9fecfee7bf37f9afcbfe3feffd7fdbfe5feeff57f6bf7dfbaf7f7bebbfddfadfd5ffaff57f6bf75f7af7d6feaff4ff9ffcffa7fb3bf9bfc7fda1e51306a3914c1a5e453068b914c3a264530e81914c39464530e51814c39260530aa5814c1a960530649814c1526053068f98481a8e4d206979348198e4d206a391481a3e452064f9148153e4520e8598483a06612068598483a864d20e91934839864d20661934819564d2064d91483a960520e9981483a360520e4d814839160520aa581481a96052066181481936052054d81483a154d20aa553481a954d2068553480a954d20e9531483954c520aa531481a94c52069531480a94c520e9130483a14c120e6130483934c1206a130481a54c12068530481984c12065530481814c12054d30481524c12054530481314c1206a393441a8e491068f9244183e4910ea193443a564d10e9193443a264d10e8193441a864d1069593441a264d1066193443a864910e8d92443a1649106a192441a364910661924419364910aa583441a960d10ea582443a560910e8d824439560910e4d82442a9609106a582441a56091065582441936091054d82443a954910e9d52443a354910e4d52442a9549106a552441a35491064d52441835491060952443a54c910e5532442a94c9106a532441a54c91065532441854c910e852044393481106a120441a54811068d20441984811064d20441854811060d204415348110549204415148110 else 0x732dcb87285c74710dc116f71bb66df5b536ca1b036b45ab66a01a5968f5a0d67ed9df66e99a3661595664798f4633d8ae6209858608d8025f457a65e217765d657325c316f65b0969a599962a58355f057415ae562156b553151d53f54e152f94a751d945250713f74f713bf4e613744d493294bf52e54b212ad4a3125648b51fe47251a045e914744610e242e5083417104740c8fff3f08f8a3db4f3f3c20ef03b40eaa3a44e753974e423880deb3740da73604d4e34b0d0d33bccdc3338cbb32b0c993200c6d3178c1e2ff4bd12eb8b7f2da4b342c30ae42ab0a7d2940a2a27c89d526e0993259894024948f423748b4223885e20d48061f547be1e307621c906f11b406af1a1065118645ea16a457d152051113dc4de12e848d11ac44e109c3ef0ee439d0df835c0cf03170b7c2ba0a50275096422d07ec1d706d41990584142046c0fb033c08c011c00075d37764dd7764d97764d4f761d37647d2f61cdaf635d8f34dd37365ca7365ca720bdaf01ddaee1ddc6a0adae61cdae447d4620adade47d2dd1cdadd6cd9dc34d9dc6cc9dc6ca9dc2bda584dd3584dd3571d5cd61cdcd60adc5626db5646d4d647d4d51cd8d51dd8d41ddcd31c5cd326db5246d4d20adc511cdc500bdc4d46cc4d36dac937dc436fcc4377db4237dac287d24293c8c28ca9c290a9428dd8c18c5cc191cc406fcc3f92c0bf1ddaba46d2ba0adab954c1ae1dd9ab2ada270ad9a734d8a70ad9a647caa50adaa546caa51cdaa30bd9a135d8a123dba06fd81f37d81f1dda9e2bda1e0b5d1d0a5d1d0ad99c48d99b0adc1a1cdc1931d91649d3961ddc1565da152bda156bd91531d91547d4155bd39549d39549d3941cdc947fda9373d39353d1936bc9936ac9937ea9930adc121cdc111cda900bdc0e49db8e23db8e53d90e31d90e47cc0e46cc0e1ddc0d6fd80d37d80d47d40d46d40d46d48c92c28b92c18b92a98b6ec28a37d9866ec28537d98437da8337dc0236dc0280c2828cc18290c18192c18013dc7e13dafe13d97e40d47e40d17e01dafd01d97d01dc7c01d97c01dc7b01dafb41ca7a63ca7908dc7941d47841d2f841d4f74bd377415d7740dd7740d4f73fd37600dd7618d8f513da7419d8f401daf101d8f13ed37101daf001d8f001dc6f3bdbef0fdbef01d8ef01d9ed01dc6c01daec41da6c13da6c13da6b00dd6a00d9e951d16859cc6808d8e811db6741cc6541cae540cc6540cae510db6439d46313da6108d8603f5cdf3f54df3edcdf3ed4df00dcde3fd35d00dd5d0cdc5d43d4dc5dd35c56dc5c18d9dc56cc5c0cdc5b00d9db18d8db05db5a19d8da09d85a1fd85900dcd604db5600dc5514d9d515d9d400dcd108d85100dd5014d9d000dc4f00dacf14d9cf18d8cf19d8ce01dccd00dacc63cc4b62cc4b50a94a5edb4924db4983d2482cdac866cc482dd) else (if j<3 then 0xe4f6b20c7814441e1d451138b15a449c588f812716293ca51271623e05bff5e71e80004a953c8a9a459fe26100b479e6c1468ddfe98200ad9b491435fc749640392497af884632975f8851b2afaf290a0039a51fd71c00842adff313009a3afbd610a12bf3ea1000028954ab2c268c98892a9c0f0851b7fad640688f4f8ea51944788225cff6e4d44ab3473423dfe8544ea32fad612a1519571c001acf5f62000d6605b93ea1350bdc7f08e8ac6680ed451ff856c045b31974f00c6525f0db9a2b510b34dff2e9900732a9f140522a7f109d90bafb884e335ff2e9900232acebae2880030691fea3ac8568fd970d6e7a102216adfa19c03247bffe3b1a012155ffe6d8900252b6bc70151f280b4f7b0644e3f5c110354753c24268c7184688b5dfa10c26dcde451942361eeffc76340242bd9a58445fa11a890defd632456194b267895c699402c5f94242721d9f8398d0833e0f4ca2f61ce66484fa463668a5188b850fff406a0a99b9dd8706123ec50d6484fa463001dd5c92462875fa106881d3cc04d95de4e660f9d02d806a1403c230fe348813b497c71e746e180115a803d3f84143b0039b52ae0b416c330642372809290150513122a37602c251018081260a1089e1382084285c1b0a061841b60087104c0430a60c3018430c178271890642646040760887c15857876a103085f137c0a19a0ac14c964251ca0e483c178550746e42c82b12478800810a72041d03c09747c8fe890a013c5704da07218528aca04c180699c06aa7bc2051141607024831134264c806060a0306d04052a15c230a828109c0f8341a0f94c844086e19c4a0805c0841b01b814470208380584248550d07a09ac001fb0809e06804d02015c2d0a05e0d00e81460e0730302205a0c5c10250500934000ae0b6180d01e030059c060702a08f41b83b0404e04002b0b60c01812d0ba180b80bd05c134201002203fc4f0601003007707f01e07383cd6b329cbe72d9caef29dc9fb258c8a3200c7971ccc6cb19ec5f7157c50f12fc3e70d6c313097c1d7056c0a300fbfd2fe0bf42fbabe12f70bd66f42bc8eef1bb6eeabba6ee7eb9bae52b8eee1bb7eedd8b722da6b626d6bb556d37b466cffb3aacd5b302ca4b246c80b17ac48b0cec1db022becaf1abaaae2eb76ad82b47acdeb27ac22af1ab72aa2aa36a66a946a33a8729f4a75a9aea63296ba53a92aa40a8d5a2f6886a1fa866a17a84ea0ba826a0467fa9f9a7d19ec27979e1e7779d467299c4a7029bca6dd9b066919a2668199ca66a997664c98f662e987e61097e25e097625d096be59095b2542946a4e492a2472910e40b8f563b88e8a3828db63588cae2f28b3629e899e22d87fa1d786ca188852e11c83a20ab81c20338021ff57ee9f867d81f3b7c35ef37b65ea779c5e427859df17721d8b75d5d4a747dce6 else (if j<4 then 0x120c1a341832eea18f40f0481e622cf3147d30b1c7162e5e0c5daa6d462e8c16b960addc822f8b105b2931f31e2d03091f4c2c66f41a20f5cb056ee415cc87088e848e84de83441a3d1822f8b10000d7fe0b4030fae582bb91eba5485f162b2b9a20f6a5d13d539230d2581e050698af46a2cbe065e6c2607cba5919287107cc3265908a71b8211496d9b0356085e1d8c205392c0e83170e00319d4401338329be1106005f16207c904196c45f16202ee9251c8c930a570657040cf9f2d8462055d24a407c904474247434cc828fa616306347f5199850000170201341a9e0fb81f703ee07dc0f2de6170de61000049d5f1a8c58d5cc1909f50742057e27916ca00067ae3483f35e880031a4d7e5a7400002a348f8fda2000c4927fa87b018ca77e4f06c002512b7e751b000234997203419bd3054d87ccc96c38257cc163f340008a17a195aff4882ed00003e078400ff468018cd4fc40240002a1c13f84e5a4415683f924e00485231d0e24518dfa104f0879fc7c4d13c7ff83800001cda4feb2e002a152bf5dd120064377f863800001cda63f947000004234d7fd238000009da6bf82e045b2d76625fff8a9a8010693bfe68a0010892b76f84104d7dbc0b89dbe96a401c6611e990c47a64355fb658009926f9ff61b00842aef9f4d0046cc4fc0c00270a6eed00d841538591a239bfaa01878003a23df9821f88b204a8e3f40e40111d9d3e611a801d0e1d3dc9321b12de90404b67b00d42c317c8d8052180efcd2101c864ffdefc441133adbde1081209ffa4bab00c683fafc208ca33e18a04eb33be4401a123ff2c38919663f0dc499e1fb34a041b3c9d86a41a4b789425dff314003c483580f5e4060e9f2f1044eb7a4139c034833cce3d8106534ff0922420630fbad6b019238cdad08d1a6d68468bbf43320648fbe30a811a3afd6124801cd2adb793a4dbf34500028495d2eb004a8f49c4a931ac065c3e66358fdf0a6127cb780b13dd37444ff08082c270c17c808034845b7c03c02ace14b7eb8a50042d2ce1c6839e52e227759543227b7930c95db3930b2c3750a0e67ac4a2772f5b142166d3a76245d3cdd448cf961ac87ac88d1f90808c450d0d1b12d089fd25511813b40738a28d9503f331d3c6e20fae91206d2039f503424f284428a985de38366eb4305c4a66dd8dc2a78dc41a07e9634c3d17326fe31a8000e69371f10085298f63d64814cebfcea40007349bbc4804294afeb6050137fcba6401cca8fbbc48032950ffd1a8000e69371f10085295ff83500009d256bf5c3a04db0e095f3053dc7fd8402d239f062d190001711afc8c93000150f2e406835fefec00511e7fc50e00041a491d4d123e41341d9fb6c164f3ec1439e096445ec1435c12c891f5813322631e5e80071a27da1225de240214a57f5b02809bfe5d3200e6559f else 0x35dc301da928e045843494f16eb6ec185024fe49088a5271834836ff1a18d5bbe2838d254cc8afa7e714205ee1ae601d2ed91b4e9d275ba9632bc6d10d6a886186c4e59c62a382b6c7d210d508db298808feae8ea0386ef8e342c91a3133e3416a2e172f7304a3ec1072c8427d312ac42d0d73093d3331d32c11b117a0f0400031fe5d4543734c133e58267cb0505e2b99012fa25142286a75208df895ef70614d88a93ca2c66c44401e8c6c7a68a281a0a8fca33668daf580cd1cee0b43ea26c98f0a483b480ca0f51782068d)))
def qeq (j:Nat):Nat:= 0xc00610b72b813515482944203880e207a351422c16800008701a0004eaa05fa2f400a0d0001237c1e000361303240f8000132821414a8a707e017956201f74b02a99f60b903701281ee061047806088800275c000000010617800281ccc88717bb381380b008934101d001005000081def00044000000489c03ba2d4058000151040c198025a80bbd408a4b3060008802a03b04d19900060af06a00cc1b40350218034a1e8e8001889ca0606606e59780a800000083e0002094028024807ec5f04100a8c0605800103100000009828e7428a14542800e000810e6819a12007908005916
def qem (j:Nat):Nat:= (if j<1 then 0xbe0f07e2408e0381a80a9c2a5fe94ca46e8dba2ba88ca17e8189fa27c09e6a7589cda7169baa6b89a1a65c98e660f97ae5bd960654c949250193424af923646390f24158f8e3b48dd23388c3e2df8ada28889a223388221d4869e17f850211583a20b5822a0358019fd97ea1f7a7d41f287c1dedd7ac5e73791de257805dd576c5d86753dd127359c9f71c1c397011bd86e69b646c79ae06ab1a91699da2b67fd9bf668d980652d90f634d8ab61c185060557ee5e997895d857435c8d6f65b316a159e965358915ed570559555bd542549d5035351492518541a4f4938a4d5532c4bd12bb49a1234481d1d0467115f44c90fa433908140f900b3f60fae3e10f3f3bd4eca3a64e7038b8e0b378cda43594d26337cca03180c262fccbb02db8b2a2bb0aac2a1ca4728149ec26e097b252091c23e08b521e08341ff07cf1e747841cfc70b1b646a019e464418345cb165455914b851513784b51208442101c3d20e743660d083130b982c70a8827d08d4206073018e053c12a042c0e0028c06c00e0000d3533d3253d2a53d2a70d2a6dd326cd2a6cd742bd552bd352bd342bd152bd3065d3524d7523d74a3d7463d3523d34a3d3463d32a3d3263d2a63d3462d3262d3062d34a1d32a1d30a147514474b447454cf41473314732b4732549f29377253755337353373472434727351143511734b1434b17331173510435107347043470733107327072a704746f7742f4742fcf40f7342f4750e474ae9f48e4742e7730e772ae7330e732ae7330d7326d4752c8f4cc4746c7726cc722c7552c7352c4352c7b30c4742b7552b7352b474aa772aa7552a7352a434aacb40acf309cf2a9cf229cb509cb4a9cb429cb309cb2a9cb229cb029caa29730677750647506774a6474a69f4867744647446cf40673506734a67344673306735057346573305732a573265755247352447523474a347463772a377263755237352343523732a37326347522874e2474627726275522735224352273262b3042474a1772a17552173521434a1732a1cb500cb4a0cb460cb300cb2a0cb260cb0a0cb060caa605b43613515134b5134553f4145f2945f293534d2234d2134721343213511134b11343113510134701742f3f40f4f30f2f48e274cc6722c1552c1552b1152b1552a1152a974893f4296f309a72696b309a2a69aaa49a262913508134a81344813507134a71346717506174a65f4862f486174466f4063f406175051746567425374251352417523135231f4e213521bf4206f2606b260aaa40baa20034d20f486fffffeffdffcffbffaff6feffeefbff7feffdffdfedfddefdbfcffbffbfebfdbefbbfb7f9ff9ef9bfe5130e45306453060530e6120e4d20e45206612064d20645206052054d204c5204c120e4d10e491064d106491060d1060910549104c91048110 else (if j<2 then 0x8542afd71e6b0001ba52f32a1711238ebf7ff5900019256fc84a20ef8022451fe210c4033a489fdf9a32a01aa54ff9d546c4023a546f1303b14a434fce22a254693f9219251fbcaa48401349667f570b89f3fe98dc21988015dac77dd6892bf5c0388c3f133a274386132019fe5cc0e147f0fb81c46c3c7ae0468c7d61fab89efc9a20b945f7db09027299ff02a48006894bfea2802c8f3f1be002a8f332078ea32ff5c000511f31a0b1ccefe85a2d7961c802b662e4de5e45900215ab33f9a10046cf3f5cf8161c2400c93b7e7ff8030db40189377fffed4918b201a5317fcd41f4058903e67a02346effdd5880035684d3f9680000a344ebcffc1a9230090027505fe3cdf4015486fe2d5648b317a7c7e7088e67a4e4bc4488f684f0a1f860910bb4d70cb40095997f1baf9001e124b0f3eb22d957d7a4fb3604da00e4a1bff38138f3400992e312f6b400634373e862800568c0fc300699718c9f10a85d5deeeeb0c48001272fbb11e3d8c1a00849c7eff1005ca03a05d3c32ccf9e768b04664ff587950000099a7bba7b4b248f21b23238fe78c0c0200744b1fcf181804008e963f9e303008011d2c03ff113dcd30024b5c7c21267d400396acf8d1467d400396a9848fac4401492e381f10c01e3467fe3c48a0600786a4f3db1cfb1801e1a80bff70c70808185a833c3f1c202021698fcf40c02000536a3f3c00d13affff8a5820029a52f5febf0288010696741a0795af234006349def9a522a0049a61ff5b0e10922aec71c001c669fc002245ef98f9680cc00ced41dff8c0c0601769affd2450c0400826a5e56be300052495cfea000d23bbeb80000550c741a070ed79f8310000093597c32d02012b3cf88830004c923f903a5200784abfa7006451bf1534b4087499fc385c000d095b5fbe3dc202053a5df9f409c004e591fad02c44010cd23bf0a80751ce8340ebcac7cba0151247d99402c8fbf106d20159247ff1fca10401892a7caff00280212547e4fed141d8ae7f43fc6c01c91b1d78104024929b3fb454233f510c01a33cae7f000891df7a0d039fce00289cfe700144ebfea7fef0202002499313ffd00551d7958f1e400634a0fcfe7b0990a05a47dfc294020039a61fce00689df7a0d0387c5d40892a1f8e27406004925cf63660c00324b8ffb4301831671de3fc09801849c2604080631a2204f21b47e02200ae11603224341a6060f8671591c138c0820861304246e198d455064bc0e2891284041452a649e150060104911c46c0e81204844240e12031e183648017096800a0b9214370e9330fc334103b20d03c09020b82f08d0726d800782d0702c6041b8350d0cb05044266103000c020901f2082782805e118603e83280220ac99060290582a069894281007607e14210301502a8604813a11850500dc128260b82a170660c0 else 0x6793eb688648959a83db84618641099a63c740e409a479934f3f3214290c86effccaac81b307b7ad10a01a00b4fa2e200b4216d680b684ce5ebac8ab347f659b6ea4ab9476bced6888f666748473d1c6577aa891a102bc9cbc82839626a2f0aef5902b0fa5903fcca8341971d13a6892886c51cd17aeaa181e5210518597053a3085c82bba533230d968c235503e7852cdde12e1054384cd36f5eb152d5087ad577bd96597053a3080979abed48861dedce22cd713188a3e3bdc0e231cdb982328bd93305e50bffd5a740f240ff5b6202548eed6ff3ec60018698388e3e6cc0174a8bdfe00ea3484bdfe00f242e7f00051187dfe60016476edd4664dfcfa9e00112433962690c854a571ef6d0d675fe78800aa3edfa000b23d7fdb183000027699fce2e13a8dd40871d0b66dffb7e8002c913f9e1c2751a7ffff8deb89168800e69c7ee43840a0a674f18005c900eac208342861fe3c000d51f7ef000354795fae01c46087df3b2574eb8c98cac0186ad82cd9fc363b400013b4b393d9885c2bead62e10f8ad85013bfde0002a8f34efe348b35f7810311c08e9b3a901543f65f0da0488095a64ff23f0c000592b3ffa38440073457cb1ac01d66af973090005ed03ffd2f00016486e9100d0b669f32a37d4001152d3fccc050014686f84bf5c048000d5abbf949be800056699ff97e8802e480f2ccc78c64f8))
def qer (j:Nat):Nat:= (if j<1 then 0x931828049fe42bc283841e02d972182e205d00b1c0aa0a6ea580092e0644ad55c4d284a03880fc040b33d80010027941c054eef74e2c00016b94095ca329413025e03495f80002ab801520a3400000002022117f049800000001c8a0000006842901a8000160d000001b7817007c6f400001003c03420dd023d028903294fe8079a28da44e527413c0003b160029d8ee000346776bd00e3912003ea0464207ad0400060e5416684f00006894c0f5dcc4233613e02400001b206136c1c182f488ce07302ae84a8449c0e81eab21f70a1e00c406c85a910be431803e824b68c8000096f913938c80cf8213c08c000494341268052054609952d40001b86406c1a0e52540002f4121438564241a148e880911406ce16e001c2214031e01c9d4c224a004a0495e9715160310e5f028881b40a2cc23003785603a0828c42a685a462f003781758258077e0d0c04a80ec000212c403100ce81ad7204892829841aa14ac05f01f1080e067c2c80002b116525c81a0001028211d42b4903204fa0400001dc8d30040ec829b5c90057a0ff415a1c1209de111d2cb821609be13f418d02db210887f081d82de203a16101e98441048813d89ef5c2b2904c7fc9b95c26681370b41c801fd0b780bcc9bb8168000012182ca22a3202000089c2a0110914172402dbd604516008000b831caa3062d0a0a256e76d2d6d000883470ad800000004813064c2869025a27d47ee900c0c20003020c0b2e5eea204000014e01e6911d097cf72ca579504000507700015c654578803000103e407380000100015b3172af9000000027a8e0b48a0600020666b002e2a857cb0c6052d941d370058c039c13a01200869530e0bcbd7776c6100025c03c04104146c1c4a51945ac8c5019704c922c972c81f601e7074800040993d1001fc0f251aa043c779494c5cf1113409a2027c143316d062e8ac0230825e20bae8e00950156034c076ee1004571a0ee8dd2801cf677c68a7e621dc3d779c112021da1ef0b3294280bc820c000085841e3985c441e08d95f5029c01ee00641b9008d270495f02d181830ab0948c2e0043105cf56c01fca0170420124480621e388d416d087e53cf047c0d6805c911840ae4f3e96c82286822130ae662bdb02e806e0156002db9380005176000aa22a139807c988e08b8135822635b962e02401130900028132a04800181b0341038078101800004502617008408a480700004040484c1607191205e731200418002280d404b0409016b9100841608070800008040082a20068497e8d02c84020e0b0dc0208010f4441c0a8186687148001608028a04411148088e3c0500c0a120501474200301c1c1604804642b010193a000180812011500c0e0b148183a0a0001c024604800120e080241c2f00884fa73060a400040f0000000000f80407010100048 else 0x403d05cc06901278235042c000484dc1120146043a0d5414a141a409c08280cd01614b420434a1d02534a4c0e1023f047000040c0c176b1e000d251881cd0313008642381fa836b7b5805942d981bd1410162c1ee221e0ae8138500e82c308de546029383d404e60fa002f83b409980004159853f57faca104fe80c8b0cc10480a7011c23e609b40e4023a09d2057c20c837d061a4fb82ce097502fe128405a2044000002b806b810b03bc0eb01a700c6027c12bee283a9407b457082a081ab44f015e0000325c066801941bd95b3b8892fa6c82002a07741084059a213082a119229b15c4026e52a52bd038c4a38f57828e520e01360ce029782fda7c467c4022a31d28a683900013a05022402ac28494020432114c0d682b80004003404982e345f609a510c00022920c9442800003094d32692c880740ae216b4024258a05f481402c1b36c0a88000c18484c60756081800e8116b11971a5ad6022c0270c6200009a6203c612dc22d31e800064b841b1829207e0000c0e8d2f706ba070ae0500a30aa60750194bd5a0aaa0c100600221091a0a3884f00840a6407b80400c5a40b6945c494805506414f6eac601500004098d83a82d6046403a412000030850000c)
def qen (j:Nat):Nat:= 0x1fffd8340260acff0e695c049961e62b073fe4c016141fe7000114a5dffad88930b3f9cc984002f0b5f5c41d0287ff9b1146197fcf3084026557f2fd08004a1607ffb22804a15b7b883a0517e79a0c051961fdc2650006565f397220392bbf61c200251597fd3800c50edf80c0eff6c42184bff980a812ec02a04ada80c20de782b849387810f730d4217a60040a67f00a40b4fe2128147eb4e000c520b0ec3464260a09054395c884403f158243e1c0206832990b06214830d81a0a35038350906c32190589c24110a0ac28220f82c1e07012b63b45b865015ebb9d6f2d318c2e255ca292b2243e6708cc1782a44b0870f119c2d04a87309e0b00046468c0d3986726ce458cc31936322c6058a9b131632646488c1918222a444c85ca47918f309e4d3c8a5985a609e4c3c905930b2434801ca5fffff7efbff7bd3048110
def qes (j:Nat):Nat:= 0x1094021e25e00490cc0ace241c14ea5b890b0ce4298000832c095c012604024e007811fbc0910205b0dd801f0a44000d42547e00014030212032800b034c2060d69b5a0978268000589140600032b100000008b2fab200000d44af1255010873a14ad051c028000026d08c410505f9d0109981104a6820c000503b250000000011fe0bcc294000ed6f05e09290c28180030000322b4242b4a41aa2b0c2ea7d4022f478c4e5a20593801e405309f8093a598e09050c08508880140cf9295bc51242010000306f00020d39f3f5a0920010940d604c428a0699e1e4afdecb10bd28f0bdc27b098d509009404f13fa5010270228017034b02d9ddf0b980f506d5a1002f59430be0003422c1f4000c18a016412b4aec95213a40de0d7c914476ed246bd0001b4ee82a4970a300bb402d77dc325956447b07e14b50c4011743002ce01510d9356c9641b30000275003b59d524c05490b97a20b00000c1d6076c1ba08280060a802d30396b1e0860c2200d989b485810d07942c164b8acb05943010c6c1fea5f9d044770c0804d45f10960001420c82701d0001008c170000aa40908d8fc028000107880fb04800e30d1d09800000030cd824800000030258184000413c00040fdb5fdc93bc8919f64d03057cb84be2bf000208eeb12a58806831e000204641f107429dc019ab2c19d5285bbd4060349029e24d01b106580e97d05e2327701c109d40f0bc719240bf015eb5841c976351230ae11e868503428830003a7581ae789415b479000002c40ec1499af201ca1432490214b50c226728d01c05a000249e00d903102acb6000000a0c08f02ac23c447c2db0b2a1610290124498d847b4f8329073c16263a000104e621b7d6534a0550002bc4107c080000205d493c0001d8848f49da077800c00000000001e0800082b1071c4910228b0c000cd437cddcfd08d000277548e624000030b1c4b4000012eb5501a00000001040c2a42440293000c2840000d4852f0b58000c14a0c3418f0aa804706641ee0af00030a341930c700016b2896a15000000ad82e301bc0aead600cc09c59280000322067c80c000409800659300b7290607aca0a1a0d2a400f96464968033020ac28686035702e02d568382479c15f4d68149990c50104002921771400253a01a1039b3e122e323b18a5010342351a2a03110000063202613702520603112a0e1a181d0665130005003b161e3d02160e02040c03200f01000009006d0c0e08010c0201130201070600011f08024b0509070c1c03010b1c0102002c
def qeo (j:Nat):Nat:= 0xe802012c810082004024341410281a1a16120a0e06001f36804c120443ff
def qet (j:Nat):Nat:= 0x13ae07e26ca224c0000042410606e07dcc000000001c68540000090200000000c2e001030000000000000000130d6300090c000000000000000000000088c000000083f40000000000127e00caa0700000089a002370009ba000000000000000000000100e08c3c0848f4000000000020800000000000000c19ad500c0b000000000000011480009a00107400000000003448000000000000000185000000000000000000005bc000008348ac2280000084c002050008640b00800125c0061bc05038a780041200205000000c0c000000000000000000000397000d961100c44362122d0052001005
def qep (j:Nat):Nat:= 0x10090e08185081808013ff
def qeu (j:Nat):Nat:= 0xc1009de4c0000284000045004a5c00c9005500000000000000000000000000000000000000000000008d0000000000d40000008c00000000009200
def qew:Nat → q0g
  | 8=> (6,6,7,327686,51,6,4097,sgD8)
  | 9=> (69,5,7,2818098,102,10,4151,sgD9)
  | 10=> (373,4,7,4849791,119,14,4299,qel)
  | 11=> (216,3,7,1769495,85,14,4244,qem)
  | 12=> (30,2,7,327683,50,11,4144,qen)
  | 13=> (3,1,7,65537,0,6,4109,qeo)
  | 14=> (1,0,7,65537,0,0,4105,qep)
  | _=> q2Y
def qev:Nat → Nat → Option (Nat × Nat)
  | 9=> q99 1 113 0 8 3 3 sgH9
  | 10=> q99 26 127 7 13 7 4 qeq
  | 11=> q99 159 691 9 15 9 4 qer
  | 12=> q99 102 467 8 14 8 4 qes
  | 13=> q99 16 163 4 11 5 4 qet
  | 14=> q99 3 59 0 8 2 4 qeu
  | _=> fun _=> none
def sg:q0a:= ⟨511,14,fun i=> sgY[i]?.getD (0,0),sgC,sgA,qew,qev⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeQ:q5D sg (q1B spri)=true:= by
  simp only [q5D,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qcr (d:= 6) ?_⟩,qcr (d:= 3) ?_⟩
  all_goals simp only [q93]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeL:q1w sg 8 0 6=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 0)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qej:q1w sg 8 0 6=true:= qeL
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeM:q1w sg 9 0 21=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 2)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeN:q1w sg 9 21 48=true:= by
  apply q1L (ar:= 10) (rows:= 0) (d:= 3)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qek:q1w sg 9 0 69=true:= (@q1y sg 9 0 21 48 qeM qeN)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qex:q1w sg 10 0 3=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 0)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeA:q1w sg 10 3 128=true:= by
  apply q1L (ar:= 10) (rows:= 0) (d:= 4)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qey:q1w sg 10 131 111=true:= by
  apply q1L (ar:= 10) (rows:= 0) (d:= 4)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qez:q1w sg 10 242 128=true:= by
  apply q1L (ar:= 11) (rows:= 0) (d:= 4)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeB:q1w sg 10 370 3=true:= by
  apply q1L (ar:= 11) (rows:= 0) (d:= 0)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qee:q1w sg 10 0 373=true:= (@q1y sg 10 0 131 242 (@q1y sg 10 0 3 128 qex qeA) (@q1y sg 10 131 111 131 qey (@q1y sg 10 242 128 3 qez qeB)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeC:q1w sg 11 0 2=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 0)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeE:q1w sg 11 2 62=true:= by
  apply q1L (ar:= 10) (rows:= 0) (d:= 3)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeF:q1w sg 11 64 123=true:= by
  apply q1L (ar:= 11) (rows:= 0) (d:= 4)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeD:q1w sg 11 187 29=true:= by
  apply q1L (ar:= 12) (rows:= 0) (d:= 2)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qef:q1w sg 11 0 216=true:= (@q1y sg 11 0 64 152 (@q1y sg 11 0 2 62 qeC qeE) (@q1y sg 11 64 123 29 qeF qeD))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeG:q1w sg 12 0 1=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 0)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeH:q1w sg 12 1 12=true:= by
  apply q1L (ar:= 10) (rows:= 0) (d:= 1)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeI:q1w sg 12 13 17=true:= by
  apply q1L (ar:= 11) (rows:= 0) (d:= 1)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qeg:q1w sg 12 0 30=true:= (@q1y sg 12 0 1 29 qeG (@q1y sg 12 1 12 17 qeH qeI))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeJ:q1w sg 13 0 3=true:= by
  apply q1L (ar:= 10) (rows:= 0) (d:= 0)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qeh:q1w sg 13 0 3=true:= qeJ
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qeK:q1w sg 14 0 1=true:= by
  apply q1L (ar:= 9) (rows:= 0) (d:= 0)
  simp only [q1K,q1C]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qei:q1w sg 14 0 1=true:= qeK
set_option maxHeartbeats 0 in
theorem qeO:q1V sg 14:= by
  intro k hk
  interval_cases k
  · exact (rfl:q1w sg 0 0 0=true)
  · exact (rfl:q1w sg 1 0 0=true)
  · exact (rfl:q1w sg 2 0 0=true)
  · exact (rfl:q1w sg 3 0 0=true)
  · exact (rfl:q1w sg 4 0 0=true)
  · exact (rfl:q1w sg 5 0 0=true)
  · exact (rfl:q1w sg 6 0 0=true)
  · exact (rfl:q1w sg 7 0 0=true)
  · exact qej
  · exact qek
  · exact qee
  · exact qef
  · exact qeg
  · exact qeh
  · exact qei
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem signedRoot:Impossible true graph 14 inputs.toFinset:= by
  rw [show graph=qfx sg by decide +kernel]
  exact qdk (g:= sg) (top:= 14) (i:= 0) (q1c spri qgO) qeQ qeO (by decide) (by decide +kernel)

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

theorem minor_lower15 (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) : 15 ≤ C.size := by
  obtain ⟨k,hk,run⟩ := signedRealize C legal computes
  have bound : 15 ≤ k := by
    by_contra h
    exact signedRoot k (by omega) run
  exact bound.trans (hk.trans List.countP_le_length)
end PEqualNP.Outside.L_meta_1890.BoundsNine
