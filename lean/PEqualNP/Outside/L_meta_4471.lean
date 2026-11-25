import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_4471
namespace Base1007
abbrev B:=BitVec 252
abbrev Sig:=B × B
def top : B:=BitVec.allOnes 252
def zero : Sig:=(0,0)
def one : Sig:=(top,top)
def target : Sig:=(top,0)
def neg (a : Sig) : Sig:=(~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1|||b.1,a.2|||b.2) else (a.1&&&b.1,a.2&&&b.2)
def proper (a : Sig) : Prop:=a ≠ zero/\a ≠ one
def Bz : Sig:=(0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def GC : Sig:=(0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def GD : Sig:=(0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230)
def GE : Sig:=(0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def Dw : Sig:=(0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def GF : Sig:=(0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000,0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def Be : Sig:=(0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def Fo : Sig:=(0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)
def raw : List Sig:=[Bz,GC,GD,GE,Dw,GF,Be,Fo]
def Live  (k t : Nat) (S : Finset Sig) : Prop :=
  ∀ (P : Nat → Nat → Finset Sig → Prop),(P 0 0 {target}) →
    (∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (ih : P k t (insert (neg a) U)),P (k+1) (t+1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (ih : P k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U))) → P k t S
theorem Live.stop   : Live 0 0 {target}:=by
  intro P stop unary binary
  exact @stop  
theorem Live.unary  {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) : Live (k+1) (t+1) (insert a U):=by
  intro P stop unary binary
  exact @unary k t U a ha hfresh (tail P stop unary binary)
theorem Live.binary  {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) : Live (k+1) t (insert a (insert b U)):=by
  intro P stop unary binary
  exact @binary k t U a b d ha hb hab hfresh (tail P stop unary binary)
theorem Live.elimInd  {P : Nat → Nat → Finset Sig → Prop}
    (stop : P 0 0 {target})
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) (ih : P k t (insert (neg a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) (ih : P k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset Sig} (h : Live k t S) : P k t S:=by
  apply And.right (a:=Live k t S)
  apply h (fun k t S=>Live k t S ∧ P k t S)
  · exact ⟨@Live.stop  ,@stop  ⟩
  · intro k t U a ha hfresh prev
    exact ⟨@Live.unary k t U a ha hfresh prev.1,@unary k t U a ha hfresh prev.1 prev.2⟩
  · intro k t U a b d ha hb hab hfresh prev
    exact ⟨@Live.binary k t U a b d ha hb hab hfresh prev.1,@binary k t U a b d ha hb hab hfresh prev.1 prev.2⟩
theorem Live.elimCases  {P : Nat → Nat → Finset Sig → Prop}
    (stop : P 0 0 {target})
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset Sig} (h : Live k t S) : P k t S:=by
  apply Live.elimInd (P:=P) (h:=h)
  · exact @stop  
  · intro k t U a ha hfresh prev ih
    exact @unary k t U a ha hfresh prev
  · intro k t U a b d ha hb hab hfresh prev ih
    exact @binary k t U a b d ha hb hab hfresh prev
theorem Live.byInd  {P : ∀ (k t : Nat) (S : Finset Sig),Live k t S → Prop}
  (stop : P 0 0 {target} (@Live.stop ))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) (ih : P k t (insert (neg a) U) tail),P (k+1) (t+1) (insert a U) (@Live.unary k t U a ha hfresh tail))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) (ih : P k t (insert (bin d a b) U) tail),P (k+1) t (insert a (insert b U)) (@Live.binary k t U a b d ha hb hab hfresh tail)) {k t : Nat} {S : Finset Sig} (h : Live k t S) : P k t S h:=by
  have aux : ∀ hx : Live k t S,P k t S hx:=by
    apply Live.elimInd (P:=fun k t S=>∀ hx : Live k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop 
    · intro k t U a ha hfresh prev ih hx
      exact @unary k t U a ha hfresh prev (ih prev)
    · intro k t U a b d ha hb hab hfresh prev ih hx
      exact @binary k t U a b d ha hb hab hfresh prev (ih prev)
  exact aux h
theorem Live.byCases  {P : ∀ (k t : Nat) (S : Finset Sig),Live k t S → Prop}
  (stop : P 0 0 {target} (@Live.stop ))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)),P (k+1) (t+1) (insert a U) (@Live.unary k t U a ha hfresh tail))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U)) (@Live.binary k t U a b d ha hb hab hfresh tail)) {k t : Nat} {S : Finset Sig} (h : Live k t S) : P k t S h:=by
  have aux : ∀ hx : Live k t S,P k t S hx:=by
    apply Live.elimCases (P:=fun k t S=>∀ hx : Live k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop 
    · intro k t U a ha hfresh prev hx
      exact @unary k t U a ha hfresh prev
    · intro k t U a b d ha hb hab hfresh prev hx
      exact @binary k t U a b d ha hb hab hfresh prev
  exact aux h
namespace Theta
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
def Run {α : Type} (inv : α->α) (meet join : α->α->α) (y : α) (s : Nat) (ws : List α) : Prop :=
  ∀ (P : ℕ → List α → Prop),(P 0 [y]) →
    (∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (ih : P s xs),P s zs) →
    (∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (ih : P s ((if neg then inv a else a) :: kept save a rest)),P (s+1) (a :: rest)) →
    (∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (ih : P s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))),P (s+1) (a :: b :: rest)) → P s ws
theorem Run.done {α : Type} {inv : α->α} {meet join : α->α->α} {y : α}  : Run inv meet join y 0 [y]:=by
  intro P done perm one two
  exact @done  
theorem Run.perm {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs) : Run inv meet join y s zs:=by
  intro P done perm one two
  exact @perm s xs zs p (tail P done perm one two)
theorem Run.one {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) : Run inv meet join y (s+1) (a :: rest):=by
  intro P done perm one two
  exact @one s a rest neg save (tail P done perm one two)
theorem Run.two {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))) : Run inv meet join y (s+1) (a :: b :: rest):=by
  intro P done perm one two
  exact @two s a b rest conj ka kb (tail P done perm one two)
theorem Run.elimInd {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {P : ℕ → List α → Prop}
    (done : P 0 [y])
    (perm : ∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs) (ih : P s xs),P s zs)
    (one : ∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) (ih : P s ((if neg then inv a else a) :: kept save a rest)),P (s+1) (a :: rest))
    (two : ∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))) (ih : P s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))),P (s+1) (a :: b :: rest)) {s : Nat} {ws : List α} (h : Run inv meet join y s ws) : P s ws:=by
  apply And.right (a:=Run inv meet join y s ws)
  apply h (fun s ws=>Run inv meet join y s ws ∧ P s ws)
  · exact ⟨@Run.done α inv meet join y  ,@done  ⟩
  · intro s xs zs p prev
    exact ⟨@Run.perm α inv meet join y s xs zs p prev.1,@perm s xs zs p prev.1 prev.2⟩
  · intro s a rest neg save prev
    exact ⟨@Run.one α inv meet join y s a rest neg save prev.1,@one s a rest neg save prev.1 prev.2⟩
  · intro s a b rest conj ka kb prev
    exact ⟨@Run.two α inv meet join y s a b rest conj ka kb prev.1,@two s a b rest conj ka kb prev.1 prev.2⟩
theorem Run.elimCases {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {P : ℕ → List α → Prop}
    (done : P 0 [y])
    (perm : ∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs),P s zs)
    (one : ∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)),P (s+1) (a :: rest))
    (two : ∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))),P (s+1) (a :: b :: rest)) {s : Nat} {ws : List α} (h : Run inv meet join y s ws) : P s ws:=by
  apply Run.elimInd (P:=P) (h:=h)
  · exact @done  
  · intro s xs zs p prev ih
    exact @perm s xs zs p prev
  · intro s a rest neg save prev ih
    exact @one s a rest neg save prev
  · intro s a b rest conj ka kb prev ih
    exact @two s a b rest conj ka kb prev
theorem Run.byInd {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {P : ∀ (s : Nat) (ws : List α),Run inv meet join y s ws → Prop}
  (done : P 0 [y] (@Run.done α inv meet join y ))
  (perm : ∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs) (ih : P s xs tail),P s zs (@Run.perm α inv meet join y s xs zs p tail))
  (one : ∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) (ih : P s ((if neg then inv a else a) :: kept save a rest) tail),P (s+1) (a :: rest) (@Run.one α inv meet join y s a rest neg save tail))
  (two : ∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))) (ih : P s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) tail),P (s+1) (a :: b :: rest) (@Run.two α inv meet join y s a b rest conj ka kb tail)) {s : Nat} {ws : List α} (h : Run inv meet join y s ws) : P s ws h:=by
  have aux : ∀ hx : Run inv meet join y s ws,P s ws hx:=by
    apply Run.elimInd (P:=fun s ws=>∀ hx : Run inv meet join y s ws,P s ws hx) (h:=h)
    · intro  hx
      exact @done 
    · intro s xs zs p prev ih hx
      exact @perm s xs zs p prev (ih prev)
    · intro s a rest neg save prev ih hx
      exact @one s a rest neg save prev (ih prev)
    · intro s a b rest conj ka kb prev ih hx
      exact @two s a b rest conj ka kb prev (ih prev)
  exact aux h
theorem Run.byCases {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {P : ∀ (s : Nat) (ws : List α),Run inv meet join y s ws → Prop}
  (done : P 0 [y] (@Run.done α inv meet join y ))
  (perm : ∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs),P s zs (@Run.perm α inv meet join y s xs zs p tail))
  (one : ∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)),P (s+1) (a :: rest) (@Run.one α inv meet join y s a rest neg save tail))
  (two : ∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))),P (s+1) (a :: b :: rest) (@Run.two α inv meet join y s a b rest conj ka kb tail)) {s : Nat} {ws : List α} (h : Run inv meet join y s ws) : P s ws h:=by
  have aux : ∀ hx : Run inv meet join y s ws,P s ws hx:=by
    apply Run.elimCases (P:=fun s ws=>∀ hx : Run inv meet join y s ws,P s ws hx) (h:=h)
    · intro  hx
      exact @done 
    · intro s xs zs p prev hx
      exact @perm s xs zs p prev
    · intro s a rest neg save prev hx
      exact @one s a rest neg save prev
    · intro s a b rest conj ka kb prev hx
      exact @two s a b rest conj ka kb prev
  exact aux h
theorem Fd {α β : Type} (e : α->β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e=kept b (e x) (xs.map e):= by cases b <;> simp [kept]
lemma Run.map {α β : Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
    {inv' : β->β} {meet' join' : β->β->β}
    (hi : ∀ a,e (inv a)=inv' (e a)) (hm : ∀ a b,e (meet a b)=meet' (e a) (e b))
    (hj : ∀ a b,e (join a b)=join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e):= by
  induction h using Run.byInd with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e):= by
      cases neg <;> simp [Fd,hi]
    rw [e1] at ih;exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)):= by
      cases conj <;> simp [Fd,hm,hj]
    rw [e1] at ih;exact Run.two conj ka kb ih
theorem DT {α inv meet join y s xs} (h : @Run α inv meet join y s xs) : xs.length ≤ s+1:= by
  induction h using Run.byInd with
  | done=>simp
  | perm hp _ ih=>rwa [←hp.length_eq]
  | one _ save _ ih=>cases save <;> simp_all [kept] <;> omega
  | two _ ka kb _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
abbrev NatRun (m : Nat):=Run (·^^^m) (·&&&·) (·|||·)
lemma q29 {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i=m.testBit j) (hw : ∀ w ∈ xs,w.testBit i=w.testBit j) :
    y.testBit i=y.testBit j:= by
  induction h using Run.byInd with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | one neg save _ ih =>
    apply ih;have ha:=hw _ List.mem_cons_self;intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr;exact ha;exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr;simp [ha,hm];exact hw _ (by simp [hr]))
  | two conj ka kb _ ih =>
    apply ih;have ha:=hw _ List.mem_cons_self;have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons];tauto)
def lo (k : Nat):=2^k - 1
def mask (k : Nat):=lo (k+k)
def goal (k : Nat):=lo k<<<k
def se : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def q7 : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def qe : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000
lemma yx : se=lo 232:= by decide +kernel
lemma vb : q7=mask 232:= by decide +kernel
lemma vc : qe=goal 232:= by decide +kernel
lemma u4 (k i : Nat) : (lo k).testBit i=decide (i<k):= by
  simp [lo,Nat.testBit_two_pow_sub_one]
lemma zn (k i : Nat) : (mask k).testBit i=decide (i<k+k):= by
  simp [mask,u4]
lemma xo (k i : Nat) :
    (goal k).testBit i=(decide (k ≤ i)&&decide (i - k<k)):= by
  simp [goal,Nat.testBit_shiftLeft,u4]
def vd (w : Nat) : Nat:=w^^^(w>>>232)
def s9 : List Nat->Nat | []=>0 | a :: t=>vd a|||s9 t
lemma q11 (i : Nat) (ws : List Nat) : (s9 ws).testBit i=true ↔
    ∃ a ∈ ws,a.testBit i ≠ a.testBit (232+i):= by
  induction ws with
  | nil=>simp [s9]
  | cons a t ih =>
    simp only [s9,Nat.testBit_or,Bool.or_eq_true,ih,vd,Nat.testBit_xor,Nat.testBit_shiftRight,List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (232+i) <;> simp_all
lemma vl {s ws} (h : NatRun q7 qe s ws) :
    (s9 ws&&&se)=se:= by
  rw [vb,vc] at h;rw [yx]
  apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hm : (mask 232).testBit i=(mask 232).testBit (232+i):= by
      simp [zn,show i<464 by omega,show 232+i<464 by omega]
    have hy : (goal 232).testBit i ≠ (goal 232).testBit (232+i):= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (s9 ws).testBit i=true:= by
      apply (q11 i ws).2;by_contra! hh;exact hy (q29 h i (232+i) hm hh)
    simp [hc]
  · simp [u4,hi]
lemma q34 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1) (i j : Nat)
    (hw : ∀ a ∈ ws,a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j:= by
  induction h using Run.byInd with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (hp.length_eq.trans hl) (fun a ha=>hw a (hp.mem_iff.1 ha))
  | one _ save h _=>have hh:=DT h;cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=DT h;cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept];omega)
    have ha:=hw _ List.mem_cons_self;have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had;simp only [kept,Bool.false_eq_true,ite_false,List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true,Bool.false_eq_true,ite_false,Nat.testBit_or,Nat.testBit_and] <;> grind
    · exact hw _ (by simp [ht])
def sq (w : Nat) : Nat:=(w>>>232)&&&(w^^^se)
def rd : List Nat->Nat | []=>0 | a :: t=>sq a|||rd t
lemma zu (i : Nat) (hi : i<232) (ws : List Nat) : (rd ws).testBit i=true ↔
    ∃ a ∈ ws,a.testBit i=false/\a.testBit (232+i)=true:= by
  induction ws with
  | nil=>simp [rd]
  | cons a t ih=>simp [rd,sq,yx,u4,hi,ih,and_comm]
lemma rl {s ws} (h : NatRun q7 qe s ws) (hl : ws.length=s+1) :
    (rd ws&&&se)=se:= by
  rw [vb,vc] at h;rw [yx]
  apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hy : ¬ (goal 232).testBit (232+i) ≤ (goal 232).testBit i:= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (rd ws).testBit i=true:= by
      apply (zu i hi ws).2;by_contra! hh;apply hy
      apply q34 h hl;intro a ha;specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (232+i) <;> simp_all
    simp [hc]
  · simp [u4,hi]
lemma y1 {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):= by cases b <;> simpa [kept] using p
def vy (s : Nat) (ws : List Nat) (f : Bool->List Nat->Bool) : Bool :=
  let len:=ws.length
  let slack:=s+2 - len
  let t0:=decide (len=s+2)
  let t1:=decide (len=s+1)
  let t2:=decide (len=s)
  ws.any fun a =>
    let ra:=ws.erase a
    let da:=vd a
    let dau:=sq a
    (slack ≥ 1 &&
      (let cra:=if t1&&slack==1 then 0 else s9 ra
       let crau:=if t1||t2 then rd ra else 0
       [false,true].any fun neg =>
        let w:=if neg then a^^^q7 else a
        (((if t1 then sq w|||crau else vd w|||cra)&&&se==se)&&f t1 (w :: ra)) ||
        (slack ≥ 2 &&
          ((if t2 then sq w|||(dau|||crau) else vd w|||(da|||cra))&&&se==se) &&
          f t2 (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b &&
      (let r:=ra.erase b
       let db:=vd b
       let dbu:=sq b
       let cr:=if t0 then 0 else s9 r
       let cru:=if t0||t1||t2 then rd r else 0
       [false,true].any fun conj =>
        let w:=if conj then a&&&b else a|||b
        let dw:=if t0 then 0 else vd w
        let dwu:=if t0||t1||t2 then sq w else 0
        (((if t0 then dwu|||cru else dw|||cr)&&&se==se)&&f t0 (w :: r)) ||
        (slack ≥ 1 &&
          ((((if t1 then dwu|||(dau|||cru) else dw|||(da|||cr))&&&se==se)&&f t1 (w :: a :: r)) ||
           (((if t1 then dwu|||(dbu|||cru) else dw|||(db|||cr))&&&se==se)&&f t1 (w :: b :: r)))) ||
        (slack ≥ 2 &&
          ((if t2 then dwu|||(dau|||(dbu|||cru)) else dw|||(da|||(db|||cr)))&&&se==se) &&
          f t2 (w :: a :: b :: r)))
lemma q08 {a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun q7 qe s ((if neg then a^^^q7 else a) :: kept save a rest))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a):=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hh:=DT h;have hl:=p.length_eq;simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length:= by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩;rw [Bool.or_eq_true];left
  rw [Bool.and_eq_true];refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have hrun:=Run.perm ((y1 pr save a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases save with
  | false =>
    simp only [kept,Bool.false_eq_true,ite_false] at ht hrun hcov
    have hlen : ((if neg then a^^^q7 else a) :: ws.erase a).length=ws.length:= by
      simp [List.length_erase_of_mem ha];omega
    rw [hlen] at ht
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h1,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [hcov,ht]
  | true =>
    simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2-ws.length:= by omega
    have hlen : ((if neg then a^^^q7 else a) :: a :: ws.erase a).length=ws.length+1:= by
      simp [List.length_erase_of_mem ha];omega
    have hlen_eq : decide (((if neg then a^^^q7 else a) :: a :: ws.erase a).length=s+1)=decide (ws.length=s):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hlen_eq] at ht
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · have h1 : ws.length ≠ s+1:= by omega
      simp only [h1,h2,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma u9 {a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun q7 qe s ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=DT h;have hl:=p.length_eq;simp only [List.length_cons] at hl hh
  have hlenr : ((ws.erase a).erase b).length=ws.length - 2:= by
    have:=pr.length_eq;omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩;rw [Bool.or_eq_true];right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩;rw [Bool.and_eq_true];refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have hrun:=Run.perm ((y1 (y1 pr kb b) ka a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases ka <;> cases kb
  · simp only [kept,Bool.false_eq_true,ite_false] at ht hh hrun hcov
    have hlen : ((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=ws.length - 1:= by
      simp [hlenr];omega
    have hle : decide (((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s+2):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    by_cases h0 : ws.length=s+2
    · have hcu:=rl hrun (by omega)
      simp only [h0,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,decide_false,s9] at ht hcov ⊢
      simp [hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: b :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr];omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr];omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=ws.length+1:= by
      simp [hlenr];omega
    have hle : decide (((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h2,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma q07 {a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun q7 qe s ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  rcases le_total a b with hab | hba
  · exact u9 hab p h f hf
  · apply u9 (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a&&&b else a|||b)=(if conj then b&&&a else b|||a):= by
      cases conj <;> simp [Nat.and_comm,Nat.or_comm]
    rw [he] at h;apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept];exact List.Perm.swap _ _ _
lemma q1f {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t=0->ws=[y]:= by
  induction h using Run.byInd with
  | done=>simp
  | perm p _ ih=>intro ht;rw [ih ht] at p;exact List.perm_singleton.1 p.symm
  | one=>simp
  | two=>simp
lemma y0 {t ws} (h : NatRun q7 qe t ws) :
    ∀ s,t=s+1->∀ zs,ws.Perm zs->∀ f : Bool->List Nat->Bool,
      (∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true)->vy s zs f=true:= by
  induction h using Run.byInd with
  | done=>simp
  | perm p _ ih=>intro s he zs q;exact ih s he zs (p.trans q)
  | one _ _ h _=>intro s he zs p f hf;cases he;exact q08 p h f hf
  | two _ _ _ h _=>intro s he zs p f hf;cases he;exact q07 p h f hf
def xs517 : List ℕ:=[0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517,0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827,0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248,0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0,0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418,0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800,0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688]
lemma yn : ∀ zs ∈ xs517.sublists,zs ≠ xs517 →
    (s9 zs&&&se) ≠ se:= by decide +kernel
def r2 (tag d w : Nat) : Nat:=((w&&&tag)<<<d)|||((w>>>d)&&&tag)
lemma q3l (tag d i w : Nat) (h : (tag&&&(tag<<<d))=0) :
    (r2 tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag<<<d).testBit i then w.testBit (i-d) else false):= by
  have ht:=congrArg (fun v : Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [r2,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at*<;> grind
lemma yw (tag d : Nat) (h : (tag&&&(tag<<<d))=0) (a b : Nat) :
    r2 tag d (a&&&b)=(r2 tag d a&&&r2 tag d b) ∧
    r2 tag d (a|||b)=(r2 tag d a|||r2 tag d b) ∧
    r2 tag d (a^^^b)=(r2 tag d a^^^r2 tag d b):= by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,q3l tag d i _ h] <;>
    split_ifs <;> simp
lemma q0b {s ws} (h : NatRun q7 qe s ws) (tag d : Nat)
    (hz : (tag&&&(tag<<<d))=0) (hm : r2 tag d q7=q7)
    (hy : r2 tag d qe=qe) :
    NatRun q7 qe s (ws.map (r2 tag d)):= by
  rw [← hy]
  exact Run.map _ (fun a=>(yw tag d hz a q7).2.2.trans (by rw [hm]))
    (fun a b=>(yw tag d hz a b).1) (fun a b=>(yw tag d hz a b).2.1) h
def q3e : Nat:=0x3ffffffffffffff000000000000003ffffffffffffff000000000000003ffffffffffffff000000000000003ffffffffffffff
def q3d : Nat:=0xfffffffffffffffffffffffffffff00000000000000000000000000000fffffffffffffffffffffffffffff
def q38 (xs : List Nat):=xs.map (r2 q3e 58)
def q37 (xs : List Nat):=xs.map (r2 q3d 116)
lemma q3j {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (q38 ws) :=
  q0b h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
lemma q3i {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (q37 ws) :=
  q0b h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
def vf (a b c d e f : Bool) : Nat :=
  let x:=b.toNat+c.toNat;let y:=(!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)
lemma q0q : ∀ a b c d e f g h i j l m : Bool,
    vf (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ vf a b c d e f+vf g h i j l m:= by decide +kernel
lemma q1g : ∀ a b c d e f g h i j l m : Bool,
    vf (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ vf a b c d e f+vf g h i j l m:= by decide +kernel
lemma q05 {l r : List Nat} (h : l.Perm r) : l.sum=r.sum:= by
  induction h with
  | nil=>rfl
  | cons _ _ ih=>simp [ih]
  | swap=>simp;omega
  | trans _ _ ih1 ih2=>exact ih1.trans ih2
lemma q01 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (v : Nat->Nat) (hand : ∀ a b,v (a&&&b) ≤ v a+v b)
    (hor : ∀ a b,v (a|||b) ≤ v a+v b) : v y ≤ (ws.map v).sum:= by
  induction h using Run.byInd with
  | done=>simp
  | perm p _ ih=>rw [← q05 (p.map v)];exact ih (p.length_eq.trans hl)
  | one _ save h _=>have hh:=DT h;cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=DT h;cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept];omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc,← hand];exact ih' | grw [← Nat.add_assoc,← hor];exact ih'
def yz (a b c d e f v : Nat) : Nat :=
  if v.testBit a then
    if v.testBit d then (!v.testBit e).toNat+(!v.testBit f).toNat
    else
      let x:=(v.testBit b).toNat+(v.testBit c).toNat
      let y:=(!v.testBit e).toNat+(!v.testBit f).toNat
      max x (max y (x+y - 1))
  else
    if v.testBit d then 0
    else (v.testBit b).toNat+(v.testBit c).toNat
lemma q0e (a b c d e f v : Nat) :
    yz a b c d e f v=vf (v.testBit a) (v.testBit b) (v.testBit c)
      (v.testBit d) (v.testBit e) (v.testBit f):= by
  unfold yz vf
  cases v.testBit a <;> cases v.testBit d <;> rfl
lemma q0f {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (a b c d e f : Nat) : yz a b c d e f y ≤ (ws.map (yz a b c d e f)).sum:= by
  apply q01 h hl
  · intro v w;simp only [q0e,Nat.testBit_and];exact q0q _ _ _ _ _ _ _ _ _ _ _ _
  · intro v w;simp only [q0e,Nat.testBit_or];exact q1g _ _ _ _ _ _ _ _ _ _ _ _
def q26 : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(462,447,452,215,221,207),(453,441,440,220,193,181),(445,410,360,199,216,201),(460,410,440,178,229,217),(459,461,454,220,89,205),(370,438,302,215,216,211),(457,410,418,199,207,201),(403,428,450,207,201,220),(457,429,450,218,207,201),(456,452,454,219,201,199)]
lemma zy : q26.all (fun t =>
    yz t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 qe==3)=true:= by decide +kernel
def yh (a b c d e f : Nat) : Nat->List Nat->Bool
  | acc,[]=>decide (acc<3)
  | acc,w :: t =>
    let acc':=acc+yz a b c d e f w
    if acc' ≥ 3 then false else yh a b c d e f acc' t
lemma zo (a b c d e f : Nat) (ws : List Nat) (acc : Nat)
    (h : yh a b c d e f acc ws=true) : acc+(ws.map (yz a b c d e f)).sum<3:= by
  induction ws generalizing acc with
  | nil=>simpa [yh] using h
  | cons w t ih =>
    simp only [yh] at h
    split at h
    · contradiction
    · have ih':=ih _ h
      simp only [List.map_cons,List.sum_cons]
      omega
def q0x (ws : List Nat) : Bool :=
  q26.any (fun t=>yh t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 0 ws)
lemma q1n {s ws} (h : NatRun q7 qe s ws) (hl : ws.length=s+1) :
    q0x ws=false:= by
  rw [Bool.eq_false_iff];intro hk
  obtain ⟨t,ht,hlt⟩:=List.any_eq_true.mp hk
  have hg:=beq_iff_eq.mp (List.all_eq_true.mp zy t ht)
  have hb:=q0f h hl t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2
  have hs:=zo t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 ws 0 hlt
  rw [hg] at hb;omega
def span (f : Nat->Bool) : Nat->Nat->Bool
  | 0,_=>true
  | n+1,i=>f i&&span f n (i+1)
theorem span_ok {f n o} (h : span f n o=true) : ∀ i,o ≤ i->i<o+n->f i=true:= by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h;intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem span_join {f a o b} (ha : span f a o=true) (hb : span f b (o+a)=true) :
    span f (a+b) o=true:= by
  induction a generalizing o with
  | zero=>simpa using hb
  | succ a ih =>
    simp only [span,Bool.and_eq_true] at ha;rw [Nat.succ_add,span,Bool.and_eq_true]
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩
lemma q10 {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r):= by
  induction t,hle using Nat.le_induction with
  | base=>exact h
  | succ _ _ ih=>exact Run.one false false ih
def q36 : Nat->Nat
  | 0=>0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517
  | 1=>0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827
  | 2=>0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248
  | 3=>0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0
  | 4=>0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418
  | 5=>0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800
  | 6=>0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688
  | 7=>0
  | 8=>q7
  | 9=>0x6f27d5b39727ae1b49f56d29a9e3808d7be5d22ba78c2bdef96c46fbe3004202ba9605a60011c4cfa98141800adbd4521ba18002a2b30446eae0
  | _=>0xff28d8b3df67b7254ff5613bb923c9858b85d6afa3524efe7b0f67d3e780c202bad625b22001c441b981418808fbd4560ba1020282330546c2e0
def q24 : Nat->Nat
  | 0=>0x2e0060280e268192c8192a0162b81918806200192a019000081000503005188191880917801268a50013001001001280180a1481912811230110080214811218110300219811200110280616805020051e015000ec018011c8151481a16819178151a8150300a1981503006188150000017809030121680902812000ac01802148150000c10009118191281501006118150200a0b80910011030160f0150200602811098010d001028050a8050b811030150a8090280d098090300d08805028090780503011068050200d0580502009
  | 1=>0xb80e01806419520b952099521f152549510004c1d812531e91f00e520163d00d33951231511d8160027c00801000044e01601805268052a005380a51881610012421b2498fa3601206816188121f0c6068c62b0121e15129012380c50022801002440c5001482481242812030010b8120011829016308161f016078163e81a01809338c5001e802002188053081a1f01a178050581a0e81a0881a0d01a38019001bc0100536819001b0028011e0193481920002338190003432819320060280a3101900184020012f819168062e819
  | 2=>0x378a62080a1f00a1b80a0b80a0780a0d00a0d80a0c00a7ca290e80a0800a0700a7a80900074368096a132338097800914806230090b8a60d0a6260a61f0a6748a500068368a5730a50005c001703d0a514801708a5000f8002e8440a50030414809378c637812378161e0056b8051780a3781a1180519809200093200514805378013b00e2b00e2980e590ad1f80e530ad612e93d80e581b21a00e3c80e1100e613052600e0300e5d9b25eae95e9293600e5dae90d00e0200e0c00e580ad0900e0d80e0800e0600e591292900e582bd
  | _=>0x5e9327780e001f4000185200a9e8fa000540001412802000102b0023b002290026a802378021d80a0b80214802110029fc691f0029ec6906802090020c0020800207002060022a00652006591be6a80e6900e3780e6800e1d806002701a806260064f80a1780606806100060a806360060b80692006030090880642806078060e806730054f81a450053d0058d005028021680a1880a778124180a0680a148126e812260121000a778163600a14816360a6260163d8a63b00a2b00a2900a2880a0980a290a61480a
def zf : Nat->Nat->Nat
  | 0,_=>0
  | fuel+1,i =>
    if i<11 then q36 i
    else
      let k:=i - 11
      let c:=(q24 (k/83)>>>(20*(k % 83)))&&&1048575
      let op:=c&&&3
      let a:=(c>>>2)&&&511
      if op=0 then zf fuel a^^^q7
      else let b:=c>>>11;if op=1 then zf fuel a&&&zf fuel b else zf fuel a|||zf fuel b
def q2a : Nat->Nat
  | 0=>0x181dc00005ff70000179dc00005ef70000175dc00005cf70000171dc00005bf7000016ddc00005af70000169dc00005977000022fec000085fb004b86de40000857b0000211ec000081fb0050205e80000817b0000203ec0144807a0000201ec00007d7b00001fbec00007e7b00001f7ec00007cfb00001f1ec008b977c3d91c83f0014493fc0000295f80000a4fe000028ff80000a37e0000289f80000a07e0000285f80000a0fe000027ff800009efe0000279f800009dfe0000275f800009cfe0000001fc0000907d00001efec00007afb00001e9ec000079fb00001e5ec0146787a00001e1ec00006efe00001b5f400006cfd000015fec0000577b000015bec0000567b0030cabcc01332af3000a8abcc00b32af30029cabcc00b12af3002f8abcc00bc2af300518abe801442afa00500abe800002afb0000157ec0000527b0000147ec00c34ff5004cd3fd4002a4ff5002cd3fd400a74ff5002c53fd400be4ff5002f13fd454554ff10000139f400004d770000125f8000048fe0030c65d801331976000a865d800b319760029c65d800b119760031865d800be1976002f065d80110197a0042065e80102197a0040065e800fa197a004b865f00128197c0049c65f00000197e003c065e8545519720015465e8549f19740027c65f0aa9f1978000011fec000046fe0000115f800003efe0011ceff40000393f00000defc0000363f00000d6fc000034bf00000cefc0000323f00000c2fc00002fbf00000b8fc00002dbf00154b6ec00002cbf000c8b2f8014d2b9f00194ae7c005d2b9f0020cae7c014b2baf00240aebc002a2bb70033caedc010a2bbb0049caef4014a2bbe00000aefc00552bbb0027caef400322bbe000009fdc013e1fee002947f9c00001f5f000a8775c00001ddf328d8306c00be0c5700440316c011888cb00435b92c00c84bc70053d2d3801375355004f94d58012b515525cf8498801538c630030db98c013754e500001519c01509bf10051657c401509f720054e8dc8004785f9002f8ae5c01102b9b
  | 1=>0x45fc014b086f000c021bc002a08770000021fc0055087b0027c21f40032087e0000041fc014b0f6f000b83dbc002a0f77003e83dec00000f7f001543dec00320f7e0054436fc014d0ddf00104377c014b0def000a837dc00bc0df70010437f400000dff0015437ec009f0dfd000c837f800000eff0000039fc00000d7f0000033fc00000bff000002bfc000009ff0000023fc000007ff000001bfc002a04770000011fc0055047b000c811fa9b4b154700536973c014d6e4f0052db73c00dc6dcfa6d2cab2e9b4b194e005351d3c014d43cf005350b3c005d42cf0030e1b5c014d155700434555c01336dd7000a9b75e9a2a2ad3000b1455c00b05157000a9455e9a2a4fd5002c13d5c002a4f57000a9295e9a2a19560052d073c008e41cf000a9075c007b40cf0052d033c002a40d70029d035c014b156700450559c01131567004cdb99c002a6e67a58a8ab8c00b054e7000a9539c002a4ae7a58a86598002a4767002cd1d9c002a4467000a90f9c002a42e7002c50b9c00c345f3000b28bcc014558730030c49cc00c31b730030e5dd4004b95f50012e7dd80000aa7700002a7dc000061f70000017dc00009b77000026bdc00009a770051a67d8000099f70000265dc000087770000219dc000083770000209dc0153787300001dfdc0000777700001dbdc000076770051455cc011615730044055cc010915730041c55cc010215730040055cc00fa1573004c455d4012e1575004ac55d4012815750049c55d4013e15760052055d8014615760051055d8014015760000055dc00f21573003c055cc000075f700001d3dc0000747700001cbdc000071f700001c1dc00c3387300001a1dc000067f7000019ddc010959f30052167d8000059f7000019bdc012b5df50000199dc010253f30007d4fd4014053f6000014fdc000065f70000195dc000064f7004acbbd4013e2ef60000191dc00000577000018fdc010058f30049d63d4014458f60000163dc00006377000018bdc000062770000183dc01105f73004a17dd400005f77
  | 2=>0x1a5fc000068ff000009dfc00002d7f000a8abcc002a2af700024abec00472afb00000abec01382afb00098abec00412afb000d0abec00022afb00280abec00362afb00000abfc002a2afb001c0abec005a2afb00154abec000050ff000a93fd4002a4ff70000137fc00554dfb0000133fc00004c7f000a85ddc0047177f000005dfc0055177b0000127fc002a1977000a865d80009197e0011c65f8014b197e0011065f8008b197e0046c65f80000197f0009865f80058197e0010465f80034197e0000865f80000197e0028065f80119197e0019465f80036197e0000c65f8002a197e0013465f80070197e0015465ec0055197a0015465f8009f197e0027c65f00099197e000b865f80093197e000c865f8002a18770011c61fc0000187f0015461ec009f187d000c861f80000467f000010bfc0000427f000a843dc000010ff0015443ec003210fe0000107fc0000417f0000103fc0000407f00000fffc00003e7f00000f5fc00323d7e00000f3fc00003c7f00000effc00003b7f00000ebfc00003a7f00000e7fc014d03df0052c0fbc002a03f7000000ffc005503fb0027c0ff4003203fe00000aefc00412bbf00000affc00002b7f00154adec00002a7f00000a5fc0032297e00000a3fc003228fe00000a1fc0000267f000a895dc0000257f0000093fc0000247f000a88ddc0000237f000008bfc000021ff0000085fc0000207f005447efc00781fbf005347f7c00811fdf001ec7fbc014b1fef0007c7fbc002a1ff70029c7fdc01021ffb0007c7ff401401ffe000007ffc00551ffb0027c7ff400321ffe0000073fc00001c7f000006ffc00001aff0000067fc003219fe00534317c00650c5f00174317c00210c5f000a831dc00b10c770040031ec01440c7e0000031fc00550c7b000c831f800530c3f0000063fc000017ff000005bfc002a15f70000057fc000014ff0000051fc000013ff000004bfc0151093f00534257c0065095f0052c25bc002a09770019425ec0000097f0015425ec009f097d000c825f8000011ff
  | _=>0x7f0000055dc000023ff0000001fc0000137f0000083fc00001a7f0000005fc0000507f000006dfc000001ff0000055fc0000387f00000abec00002aff000005dfc0000197f0000065f80000187f0000043fc000003ff000007ffc00000c7f0000025fc0000087f000003dfc00000dff00536973c014d15570052c559c002c25f70000187dc004b58770000267dc00091577000b055dc004b15770054455dc007b15770053455dc004715770052c55dc004415770022c55dc011b15770050c55dc000115770000055dc00b01577003c455dc002615770007c55dc00411577000d055dc000215770028055dc002415770045455dc006515770043c55dc00361577000e855dc010515770000c55dc002a1577000a9c9dc002a6f770030c9bdc002a26f7004cce1dc002a3877000a9a5dc00b06177000a985dc000059f7002c177dc002a5df7000014fdc002c2ef7002c0bbdc002a2ef700308bbdc000058f7000017ddc00005e770012c6dec00261b7b001946dec0000817b0000201ec00007d7b0011c89f8004745fe000028df800448dfe0000289f80000a07e0000013fc0000a97f0000155fc0000a77f00000d5fc0000347f0000299fc000023ff0000287fc0000007f00000bdfc00009c7f0000261fc0000337f000025ffc000078ff000004dfc0000977f000025bfc0000307f0000259fc00002c7f0000255fc007b20ff0000083fc000094ff0000251fc00001a7f000024ffc0000937f0000249fc000091ff0000245fc000090ff0000005fc00008fff000023dfc00008eff0000239fc0047507e0000141fc00008d7f000007bfc00006c7f0000233fc00008aff0000225fc000087ff000006dfc00001d7f000020bfc0000817f0000201fc00007fff00001fdfc00007d7f0000007fc0047787b00001e1ec0000787f0000055fc0000737f00001c9fc000070ff00001bffc00006f7f00001b7fc00006bff00001adfc00006aff00001a9fc000069ff00098e1ec0065387b00098e1f40146387e00000e1fc004d387b
def xl (code k : Nat) (acc : List Nat) : List Nat :=
  if (code>>>k)&&&1==1 then q36 k :: acc else acc
def z0 (e : Nat) (acc : List Nat) : List Nat :=
  if e==0 then acc else zf 4 (e - 1) :: acc
def q3k (i : Nat) : List Nat :=
  if i<6 then []
  else
    let j:=i - 6
    let code:=(q2a (j/176)>>>(34*(j % 176)))&&&0x3ffffffff
    let acc:=z0 ((code>>>25)&&&511) (z0 ((code>>>16)&&&511) (z0 ((code>>>7)&&&511) []))
    xl code 0 (xl code 1 (xl code 2 (xl code 3 (xl code 4 (xl code 5 (xl code 6 acc))))))
def q25 : Nat->Nat
  | 0=>1 | 1=>1 | 2=>1 | 3=>1 | 4=>1 | 5=>1
  | 6=>19 | 7=>292 | 8=>365 | 9=>26 | 10=>1 | _=>0
def q3t : Nat->Nat
  | 0=>0 | 1=>1 | 2=>2 | 3=>3 | 4=>4 | 5=>5
  | 6=>6 | 7=>25 | 8=>317 | 9=>682 | 10=>708 | _=>0
def vj (s i : Nat) : List Nat:=q3k (q3t s+i)
def sg (salt : Nat) : List Nat->Nat
  | []=>0
  | w :: t=>let x:=(w % 1048573+317+salt) % 1048573;(x*x*x) % 1048573+sg salt t
def q18 : Nat->Nat
  | 6=>0x2d510a29c920dd8c26046a45edcab10e217235801e802cc829b
  | 7=>0xba020271000f0d789715b90b1b40d05ca2d4a2b20600798bac5c7e51085e9a4554cdd8e3980600005246e24e7704c2f50005cd6d23c0e8ee0943e87206f17bbbe2205918c9ad6d8c4dd10000ca1d4a0086754ac52a4592ac768220bc3fc1f922c761b4a30630003be5e00833f0d0d88b41f41811e4783cf36e2dc004002e0fbd5d8007d4b20a617c1680000029e1429da3348d12e9adfc1e03a65ca0c0b8279042040b6832081c4a94630e90120006c8e7618c585e8478000000e0b5e3abee6724d0dc28a4f63f1783c6676dd56abce0000e08019e42acc8c20d74cc7606228d6fa4e030800778001c584c7764b0a4ac49105d1a648c4486522847d50cc6e20a0c4d4e35f0901710e0cf40515302009b2095a0370e248f4c04163a3ab0e2840000aa000b85763445f112a350607800000029000006d184643c45988fb302401912822c64a9d0e0251912f598a0f42b8671a88181a41b0d04218a2434643e58a8f31b8394262fda061372b12394e130690d75503ca3d8870b697b212c6a301b50092181d0146e85e85835b2103bcf84497750e5ff1886ee6a8460501e2ebd824067cd205840001d91dcb18003c8b01d480c8280d067c358d0e1c820064b038188b0c722360a82b46ecd1d3fb780008508e3d453439e0ab8c320211da96c49235238a77476931a93a75666c63f3553f2880e4054184a210f404408b042709674c3e1af888398a483c3b7302460aa0ba8f06319693b13a3a09d00888a0a912af60582b10c1d65990a588472078ca40e9987a0801342287b47757e41d838d2941b3c228ff1c54020aac9092059006afd1a425090c482c4850b8cf9379f87621756ebdc27d118652a69049007e8914bf0f0b012a684ab49f802050ea22623a
  | 8=>0x138c54934604ac03d9da53893a963200001f918326961401461089814d14c94c238451f64d35929b4ffaf00002f2588000001a6d1c3b8e552048160000c7da4508a12ea26db16296bd4174c85145c2c45633c2b20c82402f83540b8c291ccda0a2c69e6c9eca21c2a0b32380b2a0ac60a180095d0bdd04b246a3d513ace3aa972874da6d12706ca58000a1009a100ee43944337528b29fa491af5485ec98a38a278ca0421a2b04903aa0829c0915225ecb49060815d8002cecf16671685a93052a10eaaae5249586bf0f0aeca69a030a2190e0e420b1707a822828a486a0ae27e4f50b56214a3320d56cc656d4d911c53d81c0725307c8d2be5faaad16f4d8a258091347291cdca1ed5dec5685f09208d2be2b0f502b18c1101fd8bd580c6170a10af63b6318d13b231385cca428188a62b26c28e949168927081b0890e0aba9e0040269400f2c59014d6670b590016363c59c58138de07c8391f105e2808a0c869d46aed6a82117f42080ed12ba0f4b08151da27cb0f180e20dc9fc0023e5a74085eeb944fafa110bfa19830b40f68686160013b2a22082398f4d442f04a620c4000002211d407031a26c888514480034f1ec65800402a400009c1dd13a932c83919f0c00c2376858002822bc3b9462330991510e6a11296a7530cb8219c518464554899170005ac7f05a12d2600002d1fe000000ac43043324a781ff1c1670760b312c69b2299d1e869c551c62a085d028515a82d93ea730a41d9582a81a063800064be426b5cda8b35174b0a59ccc19eb0245b5245d516d8cf57e4544e80150494c2cf8955b0486364e79f2176764c5478cc4ba000900101ed355380392a1d0c118ee1e423a000d31ba36028c1d118b2471a0c4a48007988d1162e80315e2742680a1598944bc9701e1a83102201b47e05816d544fc03083d4a2082920003001556e38c3f44a4407c0b76562d488805032b9427aaa016464000c1819282a82a618a37e140351d5b805d33781b1956d8ad29e01d930119822ac0560012e9fb018131e24d99695c1669c70006f92a2f4950b72cc325400c21231616587088b0ae90ab9002000855500f60005c2a99970ac8911b97e567000260a0514712600cc4367782c01f106669099ad2f73c6dc179d7f360515401b83e8990e65933865e276a50ac4592ae0cc5c09959456c2e2ea5d640f052e4008538372c1ca41de619665ae3b03b725475bc0369359ab3324d26b08f0005715f1e84df000cf83393c7b87923c256875510243753e0a908db9dac89d023a20b44cc289be83c53bec083f3780ccda9df0013f63a4a274ca400001181acf03821d7b6c547d43c
  | 9=>0xa197f9864cac828bcc96272d000622a0801403cb48d000b1ebd4114d11504f80408a7451700016502d6981bb801d1148e240e1f1b0344d9ea8d30f4e10
  | _=>0
def q17 : Nat->Nat
  | 6=>0x6d235ea20
  | 7=>0x234342c80020021d2500aec0506cac86608011a05070243405480089c0601bd838e5329f00e0429190060a0788c0230151a47435248086e14000c806004980012037e2603c050381010011a978040100000c03a0388c0e461502408295081442751882c1a0000038001c00000240503018180003014000d098080233
  | 8=>0x20e334d381e85e0400d6900336c4f00e1846c1e225571d8f3650040e03b0143103c0112c380e421004c3088010408f0104101c02228630140e03c0f00c2b18c01018020f002008e13181403001164360218b004672203d074b7000000904100c3117008118960500812827084700004a000b30d4020ac01000b606003004170041a01c0810c5c00827034690d80d04c1206c000100700431038000182b02801040000640515c37008013400f0180102c330140d02c0000816078000100b000ad000000000102c20010040004800016
  | 9=>0xd16e05d801451001402c9040
  | _=>0
def q16 (s : Nat) (zs : List Nat) : Nat :=
  match s with
  | 6 =>
    let h:=sg 11 zs % 1048573
    let d:=(q17 6>>>(5*(h % 7)))&&&31
    let slot:=((h*1001) % 1048573+d) % 29
    (q18 6>>>(7*slot))&&&127
  | 7 =>
    let h:=sg 0 zs % 1048573
    let d:=(q17 7>>>(9*(h % 110)))&&&511
    let slot:=((h*17) % 1048573+d) % 463
    (q18 7>>>(11*slot))&&&2047
  | 8 =>
    let h:=sg 1 zs % 1048573
    let d:=(q17 8>>>(10*(h % 166)))&&&1023
    let slot:=((h*1) % 1048573+d) % 695
    (q18 8>>>(11*slot))&&&2047
  | 9 =>
    let h:=sg 13 zs % 1048573
    let d:=(q17 9>>>(6*(h % 16)))&&&63
    let slot:=((h*31) % 1048573+d) % 71
    (q18 9>>>(7*slot))&&&127
  | _=>0
def yd (g : Nat) (ws : List Nat) :=
  if g=0 then ws else if g=1 then q38 ws else if g=2 then q37 ws else q38 (q37 ws)
lemma q0v (g : Nat) {s ws} (h : NatRun q7 qe s ws) :
    NatRun q7 qe s (yd g ws):= by
  unfold yd;split
  · exact h
  · split
    · exact q3j h
    · split
      · exact q3i h
      · exact q3j (q3i h)
def qh : Nat->Nat->Bool
  | 0,i=>!(vj 0 i==[qe])
  | s+1,i =>
    let ws:=vj (s+1) i
    !(vy s ws fun tight zs =>
      !(tight&&q0x zs) &&
      (let v:=q16 s zs;!(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4)))))
lemma zc {s i} (hb : qh s i=true)
    (h : NatRun q7 qe s (vj s i)) :
    ∃ q<s,∃ j<q25 q,NatRun q7 qe q (vj q j):= by
  cases s with
  | zero=>simp [qh,q1f h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tight : Bool) (zs : List Nat):=!(tight&&q0x zs) &&
      (let v:=q16 s zs;!(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4))))
    have hF (zs) (hz : NatRun q7 qe s zs) : F (decide (zs.length=s+1)) zs=true:= by
      simp only [F,Bool.and_eq_true,Bool.not_eq_true']
      constructor
      · by_cases hl : zs.length=s+1
        · simp [hl,q1n hz hl]
        · simp [hl]
      · simp only [Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj;by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (q0v _ hz))
    have hN:=y0 h s rfl _ (List.Perm.refl _) F hF
    change !(vy _ _ F)=true at hb;rw [hN] at hb;contradiction
lemma q0k {cap : Nat}
    (hc : ∀ s ≤ cap,∀ i<q25 s,qh s i=true) :
    ∀ s ≤ cap,∀ i<q25 s,¬ NatRun q7 qe s (vj s i):= by
  intro s;induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩:=zc (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h
set_option maxHeartbeats 0 in
lemma q3h :
    qh 0 0=true/\qh 1 0=true/\qh 2 0=true ∧
    qh 3 0=true/\qh 4 0=true/\qh 5 0=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma z6 : span (qh 6) 19 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3s : span (qh 7) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3r : span (qh 7) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3q : span (qh 7) 92 200=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3p : span (qh 8) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3o : span (qh 8) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3n : span (qh 8) 100 200=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3m : span (qh 8) 65 300=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma z9 : span (qh 9) 26 0=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma q3z : span (qh 10) 1 0=true:= by decide +kernel
lemma z7 : span (qh 7) 292 0=true:=(@span_join (qh 7) 100 0 192 q3s (@span_join (qh 7) 100 100 92 q3r q3q))
lemma z8 : span (qh 8) 365 0=true:=(@span_join (qh 8) 200 0 165 (@span_join (qh 8) 100 0 100 q3p q3o) (@span_join (qh 8) 100 200 65 q3n q3m))
lemma q2x (s : Nat) (hs : s ≤ 10) : ∀ i<q25 s,qh s i=true:= by
  interval_cases s
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.2.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.2.2.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.2.2.2.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.2.2.2.2
  · exact fun i hi=>span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok q3z i (Nat.zero_le i) hi
theorem GG (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs517) : False:= by
  rw [← vb,← vc] at h
  have h10 : NatRun q7 qe 10 xs517:=q10 h hs
  have p : xs517.Perm (vj 10 0):= by decide +kernel
  exact q0k q2x 10 (by decide) 0 (by decide) (Run.perm p h10)
theorem noSub {s : Nat} {ws : List Nat} (hs : s ≤ 10) (hsub : ws.Sublist xs517)
    (h : NatRun (mask 232) (goal 232) s ws) : False:= by
  by_cases eq : ws=xs517
  · subst ws;exact GG _ hs h
  · rw [← vb,← vc] at h
    exact yn _ (List.mem_sublists.2 hsub) eq (vl h)
def w46 : Nat := 0xc77f55d26beae1be9f7bce5edfeb6fa7def397b7fac31dfd5749afab8000fbd47a69f06003823bee5ed6e800e08efb97b5ba0003ef51e9a7c18
def xs46 : List Nat := xs517 ++ [w46]
lemma w46_eq : w46 = (xs517.getD 4 0 ||| xs517.getD 5 0) := by decide +kernel
lemma xs46_nd : xs46.Nodup := by decide +kernel
set_option maxHeartbeats 0 in
lemma yn46 : ∀ zs ∈ xs46.sublists, zs ≠ xs46 → zs ≠ xs517 → (s9 zs &&& se) ≠ se := by decide +kernel
def q24_46 : Nat → Nat
  | 0 => 0x20560285e0f0690d00d020520203a150110d0650f01116069028420283e17069000690282e16015168150f0150304a000c00302a138190c81901079108191306910869148691381100869110690d0190c0150106910815120150f03102059140150f0250f0290000e00018000120001400006000100001a000160080e0080a00812008160081a0000501012010160101a0000c00009008090181a01816000080000402812000000201a018110281a0001500819018190100d000190001100811028190101901015020190281100815
  | 1 => 0x31560210e0313a00185430150012900238030fa00985030ea3301940819031b5009114701900248000f93e8193c01501185000e90024c0011139015008e9008f10094d0007a0107a1880e1000e0004c0006a0005e16816000520007e0003a0003e000680087a008761280e0f80e008860086a1286a0085e0084e0106a1086a10816010520104e1081a0103e0103a0102a1700900074000780f86a0f0120f016018520d00e0183e0183a01832018560182a018260e06a1800d00079008790d0660d01a0d0520d04e0d0460d0360e069
  | 2 => 0x25a002526a00e6100e002d40127a0125272009002f400b4901a9a01ace01aca01ac601a7a01a6a01aaa01a6201aa201aa601a5a01a5601a5201a86182f5720196d819708196f01900206001100015600138000ce00160009b6009be00996009f639006009860092a0093a008f20091200a4900a390118600190171f5390163904e3900a010fa010f2010ce43809108fa47085001ac001b839009001c0009f54300939005019860191a018fa019320192e018de018ce018d247879021924700d0298e009c1009bd0018d0294e0211a
  | _ => 0x6480e
def zf46 : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, i =>
    if i < 9 then q36 i
    else
      let k := i - 9
      let c := (q24_46 (k / 83) >>> (20 * (k % 83))) &&& 0xfffff
      let op := c &&& 3
      let a := (c >>> 2) &&& 511
      if op = 0 then zf46 fuel a ^^^ q7
      else let b := c >>> 11; if op = 1 then zf46 fuel a &&& zf46 fuel b else zf46 fuel a ||| zf46 fuel b
def q2a_46 : Nat → Nat
  | 0 => 0x222dd700000001e2d5700000003128cf00000002e28cf00000002228d70000000be28d700000002e116700000002b5be70000000225be70000000222e6700000002257670000000222be700000000048f700000000081f700000000080770000000007ff700000000042770000000007f7700000000067f700000000064f70000000001177000000000647700000000063f70000000007d7700000000063770000000007c770000000007bf70000000dd0ff5000bc56750ff10000056750ff30000000005ff70000000007b7700000000037f70000000007af700000008037750000000295f750000000005f7700000000036f70000000007a7700000000079f700000ea1f0f730000000005ef70000000005e77000000000797700000000036770000000005df700000000078f70000000007877000000000357700000000034770000000005d7700000000077f7000000000777700000000076f7000000000767700000000075f70000000005cf70000000003c7b0000000007efb0000000003bfb0000000003b7b00000000065fb0000000007e7b00000000045fe000000000457e00000000044fe00000000070fe000000000817e00000000080fe000000000007f00000000068ff0000000007dfb0000000e53afb0000000003afb0000000823afb0000000007cfd0000000220ef300000006f0ef30000000be0ef300000006c0ef30000000000efb0000000005c770000000220e7500000006f0e750000000be0e7500000006c0e750000000220d7600000006f0d760000000be0d7600000006c0d760000000000d7e00000001d0d7a00000001c0d7c00000622f286e000000075287b00000002f53fd00000002f74bf00000000074bf000000000743f00000000073bf000000000733f00000000052bf00000001d52bb000000030521f00000001e521f00000002e522f0000000b0522f0000000225237000000000523f00000001d523b00000001c523d00000001a523e000003e1e23970000000b5239f000000051239f00000000023bf0000000004edf0000000581eaf00000007b1ebb000003c5a0c87000003c1b578700001c61e0dc6188bc50750dc8000c45e28284c0000000dd5be50000000007567000006275286a00000007574bb000c450752848
  | 1 => 0x53ff000000000537f00000001b246f00000003003df00000002e03ef00000002203f700000000003ff00000001d03fb00000001c03fd00000001a03fe000000000523f000000082523f00000001b523f000000000527f00000501b239f00000001f23bf00000001b23bf00000001f233f000003e1a233e00000000051ff00000000050ff000000022227700000001f2277000000000227f00000000021ff0000000222177000000000217f00000000020ff000000000507f00000501b204f00000001b205f00000001b206f0000000321fbf0000000301fdf0000000281fdf00000501b1fdd0000000511fdf0000000311fef00000002e1fef0000000221ff70000000be1ff70000000821ffd0000000291ffd0000000281ffd0000000331fff00000002f1fff00000002c1fff0000000011fff0000000001fff00000001d1ffb00000001c1ffd00000001a1ffe00000004f1fff000000000087f0000000004fff0000000001f7f0000000004f7f0000036191eaf0000000321ebf0000000231ebf0000000621ebf0000000191ebf0000000171ebf0000000301edf00000001e1edf00000002e1eef0000000191eef0000000571eef0000000221ef700000002f1eff0000000001eff00000001d1efb00000001c1efd00000001a1efe0000000151ebf0000036191e4f00000001b1e5f00000001b1e6f000003e1e07d700000007007df00000000007ff0000000004e7f00000002e1def0000000221df700000007e1dfb0000000241dfb0000000001dff00000001d1dfb00000001a1dfe00000441b1d5700000001b1d5f0000000004d7f00000001b1cdf00000000006ff0000000001c7f0000000004c7f00000001b1bef000000000067f00000001b1b5f000005c1b05cf00000441b05d700000008805ef00000441b05e700000ec1b05eb00000001b05ef000003a1b05eb00000381b05ed00000361a05ee00000000005ff000000000057f0000000001aff0000000001a7f0000000004bff0000000004aff000000000047f0007c3c1b0c87000000030174f00000002e5acf000cc621e0dc6000c45e280dcc000003e1e2bc70000000302bcf00000001e2bcf000000030115700000002b5ad70000000225ad700001001e0dd5000011c1e0dd60000000bd0dd7
  | 2 => 0x72ff000000000727f0000000e517ff00000000017ff000000000007f000000000707f0000000006f7f0000000006e7f000000000157f0000000006dff0000000006d7f00000002f417f000000000417f00000000040ff000000000147f0000000006cff0000000006c7f00000000013ff0000000006bff0000000006b7f000000000017f0000000006a7f000000000137f00000000069ff00000002f3f7f0000000003f7f0000000003eff000000000697f000000000687f00000000011ff0000000003cff000000000677f00000000066ff000000000667f00000000001ff000000000117f00000000039ff00000000062ff000000000627f000000000397f00000000061ff000000000617f000000000107f00000000060ff000000000607f00000000033ff00000561f0ef300000441f0ef3000003e1e0ef30000000000efb0000000820efb00000007e0efb0000000000eff0000000730efb0000000670efb00000561f0e7500000441f0e75000003e1e0e7500000000031ff000000022317700000002f317f000000000317f00000001d317b00000000030ff000000000307f0000000002fff0000000002f7f0000000910df70000000840df70000000220df700000006f0df70000000be0df700000006d0df700000006c0df700000006a0df70000000680df700000007b0dfb00000007a0dfb0000000780dfb0000000770dfb0000000760dfb00000008e0dfe00000008c0dfe00000008b0dfe00000008a0dfe0000000890dfe00000002f0dff0000000000dff000005e750dfb0000000750dfb00000441d0df300000001d0dfb00000441c0df50000000002eff00000001d2efb00000000058ff0000000002d7f00000561f0d7600000441f0d76000003e1e0d7600000008f0d7e0000000000d7f0000000820d7e0000000000d7e00000007e0d7e0000000730d7e00000006e0d7e0000000630d7e0000000620d7e00000441b0d7600000001b0d7e000003a1b0d7a00000381b0d7c0000000000cff0000000002bff0000000002aff00000001a2afe00000000056ff0000000000bff000000000567f00000000029ff000000000297f00000000028ff00000002f287f000000000287f000000000277f000000000257f00000001b24ef000000000547f
  | _ => 0xdff00000002b0ff70000000220ff700000001f0f77000000000007f000000000417f0000000003f7f00000000039ff000000000317f0000000220df700000002f0dff00000002e0dff0000000000dff0000000880dff00000002b0dff00000002a0dff0000000820dff0000000290dff0000000280dff0000000270dff0000000020dff0000000260dff00000007e0dff0000000240dff0000000230dff0000000030dff0000000220dff0000000200dff00000001f0dff00000001d0dfb00000001d0dff0000000620dff00000001b0dff00000001b0d7f00000001b0d7e00000001b0cff00000001b0bff00000000003ff00000001f03ff00000001b03ff0000000001fff00000001b1fff00000001f087f00000001b087f0000000001eff00000001b1eff00000001b07ff0000000001dff00000001b1dff00000001f06ff00000001b06ff00000001b067f00000001b05ef00000001f05ff00000001b05ff00000001f057f00000001b057f00000602e0fcf00000602e0dcf000011a2e0dcf0000062280dcf000005c280dcf00000601b0ccf00000501b0ccf000003c1b0ccf0000060220dd70000050220dd700000661e0dd700000561e0dd700000441e0dd7000003e1e0dd70000062220de7000005c220de700000441b0ce700000009315f700000000911770000000941177000000093117700000008f1177000000000117700000008811770000000871177000000082117700000007e117700000007d117700000009239f700000002b39f700000002239f700000002b38f700000002238f700000002b38770000000223877000005e2b0ff50000056290ff50000000920ff70000000910ff70000000900ff70000000860ff7000005e2b0ff700000002b0ff70000000850ff70000000840ff70000000830ff700000007f0ff700000007c0ff70000000220ff70000000740ff700000000037f700000002b37f700000001f37f700000002b377700000002237770000000005f7700000001f36f70000000940f770000000870f770000000730f77000005e1f0f7700000001f0f77000000000367700000001f367700000001e367700000001f35f700000001f357700000001f34f700000001f347700000000004ff
def z0_46 (e : Nat) (acc : List Nat) : List Nat :=
  if e == 0 then acc else zf46 5 (e - 1) :: acc
def q3k_46 (j : Nat) : List Nat :=
  let code := (q2a_46 (j / 129) >>> (52 * (j % 129))) &&& 0xfffffffffffff
  let acc := z0_46 ((code >>> 43) &&& 511) (z0_46 ((code >>> 34) &&& 511) (z0_46 ((code >>> 25) &&& 511) (z0_46 ((code >>> 16) &&& 511) (z0_46 ((code >>> 7) &&& 511) []))))
  xl code 0 (xl code 1 (xl code 2 (xl code 3 (xl code 4 (xl code 5 (xl code 6 acc))))))
def q25_46 : Nat → Nat
  | 5 => 1 | 6 => 9 | 7 => 133 | 8 => 314 | 9 => 56 | 10 => 1 | _ => 0
def q3t_46 : Nat → Nat
  | 5 => 0 | 6 => 1 | 7 => 10 | 8 => 143 | 9 => 457 | 10 => 513 | _ => 0
def vj46 (s i : Nat) : List Nat := q3k_46 (q3t_46 s + i)
def q18_46 : Nat → Nat
  | 5 => 0x0
  | 6 => 0xf7461007c000781000301401a00064a540
  | 7 => 0xd5511be065f60000000036750811e000000005888079ce04a084231ac2e0235515848948500113013f171f8000000000062000000d0624440009843c301b83d7b400000000000000047000005f15e24c005a4001d16576d00000000007d65c00001c9061d06aa0703943778004b98b0000052de92806c000f82a09e7c000390661811d248f0681840001c235590e0007f9380000043136001fa3a4007358a5a93a0e40c002090a020818cc141d8270008352c00132020fd2ac005e1b674d51805d93d1c4721ae291f7440dc3b198481180020454c005c54c831ba125f45d0002a5c016c400b054649136d000000d910c06000003a00019cb0685082d000000bc00000000001c8000019c6dc000019946d700000057200581554d0007f1a5001e5001142b1d6001a84144d321d1250866adcc294d315c153f1e1010aa220700416f5a12a09068840900d1566c03c630f53687619180000000000000000311e0000d46980049000000d8000000007c
  | 8 => 0xe81b0e3d981ae000000004773c8b4657455000066220005b88fe442307c8002344b04d8f508993d50afa2540bc3e8b8059b3591a55533800000002688d0000001a107f1566a1de4a08a4e10803410ee0000000031a2a191827364000000000000013e2b50180000039535438d8e2e49bc770162f800066006bc03e129a2a4ce0004a1101fb7280024642097e0015d80000024000000000000000b7000000001ba4be000f032c800d903c4890d8c422e1915ae00049000000001ddaac0680023fbae45008c000007c0e58ba0001f0cf272bdb38e0000030e0006e1050000004c000280541268158009aa31113aa8838ff25ec784f0e2c0013c4e20017a43a0080011d33809800000000000c5a360006b10600000000028400244000fb82b31198ab6e66a6019a0541c05e106f30630dc00000175415001091948000e0840281071c8eb000000464000003480001a18a920000891ec31802e0000042e000fc9803c487c11a692cd000cbd6fbb6000991b12c65e4670294133100003e1d29260020440c000dd087b148c0915acb82000000000160000021aa143ac0d9fb1948287626003b13d291003df84b3261e86072e9c0a4343702d5d8685135a9d12645e894925da8e00e80a9aa4a2459108fe10b1a88adb99240c92b0bf8354307564aca126440e383a4490c91d5b685f9311b81450009510404400016c00000982ae00038822e8e008b0c00000000000750fc4a5b5f91d10583c3c00000120800000db0000006b8000d2b7e6083c0e00888f800109bd0860000000002e01adc4aec53a02c00024880000001b1000000000003592d1c52bc000b0e2c9040010400047327103c56000804000e40c03eae7dfc2a7938d11200105323d11e0897ea0f0648c2792960e21bd6992e65a85507e8d0001348b0050000007d4fc02b828914e6000000340002428003d65440e48f19924000000210604b7000739144d20b028285c9b0009ac0007e000398fd00294411c291061bc00061400030746500000000006c117b20724582320a0366e8000054930be5480e6560564000b8900c49ad25c0000016a294516000404aa000001fec942b83d4003b3000dedf62f04085ecda428964120201649080607592c000d025c00010400000000000a300000000000000000000000000004a2320f78f709e000000f65dd0993430864c211ad8004530740446f88a000004620005323491c4383b0003b02d004a3a0af89d195fdc39130cf565000001258000008b446c000005b00000000012cdf1a84d9040ba2024e1
  | 9 => 0x53370000003c005b0000d6b75000587cc55c006c069fcc2408a80d6757681d78c88397003f0005b44ade39a4bcc000942f00a71b0000a300140000000049d500003a602c54d0002b00771800000040000000bf93b844ac8884208c74c31710339c9bab4e98a07b808790642800430000d903da000013340000cf475f4d7000b030dd1e
  | _ => 0
def q17_46 : Nat → Nat
  | 5 => 0x0
  | 6 => 0x82000000
  | 7 => 0xe000582c0602048201a00000000000000000000000140800020180c00030100000000001e0007010020806814040a00030181101804060000000000000824020001008000300004000c000000400038000403000000002000040603000080000008000400000000402
  | 8 => 0x40000002c0800c030003905819000000040800000000000500f0000002000020000241701c00000060080b018010200108400018010080000000000050bc040040002c0a0000100002008030040400803010060040000401008010000000c02018000000000400024050100100803004000100100c25018010040b000030000200c0300c00000010000001c060040000c01000000201600c020000100c060040403c0000400000000000003800004020000200000004010000100000000000000401800000010000000000004000040000000004010240300000010000000500002000000000000000000000080400806000000040000c0502401000030140000c0000c000440000000000020000000400004010000600800
  | 9 => 0x150001080f0001180200070d0112010001020301030100030000080102000208040300010e04000005000000
  | _ => 0
def q16_46 (s : Nat) (zs : List Nat) : Nat :=
  match s with
  | 5 =>
    let h := sg 0 zs % 1048573
    let d := (q17_46 5 >>> (4 * (h % 2))) &&& 15
    let slot := ((h * 1) % 1048573 + d) % 5
    (q18_46 5 >>> (1 * slot)) &&& 1
  | 6 =>
    let h := sg 0 zs % 1048573
    let d := (q17_46 6 >>> (5 * (h % 8))) &&& 31
    let slot := ((h * 1) % 1048573 + d) % 23
    (q18_46 6 >>> (6 * slot)) &&& 63
  | 7 =>
    let h := sg 0 zs % 1048573
    let d := (q17_46 7 >>> (9 * (h % 98))) &&& 511
    let slot := ((h * 1001) % 1048573 + d) % 293
    (q18_46 7 >>> (10 * slot)) &&& 1023
  | 8 =>
    let h := sg 0 zs % 1048573
    let d := (q17_46 8 >>> (10 * (h % 225))) &&& 1023
    let slot := ((h * 1) % 1048573 + d) % 673
    (q18_46 8 >>> (11 * slot)) &&& 2047
  | 9 =>
    let h := sg 0 zs % 1048573
    let d := (q17_46 9 >>> (8 * (h % 44))) &&& 255
    let slot := ((h * 1) % 1048573 + d) % 131
    (q18_46 9 >>> (8 * slot)) &&& 255
  | _ => 0
def qh46 : Nat → Nat → Bool
  | 0, _ => true
  | s + 1, i =>
    let ws := vj46 (s + 1) i
    !(vy s ws fun tight zs =>
      !(tight && q0x zs) &&
      (let v := q16_46 s zs; !(v / 4 < q25_46 s && (yd (v % 4) zs).isPerm (vj46 s (v / 4)))))
lemma zc46 {s i} (hb : qh46 s i = true) (h : NatRun q7 qe s (vj46 s i)) (hs : 5 ≤ s) :
    ∃ q < s, ∃ j < q25_46 q, NatRun q7 qe q (vj46 q j) := by
  cases s with
  | zero => omega
  | succ s =>
    by_contra! hn
    let F (tight : Bool) (zs : List Nat) := !(tight && q0x zs) &&
      (let v := q16_46 s zs; !(v / 4 < q25_46 s && (yd (v % 4) zs).isPerm (vj46 s (v / 4))))
    have hF (zs) (hz : NatRun q7 qe s zs) : F (decide (zs.length = s + 1)) zs = true := by
      simp only [F, Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · by_cases hl : zs.length = s + 1
        · simp [hl, q1n hz hl]
        · simp [hl]
      · simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
        intro hj; by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (q0v _ hz))
    have hN := y0 h s rfl _ (List.Perm.refl _) F hF
    change !(vy _ _ F) = true at hb; rw [hN] at hb; contradiction
lemma q0k46 {cap : Nat} (hc : ∀ s ≤ cap, ∀ i < q25_46 s, qh46 s i = true) :
    ∀ s ≤ cap, ∀ i < q25_46 s, ¬ NatRun q7 qe s (vj46 s i) := by
  intro s; induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have h5 : 5 ≤ s := by
      by_contra hlt
      have hlt5 : s < 5 := by omega
      interval_cases s <;> simp [q25_46] at hi
    obtain ⟨q, hq, j, hj, h⟩ := zc46 (hc s hs i hi) hh h5
    exact ih q hq (by omega) j hj h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_5 : span (qh46 5) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_6 : span (qh46 6) 9 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_7_0 : span (qh46 7) 60 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_7_1 : span (qh46 7) 60 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_7_2 : span (qh46 7) 13 120 = true := by decide +kernel
lemma sp46_7 : span (qh46 7) 133 0 = true := (@span_join (qh46 7) 60 0 73 sp46_7_0 (@span_join (qh46 7) 60 60 13 sp46_7_1 sp46_7_2))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_8_0 : span (qh46 8) 60 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_8_1 : span (qh46 8) 60 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_8_2 : span (qh46 8) 60 120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_8_3 : span (qh46 8) 60 180 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_8_4 : span (qh46 8) 60 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_8_5 : span (qh46 8) 14 300 = true := by decide +kernel
lemma sp46_8 : span (qh46 8) 314 0 = true := (@span_join (qh46 8) 60 0 254 sp46_8_0 (@span_join (qh46 8) 60 60 194 sp46_8_1 (@span_join (qh46 8) 60 120 134 sp46_8_2 (@span_join (qh46 8) 60 180 74 sp46_8_3 (@span_join (qh46 8) 60 240 14 sp46_8_4 sp46_8_5)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_9 : span (qh46 9) 56 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sp46_10 : span (qh46 10) 1 0 = true := by decide +kernel
lemma q2x46 (s : Nat) (hs : s ≤ 10) : ∀ i < q25_46 s, qh46 s i = true := by
  interval_cases s
  · intro i hi; simp [q25_46] at hi
  · intro i hi; simp [q25_46] at hi
  · intro i hi; simp [q25_46] at hi
  · intro i hi; simp [q25_46] at hi
  · intro i hi; simp [q25_46] at hi
  · exact fun i hi => span_ok sp46_5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok sp46_6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok sp46_7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok sp46_8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok sp46_9 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok sp46_10 i (Nat.zero_le i) hi
theorem noRun46 (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs46) : False := by
  rw [← vb, ← vc] at h
  have h10 : NatRun q7 qe 10 xs46 := q10 h hs
  have p : xs46.Perm (vj46 10 0) := by decide +kernel
  exact q0k46 q2x46 10 (by decide) 0 (by decide) (Run.perm p h10)
theorem noSub46 {s : Nat} {ws : List Nat} (hs : s ≤ 10) (hsub : ws.Sublist xs46)
    (h : NatRun (mask 232) (goal 232) s ws) : False := by
  by_cases eq1 : ws = xs46
  · subst ws; exact noRun46 _ hs h
  · by_cases eq2 : ws = xs517
    · subst ws; exact GG _ hs h
    · rw [← vb, ← vc] at h
      exact yn46 _ (List.mem_sublists.2 hsub) eq1 eq2 (vl h)
end Theta
abbrev q0:=Nat × Nat
def rx : Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def rm (x : Nat) : Nat:=x^^^rx
def rv : q0:=(0,0)
def v5 : q0:=(rx,rx)
def qc : q0:=(rx,0)
def qx (a : q0) : q0:=(rm a.1,rm a.2)
def qn (isOr : Bool) (a b : q0) : q0 :=
  if isOr then (a.1|||b.1,a.2|||b.2) else (a.1&&&b.1,a.2&&&b.2)
def qr (x : Nat) : Prop:=∀ j,252 ≤ j->x.testBit j=false
def qb (a : q0) : Prop:=qr a.1/\qr a.2
def qd (a : q0) : Prop:=qb a/\a ≠ rv/\a ≠ v5
def x3 : q0:=(0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def q1d : q0:=(0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def q1c : q0:=(0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230)
def yv : q0:=(0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def q1b : q0:=(0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def yu : q0:=(0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000,0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def yt : q0:=(0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def q1a : q0:=(0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)
def rj : List q0:=[x3,q1d,q1c,yv,q1b,yu,yt,q1a]
lemma y6 : rx=2 ^ 252 - 1:= by
  have h1 : rx=2 ^ 126*2 ^ 126 - 1:= by decide
  rw [h1,← Nat.pow_add]
lemma qg (j : Nat) : rx.testBit j=decide (j<252):= by
  rw [y6];exact Nat.testBit_two_pow_sub_one 252 j
lemma uw {x : Nat} (hx : qr x) (j : Nat) :
    (rm x).testBit j=if j<252 then !(x.testBit j) else false:= by
  simp only [rm,Nat.testBit_xor,qg]
  by_cases hj : j<252
  · simp [hj]
  · simp [hj,hx j (by omega)]
lemma q5 (x : Nat) {j : Nat} (hj : j<252) :
    (rm x).testBit j=!(x.testBit j):= by
  simp [rm,Nat.testBit_xor,qg,hj]
lemma sc : qr 0:=fun _ _=>Nat.zero_testBit _
lemma vh : qr rx:=fun j hj=>by
  rw [qg];simp [show ¬ j<252 by omega]
lemma xm {x : Nat} (hx : qr x) : qr (rm x):=fun j hj=>by
  rw [uw hx];simp [show ¬ j<252 by omega]
lemma s4 {x y : Nat} (hx : qr x) : qr (x&&&y):=fun j hj=>by
  rw [Nat.testBit_and,hx j hj];rfl
lemma uz {x y : Nat} (hx : qr x) (hy : qr y) : qr (x|||y):=fun j hj=>by
  rw [Nat.testBit_or,hx j hj,hy j hj];rfl
lemma q0s {x y : Nat} (hx : qr x) (hy : qr y) : qr (x^^^y):=fun j hj=>by
  rw [Nat.testBit_xor,hx j hj,hy j hj];rfl
lemma uj {x : Nat} (h : x ≤ rx) : qr x:=fun j hj=>by
  have hlt : x<2 ^ 252:= by
    have hp : 0<2 ^ 252:=Nat.pow_pos (by omega)
    rw [y6] at h;omega
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hj))
lemma vg : qb rv:=⟨sc,sc⟩
lemma q0r : qb v5:=⟨vh,vh⟩
lemma z3 : qb qc:=⟨vh,sc⟩
lemma ye {a : q0} (ha : qb a) : qb (qx a) :=
  ⟨xm ha.1,xm ha.2⟩
lemma x9 (d : Bool) {a b : q0} (ha : qb a) (hb : qb b) :
    qb (qn d a b):= by
  cases d
  · exact ⟨s4 ha.1,s4 ha.2⟩
  · exact ⟨uz ha.1 hb.1,uz ha.2 hb.2⟩
lemma s0 (d : Bool) (a b : q0) : qn d a b=qn d b a:= by
  cases d <;> simp [qn,Nat.and_comm,Nat.or_comm]
lemma so {a : q0} (ha : qb a) :
    qn false a v5=a/\qn true a rv=a ∧
    qn false a rv=rv/\qn true a v5=v5 ∧
    qn false a a=a/\qn true a a=a:= by
  obtain ⟨p,n⟩:=a
  have hp1 : p&&&rx=p:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_and,qg];by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.1 j (by omega)]
  have hn1 : n&&&rx=n:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_and,qg];by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.2 j (by omega)]
  have hp2 : p|||rx=rx:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_or,qg];by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.1 j (by omega)]
  have hn2 : n|||rx=rx:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_or,qg];by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.2 j (by omega)]
  simp [qn,v5,rv,hp1,hn1,hp2,hn2]
lemma v6 : qx rv=v5/\qx v5=rv:= by
  constructor
  · simp [qx,rv,v5,rm]
  · simp [qx,rv,v5,rm]
def y7 (a : Sig) : q0:=(a.1.toNat,a.2.toNat)
lemma xb (x : B) : qr x.toNat:=fun j hj=>by
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hj))
lemma q1h (a : Sig) : qb (y7 a):=⟨xb a.1,xb a.2⟩
lemma xn : Function.Injective y7:= by
  intro a b h
  have h1 : a.1.toNat=b.1.toNat:=congrArg Prod.fst h
  have h2 : a.2.toNat=b.2.toNat:=congrArg Prod.snd h
  exact Prod.ext (BitVec.eq_of_toNat_eq h1) (BitVec.eq_of_toNat_eq h2)
lemma q28 : y7 zero=rv:=rfl
lemma q2y : y7 one=v5:= by
  apply Prod.ext <;> exact (by decide : (BitVec.allOnes 252).toNat=rx)
lemma q0t : y7 target=qc:= by
  apply Prod.ext
  · exact (by decide : (BitVec.allOnes 252).toNat=rx)
  · rfl
lemma q13 (a : Sig) : y7 (neg a)=qx (y7 a):= by
  have hnot (x : B) : (~~~x).toNat=rm x.toNat:= by
    apply Nat.eq_of_testBit_eq;intro j
    rw [BitVec.testBit_toNat,BitVec.getLsbD_not,uw (xb x)]
    by_cases hj : j<252
    · simp [hj,BitVec.testBit_toNat]
    · simp [hj]
  exact Prod.ext (hnot a.1) (hnot a.2)
lemma q14 (d : Bool) (a b : Sig) : y7 (bin d a b)=qn d (y7 a) (y7 b):= by
  cases d <;> simp [bin,qn,y7]
lemma xc {a : Sig} (ha : proper a) : qd (y7 a):= by
  refine ⟨q1h a,fun h=>ha.1 (xn (h.trans q28.symm)),
    fun h=>ha.2 (xn (h.trans q2y.symm))⟩
def qy  (k t : Nat) (S : Finset q0) : Prop :=
  ∀ (P : Nat → Nat → Finset q0 → Prop),(P 0 0 {qc}) →
    (∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (ih : P k t (insert (qx a) U)),P (k+1) (t+1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (ih : P k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) → P k t S
theorem qy.stop   : qy 0 0 {qc}:=by
  intro P stop unary binary
  exact @stop  
theorem qy.unary  {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)) : qy (k+1) (t+1) (insert a U):=by
  intro P stop unary binary
  exact @unary k t U a ha hfresh (tail P stop unary binary)
theorem qy.binary  {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)) : qy (k+1) t (insert a (insert b U)):=by
  intro P stop unary binary
  exact @binary k t U a b d ha hb hab hfresh (tail P stop unary binary)
theorem qy.elimInd  {P : Nat → Nat → Finset q0 → Prop}
    (stop : P 0 0 {qc})
    (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)) (ih : P k t (insert (qx a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)) (ih : P k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset q0} (h : qy k t S) : P k t S:=by
  apply And.right (a:=qy k t S)
  apply h (fun k t S=>qy k t S ∧ P k t S)
  · exact ⟨@qy.stop  ,@stop  ⟩
  · intro k t U a ha hfresh prev
    exact ⟨@qy.unary k t U a ha hfresh prev.1,@unary k t U a ha hfresh prev.1 prev.2⟩
  · intro k t U a b d ha hb hab hfresh prev
    exact ⟨@qy.binary k t U a b d ha hb hab hfresh prev.1,@binary k t U a b d ha hb hab hfresh prev.1 prev.2⟩
theorem qy.elimCases  {P : Nat → Nat → Finset q0 → Prop}
    (stop : P 0 0 {qc})
    (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset q0} (h : qy k t S) : P k t S:=by
  apply qy.elimInd (P:=P) (h:=h)
  · exact @stop  
  · intro k t U a ha hfresh prev ih
    exact @unary k t U a ha hfresh prev
  · intro k t U a b d ha hb hab hfresh prev ih
    exact @binary k t U a b d ha hb hab hfresh prev
theorem qy.byInd  {P : ∀ (k t : Nat) (S : Finset q0),qy k t S → Prop}
  (stop : P 0 0 {qc} (@qy.stop ))
  (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)) (ih : P k t (insert (qx a) U) tail),P (k+1) (t+1) (insert a U) (@qy.unary k t U a ha hfresh tail))
  (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)) (ih : P k t (insert (qn d a b) U) tail),P (k+1) t (insert a (insert b U)) (@qy.binary k t U a b d ha hb hab hfresh tail)) {k t : Nat} {S : Finset q0} (h : qy k t S) : P k t S h:=by
  have aux : ∀ hx : qy k t S,P k t S hx:=by
    apply qy.elimInd (P:=fun k t S=>∀ hx : qy k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop 
    · intro k t U a ha hfresh prev ih hx
      exact @unary k t U a ha hfresh prev (ih prev)
    · intro k t U a b d ha hb hab hfresh prev ih hx
      exact @binary k t U a b d ha hb hab hfresh prev (ih prev)
  exact aux h
theorem qy.byCases  {P : ∀ (k t : Nat) (S : Finset q0),qy k t S → Prop}
  (stop : P 0 0 {qc} (@qy.stop ))
  (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)),P (k+1) (t+1) (insert a U) (@qy.unary k t U a ha hfresh tail))
  (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U)) (@qy.binary k t U a b d ha hb hab hfresh tail)) {k t : Nat} {S : Finset q0} (h : qy k t S) : P k t S h:=by
  have aux : ∀ hx : qy k t S,P k t S hx:=by
    apply qy.elimCases (P:=fun k t S=>∀ hx : qy k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop 
    · intro k t U a ha hfresh prev hx
      exact @unary k t U a ha hfresh prev
    · intro k t U a b d ha hb hab hfresh prev hx
      exact @binary k t U a b d ha hb hab hfresh prev
  exact aux h
lemma z5 {k t : Nat} {S : Finset Sig} (h : Live k t S) :
    qy k t (S.image y7):= by
  induction h using Live.byInd with
  | stop=>simpa [q0t] using qy.stop
  | @unary k t U a ha hf _ ih =>
    simp only [Finset.image_insert,q13] at ih ⊢
    have hf' : qx (y7 a) ∉ insert (y7 a) (U.image y7):= by
      rw [← Finset.image_insert,← q13]
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hf (xn he ▸ hy)
    exact qy.unary (xc ha) hf' ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    simp only [Finset.image_insert,q14] at ih ⊢
    have hf' : qn d (y7 a) (y7 b) ∉ insert (y7 a) (insert (y7 b) (U.image y7)):= by
      rw [← Finset.image_insert,← Finset.image_insert,← q14]
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hf (xn he ▸ hy)
    exact qy.binary (xc ha) (xc hb) (fun e=>hab (xn e)) hf' ih
lemma q00 {a : Sig} (ha : a ∈ raw) : y7 a ∈ rj:= by
  have h : raw.map y7=rj:= by decide +kernel
  rw [← h];exact List.mem_map_of_mem ha
def r9 (d : Bool) (a : q0) : Nat :=
  if d then a.1^^^a.2 else a.1&&&rm a.2
def q9 (d : Bool) : List q0->Nat
  | []=>0
  | a :: l=>r9 d a|||q9 d l
def rg (a b : q0) : Bool:=Nat.beq a.1 b.1&&Nat.beq a.2 b.2
lemma rf (a b : q0) : rg a b=true ↔ a=b:= by
  cases a;cases b;simp only [rg,Bool.and_eq_true,Nat.beq_eq,Prod.mk.injEq]
def up (x : q0) : List q0->Bool
  | []=>false
  | y :: ys=>rg x y||up x ys
lemma y5 (x : q0) (l : List q0) : up x l=true ↔ x ∈ l:= by
  induction l with
  | nil=>simp [up]
  | cons y ys ih=>simp [up,rf,ih]
def v4 : List q0->Bool
  | []=>true
  | x :: xs=>!up x xs&&v4 xs
lemma ve {l : List q0} (h : v4 l=true) : l.Nodup:= by
  induction l with
  | nil=>exact List.nodup_nil
  | cons x xs ih =>
    simp only [v4,Bool.and_eq_true,Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨fun hm=>by rw [(y5 x xs).mpr hm] at h;exact Bool.false_ne_true h.1.symm,ih h.2⟩
def sn (x : q0) : List q0->Option (List q0)
  | []=>none
  | y :: ys=>if rg x y then some ys else
    match sn x ys with | none=>none | some r=>some (y :: r)
lemma yq {x : q0} {ys r : List q0} (h : sn x ys=some r) :
    ys.Perm (x :: r):= by
  induction ys generalizing r with
  | nil=>simp [sn] at h
  | cons y ys ih =>
    simp only [sn] at h
    cases he : rg x y
    · rw [he] at h
      cases hr : sn x ys with
      | none=>rw [hr] at h;contradiction
      | some r' =>
        rw [hr] at h;injection h with h;subst h
        exact ((ih hr).cons y).trans (List.Perm.swap _ _ _)
    · rw [he] at h;injection h with h;subst h
      rw [(rf x y).mp he]
def vp : List q0->List q0->Bool
  | [],[]=>true
  | x :: xs,ys=>match sn x ys with | none=>false | some ys'=>vp xs ys'
  | _,_=>false
lemma yp {xs ys : List q0} (h : vp xs ys=true) : xs.Perm ys:= by
  induction xs generalizing ys with
  | nil=>cases ys with | nil=>exact List.Perm.nil | cons _ _=>simp [vp] at h
  | cons x xs ih =>
    simp only [vp] at h
    cases he : sn x ys with
    | none=>rw [he] at h;contradiction
    | some ys'=>rw [he] at h;exact ((ih h).cons x).trans (yq he).symm
def qw (del v : List q0) : List q0:=v.filter (fun x=>!(del.contains x))
def vs (a : q0) : List q0->List q0
  | []=>[]
  | x :: xs=>if rg a x then vs a xs else x :: vs a xs
def ug (a b : q0) : List q0->List q0
  | []=>[]
  | x :: xs=>if rg a x||rg b x then ug a b xs else x :: ug a b xs
lemma q0h (a : q0) (v : List q0) : vs a v=qw [a] v:= by
  induction v with
  | nil=>rfl
  | cons x xs ih =>
    simp only [vs,qw,List.filter_cons,List.contains_eq_mem,List.mem_singleton] at ih ⊢
    by_cases h : a=x
    · subst h;rw [(rf a a).mpr rfl];simp [ih]
    · have hf : rg a x=false:= by cases he : rg a x;rfl;exact (h ((rf a x).mp he)).elim
      have hne : decide (x=a)=false:=decide_eq_false (Ne.symm h)
      rw [hf,hne];simp [ih]
lemma q0g (a b : q0) (v : List q0) : ug a b v=qw [a,b] v:= by
  induction v with
  | nil=>rfl
  | cons x xs ih =>
    simp only [ug,qw,List.filter_cons,List.contains_eq_mem,List.mem_cons,List.not_mem_nil,or_false] at ih ⊢
    by_cases h : a=x\/b=x
    · have ht : (rg a x||rg b x)=true:= by
        rcases h with rfl | rfl <;> simp [(rf _ _).mpr rfl]
      have hm : decide (x=a\/x=b)=true:=decide_eq_true (by rcases h with rfl | rfl <;> simp)
      rw [ht,hm];simp [ih]
    · have ha : a ≠ x:=fun e=>h (Or.inl e)
      have hb : b ≠ x:=fun e=>h (Or.inr e)
      have hfa : rg a x=false:= by cases he : rg a x;rfl;exact (ha ((rf a x).mp he)).elim
      have hfb : rg b x=false:= by cases he : rg b x;rfl;exact (hb ((rf b x).mp he)).elim
      have hm : decide (x=a\/x=b)=false:=decide_eq_false (by rintro (rfl | rfl);exact ha rfl;exact hb rfl)
      rw [hfa,hfb,hm];simp [ih]
abbrev y3:=Nat × Nat × Nat
def r0 (z : Nat) (c : y3) : y3 :=
  let nz:=rm z
  (z|||c.1,(z&&&rm c.1)|||(c.2.1&&&nz),
   (z&&&c.2.1)|||(c.2.2&&&nz))
def qz (d : Bool) : List q0->y3
  | []=>(0,0,0)
  | a :: l=>r0 (r9 d a) (qz d l)
def q0a (z : Nat) (c : Nat × Nat) : Nat × Nat :=
  (z|||c.1,(z&&&rm c.1)|||(c.2&&&rm z))
def zi : List q0->Nat × Nat
  | []=>(0,0)
  | a :: l=>q0a (r9 false a) (zi l)
lemma q2c (v : List q0) :
    (zi v).1=(qz false v).1/\(zi v).2=(qz false v).2.1:= by
  induction v with
  | nil=>exact ⟨rfl,rfl⟩
  | cons a l ih=>simp only [zi,qz,q0a,r0,ih.1,ih.2,and_self]
def vr (c : y3) (a : Nat) : Nat:=c.1&&&rm (c.2.1&&&a)
def uc (c : y3) (a b : Nat) : Nat :=
  c.1&&&rm ((c.2.1&&&(a|||b))|||(c.2.2&&&(a&&&b)))
def sv (c : y3) : Prop:=qr c.1/\qr c.2.1/\qr c.2.2
lemma rq (d : Bool) {a : q0} (ha : qb a) : qr (r9 d a):= by
  cases d
  · exact s4 ha.1
  · exact q0s ha.1 ha.2
lemma zl {z : Nat} {c : y3} (hz : qr z) (hc : sv c) :
    sv (r0 z c) :=
  ⟨uz hz hc.1,uz (s4 hz) (s4 hc.2.1),
   uz (s4 hz) (s4 hc.2.2)⟩
lemma ru (d : Bool) {v : List q0} (hv : ∀ a ∈ v,qb a) :
    sv (qz d v):= by
  induction v with
  | nil=>exact ⟨sc,sc,sc⟩
  | cons a l ih =>
    exact zl (rq d (hv a List.mem_cons_self))
      (ih fun b hb=>hv b (List.mem_cons_of_mem _ hb))
lemma q33 {c : y3} {a : Nat} (hc : sv c) (ha : qr a) :
    vr (r0 a c) a=c.1:= by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases hi : i<252
  · simp only [vr,r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
    cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
  · have hge : 252 ≤ i:= by omega
    simp [vr,r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hc.1 i hge]
lemma q32 {c : y3} {a b : Nat} (hc : sv c) (ha : qr a) (hb : qr b) :
    uc (r0 a (r0 b c)) a b=c.1:= by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases hi : i<252
  · simp only [uc,r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
    cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
  · have hge : 252 ≤ i:= by omega
    simp [uc,r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.1 i hge]
lemma zq {c : y3} {a b : Nat} (hc : sv c) (ha : qr a) (hb : qr b) :
    r0 a (r0 b c)=r0 b (r0 a c):= by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq;intro i
    simp only [r0,Nat.testBit_or]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> (apply Nat.eq_of_testBit_eq;intro i;by_cases hi : i<252)
    · simp only [r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
        cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
    · have hge : 252 ≤ i:= by omega
      simp [r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.2.1 i hge]
    · simp only [r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
        cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
    · have hge : 252 ≤ i:= by omega
      simp [r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.2.2 i hge]
lemma q0i (d : Bool) {l r : List q0} (h : l.Perm r) (hl : ∀ a ∈ l,qb a) :
    qz d l=qz d r:= by
  induction h with
  | nil=>rfl
  | cons a _ ih =>
    exact congrArg (r0 (r9 d a)) (ih fun x hx=>hl x (List.mem_cons_of_mem _ hx))
  | @swap a b t =>
    exact zq (ru d fun x hx=>hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
      (rq d (hl b (List.mem_cons_self)))
      (rq d (hl a (List.mem_cons_of_mem _ List.mem_cons_self)))
  | trans p _ h1 h2=>exact (h1 hl).trans (h2 fun x hx=>hl x (p.mem_iff.mpr hx))
lemma zj (d : Bool) (v : List q0) : (qz d v).1=q9 d v:= by
  induction v with
  | nil=>rfl
  | cons a v ih=>change r9 d a|||(qz d v).1=r9 d a|||q9 d v;rw [ih]
lemma vq : qd qc:=⟨z3,by decide,by decide⟩
lemma qv {k t S} (h : qy k t S) : ∀ a ∈ S,qd a:= by
  induction h using qy.byInd with
  | stop=>simpa using vq
  | unary ha _ _ ih=>simpa using And.intro ha (fun a h=>ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩
lemma xg {k t S} (h : qy k t S) : t ≤ k/\S.card+t ≤ k+1:= by
  induction h using qy.byInd with
  | stop=>simp
  | @unary k t U a _ hf _ ih =>
    have hu : qx a ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : qn d a b ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
lemma q1i (t : Nat) (a : q0) (i : Nat) (hi : i<252)
    (h : (r9 (decide (0<t)) (qx a)).testBit i=true) :
    (r9 true a).testBit i=true:= by
  cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> cases ht : decide (0<t) <;>
    simp only [r9,qx,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_and,
      q5 _ hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
lemma q0u (t d : Bool) (a b : q0) (i : Nat) (hi : i<252)
    (h : (r9 t (qn d a b)).testBit i=true) :
    (r9 t a).testBit i=true\/(r9 t b).testBit i=true:= by
  cases t <;> cases d <;>
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;>
    cases hu : b.1.testBit i <;> cases hv : b.2.testBit i <;>
    simp only [r9,qn,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_or,
      Nat.testBit_and,q5 _ hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
lemma yj (t : Nat) (a : q0) (i : Nat) (hi : i<252)
    (h : (r9 (decide (0<t)) a).testBit i=true) : (r9 true a).testBit i=true:= by
  cases ht : decide (0<t) <;> cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;>
    simp only [r9,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_and,
      q5 _ hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
lemma zh {k t S} (h : qy k t S) (i : Nat) (hi : i<252) :
    ∃ a ∈ S,(r9 (decide (0<t)) a).testBit i=true:= by
  induction h using qy.byInd with
  | stop =>
    refine ⟨qc,by simp,?_⟩
    simp [r9,qc,Nat.testBit_and,q5 _ hi,qg,hi]
  | unary _ _ _ ih =>
    obtain ⟨x,hx,h⟩:=ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,q1i _ _ _ hi h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,yj _ _ _ hi h⟩
  | binary _ _ _ _ _ ih =>
    obtain ⟨x,hx,h⟩:=ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases q0u _ _ _ _ _ hi h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
lemma ss (d : Bool) (v : List q0) (i : Nat) :
    (q9 d v).testBit i=true ↔ ∃ a ∈ v,(r9 d a).testBit i=true:= by
  induction v with
  | nil=>simp [q9]
  | cons a v ih =>
    simp only [q9,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h | ⟨b,hb,h⟩)
      · exact ⟨a,Or.inl rfl,h⟩
      · exact ⟨b,Or.inr hb,h⟩
    · rintro ⟨b,rfl | hb,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b,hb,h⟩
lemma q09 {k t S} {v : List q0} (h : qy k t S) (he : v.toFinset=S) :
    q9 (decide (0<t)) v=rx:= by
  apply Nat.eq_of_testBit_eq;intro i
  rw [qg]
  by_cases hi : i<252
  · obtain ⟨a,hm,ha⟩:=zh h i hi
    have hmem : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ hm)
    simp only [hi,decide_true]
    exact (ss _ _ _).2 ⟨a,hmem,ha⟩
  · simp only [hi,decide_false]
    rw [Bool.eq_false_iff];intro ht
    obtain ⟨a,ha,hbit⟩:=(ss _ _ _).1 ht
    have hv : qb a:=(qv h a (he ▸ List.mem_toFinset.mpr ha)).1
    have hf:=rq (decide (0<t)) hv i (by omega)
    rw [hf] at hbit;contradiction
lemma zm (d : Bool) (l r : List q0) :
    q9 d (l++r)=q9 d l|||q9 d r:= by
  induction l with
  | nil=>simp [q9]
  | cons a l ih=>simp [q9,ih,Nat.or_assoc]
def s8 (U : Finset q0) (del : List q0) : List q0 :=
  del.filter (fun a=>decide (a ∈ U))
lemma vz {v del : List q0} {U : Finset q0}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset=del.toFinset ∪ U) :
    (s8 U del++qw del v).Nodup/\(s8 U del++qw del v).toFinset=U:= by
  have memv (x : q0) : x ∈ v ↔ x ∈ del\/x ∈ U:= by
    rw [← List.mem_toFinset,he];simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq;subst b
    simp [s8] at ha;simp [qw] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,s8,qw,
      decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all
lemma u0 (del v : List q0) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del,x ∈ v) : v.Perm (del++qw del v):= by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e;subst b
    simp [qw] at hb;exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,qw,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma q2b (d : Bool) {v : List q0} {a : q0} (hv : v.Nodup) (hval : ∀ x ∈ v,qb x)
    (ha : a ∈ v) :
    v.length - 1=(qw [a] v).length ∧
      vr (qz d v) (r9 d a)=q9 d (qw [a] v):= by
  have p:=u0 [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l:=p.length_eq;simp at l;omega
  · rw [q0i d p hval]
    have hvd : ∀ x ∈ qw [a] v,qb x:=fun x hx =>
      hval x (p.mem_iff.mpr (List.mem_append_right _ hx))
    exact (q33 (ru d hvd) (rq d (hval a ha))).trans (zj _ _)
lemma q27 (d : Bool) {v : List q0} {a b : q0} (hv : v.Nodup)
    (hval : ∀ x ∈ v,qb x) (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2=(qw [a,b] v).length ∧
      uc (qz d v) (r9 d a) (r9 d b)=q9 d (qw [a,b] v):= by
  have p:=u0 [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l:=p.length_eq;simp at l;omega
  · rw [q0i d p hval]
    have hvd : ∀ x ∈ qw [a,b] v,qb x:=fun x hx =>
      hval x (p.mem_iff.mpr (List.mem_append_right _ hx))
    exact (q32 (ru d hvd) (rq d (hval a ha))
      (rq d (hval b hb))).trans (zj _ _)
lemma q19 : rj.Nodup:= by decide +kernel
lemma rh : ∀ a ∈ rj,qb a:= by
  have hle : rj.all (fun a=>decide (a.1 ≤ rx/\a.2 ≤ rx))=true:= by decide +kernel
  intro a ha
  have h:=of_decide_eq_true (List.all_eq_true.mp hle a ha)
  exact ⟨uj h.1,uj h.2⟩
lemma q0d : rj.all (fun a=>q9 true (rj.erase a)!=rx)=true:= by
  decide +kernel
lemma q1l {k t S} (l : qy k t S) (hs : ∀ a ∈ S,a ∈ rj) : rj.toFinset=S:= by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr=>?_,hs a⟩
  by_contra hn
  have fail:=List.all_eq_true.mp q0d a hr
  have cov : q9 true (rj.erase a)=rx:= by
    apply Nat.eq_of_testBit_eq;intro i;rw [qg]
    by_cases hi : i<252
    · obtain ⟨b,hb,h⟩:=zh l i hi
      have ba : b ≠ a:=fun he=>hn (he ▸ hb)
      have hm:=(List.mem_erase_of_ne ba).mpr (hs _ hb)
      simp only [hi,decide_true]
      exact (ss true _ _).mpr ⟨b,hm,yj _ _ _ hi h⟩
    · simp only [hi,decide_false]
      rw [Bool.eq_false_iff];intro ht
      obtain ⟨b,hb,hbit⟩:=(ss true _ _).mp ht
      have hbv:=rh b (List.mem_of_mem_erase hb)
      have hf:=rq true hbv i (by omega)
      rw [hf] at hbit;contradiction
  simp [cov] at fail
def q0w : Nat:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cb70ca41b4174c6b5c8dc87531b7a7a7a5074cd8a3e7ab966b5620c41cd99c659b5a7f5391beb8f399eb78a62dc8d4ea48db9593e7aec79a7c8b9b766e71b7a74f5ecdcc88f3e1b4141418a74b9505341cd0cec62667ab940f59beca7c6921beb87925db75062c89689e796cd9b5341b579a7dccdb7cddca741e29253e7a49bb5a77a7a7a50e20c8aec7a66b953f0cd410ccc928f531b39f5a7e359f5f4b78af0a49fdbdc9f668fec7a3ee41be766b7b9c8a77ae2393ea4e759eca74141418ae26650b5410ccd3ef0b97a66fa39873e1b92c6a7e39bc6f9b750f0e760f2c8600c87b54153e41ba40c
def q1k : Nat:=0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a51d000e00000eafaf3ca338a54e90779706a54e970505a39003060202a3970b06071d90030e0b653805a53c054e074e0b03af363c38e807a5a5a51d000e00000eafaf51e84ea538361a0306a538030505e83697066c6ce8030b06071d36970e0b654e05a551053807380b97af90514ea307a5a5a51d00af0000af0e0e774ee8a5a3363c0307a5a3030b0b4e36970744444e030507061d3697af0558e80ba5770ba306a305970e9077e83806a5a5a51d00af0000af0e0e1a38a3a5e890519707a5e8970b0b389003072c2c38970507061d9003af0558a30ba51a0be806e805030e361aa34e06a5a5a5
def v9 : Nat:=0x9a999e949592935d4f4e626355565354e3dedfdcdd5c5b79eb747877e9eae7e88972736a696f676e6b6d71706c68664029a6a5a43a39181110150e14121317160f0d0cb8b73e3f2728201f241c23212226251e1d1bcac9c83837989796f991908ffbfaa1a09ff7f8f5f69d9c9b6160525150db5a594d46454a494744484c4b434241e4e1e05f5ee2d9dad1d0d6d4d2cfd3d8d7ced5cd5857f0f18e8d7675f4e6e588876564eeefeced8c8b8af3f2867e7d83827f818584807c7b7accb5b63d1a19c7c6a3a2360504090806070b0a03020100cbb3b4abaab0aeacadb2b1a9a8afa73c3bc5bdbcc2c0bebfc4c3bbc1bab92f2e3332303135342d2c2b2a
def v8 : Nat:=0xa18c3d5f5e3c3bcce4cb8d8e9fa08a8b4063623f3e6061f3cac59d865c5b38373658572d302f2c323134332e2b352af4f2e3c8c9c6c7e2bbbebdbac0bfc3c2bcc4c1b99e8987889b9c7c7f7e7b828184837d85807a5d3a39595afbeeefb8e1b3b49a789875765655282752191af0f1faecedb7b5b6e0a9acabaeada8b1b0aab2afa779997796972954531e212023221d25241f261c1b5051eae9e5e6f8f7a6dfdea2a3dad9959473729164654f184d03060508070a0904010b0200ebe8e7f9f6f5a5a4dddcdbced2d1d4d3d7d6d0d8d5cfcd749392686b6a6e6d706f69716c67668f904e0f12111413161510170e0d0c43474649484b4a454c424441
def sw (key j : Nat) : Nat:=(key>>>(8*j))&&&255
def u7 (f : Nat->Nat) (x : Nat) : Nat->Nat->Nat
  | 0,acc=>acc
  | j+1,acc =>
    u7 f x j ((acc<<<1)|||(if x.testBit (f j) then 1 else 0))
def qu (f : Nat->Nat) (x : Nat) : Nat :=
  if x=0 then 0 else u7 f x 252 0
lemma u3 (f : Nat->Nat) (x : Nat) :
    ∀ (n acc k : Nat),(u7 f x n acc).testBit k =
      if k<n then x.testBit (f k) else acc.testBit (k - n)
  | 0,acc,k=>by simp [u7]
  | n+1,acc,k=>by
    rw [u7,u3]
    by_cases hk : k<n
    · simp [hk,show k<n+1 by omega]
    · by_cases heq : k=n
      · subst heq
        simp only [Nat.lt_irrefl,ite_false,Nat.lt_succ_self,ite_true,Nat.sub_self,
          Nat.testBit_or,Nat.testBit_shiftLeft,not_le.mpr Nat.zero_lt_one,
          decide_false,Bool.false_and,Bool.false_or]
        cases x.testBit (f k) <;> rfl
      · have h1 : ¬ k<n+1:= by omega
        have hsub : k - n=(k - (n+1))+1:= by omega
        simp only [hk,h1,ite_false,hsub,Nat.testBit_or,Nat.testBit_shiftLeft]
        have hbit : (if x.testBit (f n)=true then (1 : Nat) else 0).testBit (k - (n+1)+1)=false:= by
          cases x.testBit (f n) <;> simp [Nat.testBit_succ]
        rw [hbit,Bool.or_false]
        simp [show 1 ≤ k - (n+1)+1 by omega]
lemma ql (f : Nat->Nat) (x k : Nat) :
    (qu f x).testBit k=if k<252 then x.testBit (f k) else false:= by
  by_cases hx : x=0
  · subst hx;simp [qu]
  · rw [qu,ite_eq_right hx,u3];simp
lemma r7 (f : Nat->Nat) (x : Nat) : qr (qu f x):=fun j hj=>by
  rw [ql];simp [show ¬ j<252 by omega]
lemma sd (f : Nat->Nat) (a b : Nat) :
    qu f (a&&&b)=qu f a&&&qu f b:= by
  apply Nat.eq_of_testBit_eq;intro j
  simp only [Nat.testBit_and,ql];split_ifs <;> simp
lemma sm (f : Nat->Nat) (a b : Nat) :
    qu f (a|||b)=qu f a|||qu f b:= by
  apply Nat.eq_of_testBit_eq;intro j
  simp only [Nat.testBit_or,ql];split_ifs <;> simp
lemma ry (f : Nat->Nat) (hf : ∀ j<252,f j<252) (a : Nat) :
    qu f (rm a)=rm (qu f a):= by
  apply Nat.eq_of_testBit_eq;intro j
  rw [ql,uw (r7 f a),ql]
  by_cases hj : j<252
  · simp [hj,q5 a (hf j hj)]
  · simp [hj]
lemma rr (f : Nat->Nat) : qu f 0=0:= by
  apply Nat.eq_of_testBit_eq;intro j;rw [ql];split_ifs <;> simp
lemma sh (f : Nat->Nat) (hf : ∀ j<252,f j<252) : qu f rx=rx:= by
  apply Nat.eq_of_testBit_eq;intro j;rw [ql]
  by_cases hj : j<252
  · simp [hj,qg,hf j hj]
  · simp [hj,qg]
lemma ul (f : Nat->Nat) (hf : ∀ j<252,f j<252/\f (f j)=j)
    {a : Nat} (ha : qr a) : qu f (qu f a)=a:= by
  apply Nat.eq_of_testBit_eq;intro j
  rw [ql]
  by_cases hj : j<252
  · have hfj:=hf j hj
    rw [ite_eq_left hj,ql,ite_eq_left hfj.1,hfj.2]
  · rw [ite_eq_right hj];exact (ha j (by omega)).symm
lemma vx : ∀ j : Fin 252,sw v9 j.val<252/\sw v9 (sw v9 j.val)=j.val:= by
  decide +kernel
lemma vw : ∀ j : Fin 252,sw v8 j.val<252/\sw v8 (sw v8 j.val)=j.val:= by
  decide +kernel
lemma q15 : ∀ j : Fin 252,sw q0w j.val<252:= by decide +kernel
lemma q31 : ∀ j : Fin 252,sw q1k j.val<252:= by decide +kernel
def q3g (a : q0) : q0:=(qu (sw v9) a.1,qu (sw v9) a.2)
def q3f (a : q0) : q0:=(qu (sw v8) a.1,qu (sw v8) a.2)
def qj (isB : Bool) (a : q0) : q0:=if isB then q3f a else q3g a
def q1 : List Bool->q0->q0
  | [],a=>a
  | b :: t,a=>q1 t (qj b a)
def uu : Fin 8->List Bool :=
  ![[],[false],[false,true,false,true],[true,false,true],
    [true],[true,false],[false,true,false],[false,true]]
def r1 (g : Fin 8) (a : q0) : q0:=q1 (uu g) a
def zk (g : Fin 8) (a : q0) : q0:=q1 (uu g).reverse a
lemma uy (b : Bool) (a : q0) : qb (qj b a):= by
  cases b
  · exact ⟨r7 (sw v9) a.1,r7 (sw v9) a.2⟩
  · exact ⟨r7 (sw v8) a.1,r7 (sw v8) a.2⟩
lemma q0o (b : Bool) (a : q0) : qj b (qx a)=qx (qj b a):= by
  cases b
  · exact Prod.ext (ry (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1) a.1)
      (ry (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1) a.2)
  · exact Prod.ext (ry (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1) a.1)
      (ry (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1) a.2)
lemma q0p (b d : Bool) (x y : q0) :
    qj b (qn d x y)=qn d (qj b x) (qj b y):= by
  cases b <;> cases d
  · exact Prod.ext (sd (sw v9) x.1 y.1) (sd (sw v9) x.2 y.2)
  · exact Prod.ext (sm (sw v9) x.1 y.1) (sm (sw v9) x.2 y.2)
  · exact Prod.ext (sd (sw v8) x.1 y.1) (sd (sw v8) x.2 y.2)
  · exact Prod.ext (sm (sw v8) x.1 y.1) (sm (sw v8) x.2 y.2)
lemma zx (b : Bool) : qj b rv=rv:= by
  cases b
  · exact Prod.ext (rr (sw v9)) (rr (sw v9))
  · exact Prod.ext (rr (sw v8)) (rr (sw v8))
lemma q0n (b : Bool) : qj b v5=v5:= by
  cases b
  · have hA:=sh (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1)
    simp only [qj,q3g,v5,Bool.false_eq_true,ite_false,hA]
  · have hB:=sh (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1)
    simp only [qj,q3f,v5,ite_true,hB]
lemma z2 (b : Bool) : qj b qc=qc:= by
  cases b
  · have hA:=sh (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1)
    simp only [qj,q3g,qc,Bool.false_eq_true,ite_false,hA,rr]
  · have hB:=sh (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1)
    simp only [qj,q3f,qc,ite_true,hB,rr]
lemma vv (b : Bool) {a : q0} (ha : qb a) :
    qj b (qj b a)=a:= by
  cases b
  · exact Prod.ext (ul (sw v9) (fun j hj=>vx ⟨j,hj⟩) ha.1)
      (ul (sw v9) (fun j hj=>vx ⟨j,hj⟩) ha.2)
  · exact Prod.ext (ul (sw v8) (fun j hj=>vw ⟨j,hj⟩) ha.1)
      (ul (sw v8) (fun j hj=>vw ⟨j,hj⟩) ha.2)
lemma ze (w : List Bool) {a : q0} (ha : qb a) : qb (q1 w a):= by
  induction w generalizing a with
  | nil=>exact ha
  | cons b t ih=>exact ih (uy b a)
lemma us (w : List Bool) (a : q0) : q1 w (qx a)=qx (q1 w a):= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0o,ih,q1]
lemma su (w : List Bool) (d : Bool) (x y : q0) :
    q1 w (qn d x y)=qn d (q1 w x) (q1 w y):= by
  induction w generalizing x y with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0p,ih,q1,q1]
lemma xw (w : List Bool) : q1 w rv=rv:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,zx,ih]
lemma q0l (w : List Bool) : q1 w v5=v5:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0n,ih]
lemma vu (w : List Bool) : q1 w qc=qc:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,z2,ih]
lemma z1 (w1 w2 : List Bool) (a : q0) :
    q1 (w1++w2) a=q1 w2 (q1 w1 a):= by
  induction w1 generalizing a with
  | nil=>rfl
  | cons b t ih=>exact ih (qj b a)
lemma ut (w : List Bool) {a : q0} (ha : qb a) :
    q1 w.reverse (q1 w a)=a:= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih =>
    rw [List.reverse_cons,z1]
    simp only [q1]
    rw [ih (uy b a),vv b ha]
lemma sf (w : List Bool) {a b : q0} (ha : qb a) (hb : qb b)
    (he : q1 w a=q1 w b) : a=b:= by
  have h:=congrArg (q1 w.reverse) he
  rwa [ut w ha,ut w hb] at h
lemma ui (w : List Bool) {a : q0} (h : qd a) :
    qd (q1 w a):= by
  refine ⟨ze w h.1,?_,?_⟩
  · intro h0;exact h.2.1 (sf w h.1 vg (h0.trans (xw w).symm))
  · intro h1;exact h.2.2 (sf w h.1 q0r (h1.trans (q0l w).symm))
def si : Nat->q0
  | 0=>x3 | 1=>q1d | 2=>q1c | 3=>yv
  | 4=>q1b | 5=>yu | 6=>yt | 7=>q1a | _=>rv
lemma y4 (j : Nat) : qb (si j):= by
  match j with
  | 0=>exact rh x3 (by simp [rj])
  | 1=>exact rh q1d (by simp [rj])
  | 2=>exact rh q1c (by simp [rj])
  | 3=>exact rh yv (by simp [rj])
  | 4=>exact rh q1b (by simp [rj])
  | 5=>exact rh yu (by simp [rj])
  | 6=>exact rh yt (by simp [rj])
  | 7=>exact rh q1a (by simp [rj])
  | _+8=>exact vg
def u8 (isB : Bool) (j : Nat) : Nat :=
  ((if isB then 0x43076215 else 0x25613740)>>>(4*j))&&&7
def vo : List Bool->Nat->Nat
  | [],j=>j
  | b :: t,j=>vo t (u8 b j)
set_option maxRecDepth 10000 in
lemma x8 : ∀ (b : Bool) (j : Fin 8),
    qj b (si j.val)=si (u8 b j.val):= by decide +kernel
lemma q06 (b : Bool) (j : Nat) : u8 b j<8:= by
  have h : u8 b j ≤ 7:=Nat.and_le_right
  omega
lemma s3 (w : List Bool) : ∀ (j : Nat),j<8 →
    q1 w (si j)=si (vo w j):= by
  induction w with
  | nil=>intro j _;rfl
  | cons b t ih =>
    intro j hj
    rw [q1,x8 b ⟨j,hj⟩,vo]
    exact ih (u8 b j) (q06 b j)
def qf : List q0:=[x3,yv,yu,yt]
def qa (a : q0) : Bool :=
  rg a x3||rg a yv||rg a yu||rg a yt
lemma ri (a : q0) : qa a=true ↔ a ∈ qf:= by
  simp only [qa,qf,Bool.or_eq_true,rf,List.mem_cons,List.not_mem_nil,or_false]
  tauto
def s5 : Fin 4->q0:=![x3,yv,yu,yt]
def sp : Fin 4->Fin 8:=![0,2,4,6]
lemma yr : ∀ a ∈ qf,qb a:=fun a ha =>
  rh a (by simp only [qf,rj,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢;tauto)
lemma sy (b : Bool) (l : List Nat) (hl : ∀ j ∈ l,j<8)
    (hp : (l.map (u8 b)).Perm l) :
    ((l.map si).map (qj b)).Perm (l.map si):= by
  have heq : (l.map si).map (qj b)=(l.map (u8 b)).map si:= by
    rw [List.map_map,List.map_map]
    exact List.map_congr_left fun j hj=>x8 b ⟨j,hl j hj⟩
  rw [heq];exact hp.map si
lemma yb (b : Bool) : (qf.map (qj b)).Perm qf:= by
  change (([0,3,5,6].map si).map (qj b)).Perm ([0,3,5,6].map si)
  exact sy b [0,3,5,6] (by decide) (by cases b <;> decide)
lemma x0 (b : Bool) {a : q0} (ha : qb a) :
    qj b a ∈ qf ↔ a ∈ qf:= by
  have hp:=yb b
  rw [← hp.mem_iff]
  constructor
  · intro hm;obtain ⟨x,hx,he⟩:=List.mem_map.mp hm
    have hinv : x=a:= by
      have h:=congrArg (qj b) he
      rwa [vv b (yr x hx),vv b ha] at h
    exact hinv ▸ hx
  · exact List.mem_map_of_mem
lemma s1 (w : List Bool) {a : q0} (ha : qb a) :
    q1 w a ∈ qf ↔ a ∈ qf:= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih=>rw [q1,ih (uy b a),x0 b ha]
lemma q0m (b : Bool) : (rj.map (qj b)).Perm rj:= by
  change (([0,1,2,3,4,5,6,7].map si).map (qj b)).Perm ([0,1,2,3,4,5,6,7].map si)
  exact sy b [0,1,2,3,4,5,6,7] (by decide) (by cases b <;> decide)
lemma y2 (w : List Bool) : (rj.map (q1 w)).Perm rj:= by
  induction w with
  | nil=>simp [q1]
  | cons b t ih =>
    have hs:=q0m b
    have hm : rj.map (q1 (b :: t))=(rj.map (qj b)).map (q1 t):= by
      rw [List.map_map];rfl
    rw [hm];exact (hs.map (q1 t)).trans ih
def xt (a : q0) : q0:=(qu (sw q0w) a.1,qu (sw q1k) a.2)
def q3 (i : Fin 4) (a : q0) : q0:=xt (r1 (sp i) a)
lemma re (i : Fin 4) (a : q0) : qb (q3 i a) :=
  ⟨r7 (sw q0w) (r1 (sp i) a).1,
   r7 (sw q1k) (r1 (sp i) a).2⟩
lemma uo (i : Fin 4) (a : q0) : q3 i (qx a)=qx (q3 i a):= by
  rw [q3,q3,r1,r1,us]
  exact Prod.ext (ry (sw q0w) (fun j hj=>q15 ⟨j,hj⟩) _)
    (ry (sw q1k) (fun j hj=>q31 ⟨j,hj⟩) _)
lemma vn (i : Fin 4) (d : Bool) (a b : q0) :
    q3 i (qn d a b)=qn d (q3 i a) (q3 i b):= by
  rw [q3,q3,q3,r1,r1,r1,su]
  cases d
  · exact Prod.ext (sd (sw q0w) _ _) (sd (sw q1k) _ _)
  · exact Prod.ext (sm (sw q0w) _ _) (sm (sw q1k) _ _)
lemma zp : xt qc=qc:= by
  have hP:=sh (sw q0w) (fun j hj=>q15 ⟨j,hj⟩)
  simp only [xt,qc,hP,rr]
lemma vm (i : Fin 4) : q3 i qc=qc:= by
  rw [q3,r1,vu,zp]
set_option maxRecDepth 10000 in
lemma yo : xt x3=rv:= by decide +kernel
lemma zd (i : Fin 4) : r1 (sp i) (s5 i)=x3:= by
  fin_cases i
  · exact s3 _ 0 (by omega)
  · exact s3 _ 3 (by omega)
  · exact s3 _ 5 (by omega)
  · exact s3 _ 6 (by omega)
lemma r8 (i : Fin 4) : q3 i (s5 i)=rv:= by
  rw [q3,zd i,yo]
def r4 (a : q0) : Nat :=
  ((a.1&&&Theta.lo 232)<<<232)|||(a.2&&&Theta.lo 232)
lemma uv (a : q0) (j : Nat) :
    (r4 a).testBit j =
      if j<232 then a.2.testBit j else if j<464 then a.1.testBit (j - 232) else false:= by
  simp only [r4,Theta.lo,Nat.testBit_or,Nat.testBit_and,
    Nat.testBit_two_pow_sub_one,Nat.testBit_shiftLeft]
  by_cases hj : j<232
  · simp [hj,show ¬ 232 ≤ j by omega]
  · by_cases hk : j<464
    · simp [hj,hk,show 232 ≤ j by omega,show j - 232<232 by omega]
    · simp [hj,hk,show 232 ≤ j by omega,show ¬ j - 232<232 by omega]
lemma xy : r4 qc=Theta.goal 232:= by decide +kernel
lemma z4 (a : q0) :
    r4 (qx a)=r4 a^^^Theta.mask 232:= by
  have hmask (j : Nat) : (Theta.mask 232).testBit j=decide (j<464):= by
    simp only [Theta.mask,Theta.lo,Nat.testBit_two_pow_sub_one]
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_xor,hmask,uv,uv]
  by_cases hl : j<232
  · simp [hl,qx,q5 _ (show j<252 by omega),show j<464 by omega]
  · by_cases hh : j<464
    · simp [hl,hh,qx,q5 _ (show j - 232<252 by omega)]
    · simp [hl,hh]
lemma x2 (d : Bool) (a b : q0) :
    r4 (qn d a b)=if d then r4 a|||r4 b else r4 a&&&r4 b:= by
  apply Nat.eq_of_testBit_eq;intro j
  cases d <;> simp only [qn,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_or,
    Nat.testBit_and,uv] <;> split_ifs <;> rfl
lemma q1m {k t S} (h : qy k t S) (v : List q0) (hv : v.Nodup)
    (he : v.toFinset=S) :
    Theta.Run qx (qn false) (qn true) qc k v:= by
  induction h using qy.byInd generalizing v with
  | stop =>
    have hp : ([qc] : List q0).Perm v :=
      List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [he])
    exact Theta.Run.perm hp Theta.Run.done
  | @unary k t U a _ hf _ ih =>
    let rest:=qw [a] v
    have ham : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hn,eq⟩:=vz (del:=[a]) hv (by simp) (by simpa using he)
    let save:=decide (a ∈ U)
    have hkeep : Theta.kept save a rest=s8 U [a]++rest:= by
      by_cases hm : a ∈ U <;> simp [save,Theta.kept,s8,hm]
    rw [← hkeep] at hn eq
    have hs : (qx a :: Theta.kept save a rest).toFinset=insert (qx a) U:= by
      rw [List.toFinset_cons,eq]
    have hnd : (qx a :: Theta.kept save a rest).Nodup:= by
      refine List.nodup_cons.mpr ⟨fun hz=>hf (Finset.mem_insert_of_mem ?_),hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p:=u0 [a] v hv (by simp) (by simpa using ham)
    exact Theta.Run.perm p.symm (Theta.Run.one true save (ih _ hnd hs))
  | @binary k t U a b d _ _ hab hf _ ih =>
    let rest:=qw [a,b] v
    have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨hn,eq⟩:=vz (del:=[a,b]) hv (by simp [hab]) (by simpa using he)
    let sa:=decide (a ∈ U);let sb:=decide (b ∈ U)
    have hkeep : Theta.kept sa a (Theta.kept sb b rest)=s8 U [a,b]++rest:= by
      by_cases ham : a ∈ U <;> by_cases hbm : b ∈ U <;> simp [sa,sb,Theta.kept,s8,ham,hbm]
    rw [← hkeep] at hn eq
    have hs : (qn d a b :: Theta.kept sa a (Theta.kept sb b rest)).toFinset=insert (qn d a b) U:= by
      rw [List.toFinset_cons,eq]
    have hnd : (qn d a b :: Theta.kept sa a (Theta.kept sb b rest)).Nodup:= by
      refine List.nodup_cons.mpr ⟨fun hz=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)),hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p:=u0 [a,b] v hv (by simp [hab]) (by simpa using And.intro ah bh)
    have hdone:=ih _ hnd hs
    cases d
    · exact Theta.Run.perm p.symm (Theta.Run.two true sa sb hdone)
    · exact Theta.Run.perm p.symm (Theta.Run.two false sa sb hdone)
def vi : List q0:=[q1c,q1a,yv,q1d,yu,yt,q1b]
def rc : List q0:=vi.map xt
lemma yg : vi.toFinset=rj.toFinset.erase x3:= by decide +kernel
lemma x4 (i : Fin 4) : s5 i ∈ rj.toFinset:= by
  fin_cases i <;> decide +kernel
set_option maxRecDepth 10000 in
lemma uk : rc.map r4=Theta.xs517:= by decide +kernel
lemma xx : Theta.xs517.Nodup:= by decide +kernel
lemma y8 : rc.Nodup:= by
  have h:=xx;rw [← uk] at h;exact List.Nodup.of_map _ h
lemma q04 (i : Fin 4) :
    rj.toFinset.image (q3 i)=insert rv rc.toFinset:= by
  have hact : rj.toFinset.image (r1 (sp i))=rj.toFinset:= by
    ext x;simp only [Finset.mem_image,List.mem_toFinset]
    have hp:=y2 (uu (sp i))
    rw [← hp.mem_iff,List.mem_map];rfl
  have hcomp : rj.toFinset.image (q3 i)=rj.toFinset.image xt:= by
    calc rj.toFinset.image (q3 i)
        = (rj.toFinset.image (r1 (sp i))).image xt:= by
          rw [Finset.image_image];rfl
      _=rj.toFinset.image xt:= by rw [hact]
  have hm : rc.toFinset=vi.toFinset.image xt:= by
    ext a;simp [rc,Finset.mem_image,List.mem_map]
  have h0 : x3 ∈ rj.toFinset:=x4 0
  rw [hcomp,hm,yg,← yo,← Finset.image_insert,Finset.insert_erase h0]
def qm (w : List q0) (v : q0) : Prop:=v ∈ w\/¬ qd v
lemma s2 {w : List q0} {a : q0} (haV : qb a) (h : qm w a) :
    a=rv\/a=v5\/(a ∈ w/\qd a):= by
  by_cases hz : a=rv
  · exact Or.inl hz
  by_cases ho : a=v5
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x=>x ⟨haV,hz,ho⟩),haV,hz,ho⟩)
def yc (w : List q0) (z : q0) : Prop :=
  (∃ a ∈ w,qd a/\z=qx a) ∨
  (∃ d a b,a ∈ w/\b ∈ w/\qd a/\qd b/\a ≠ b/\z=qn d a b)
lemma q35 {w a b} (d : Bool) (haV : qb a) (hbV : qb b)
    (ha : qm w a) (hb : qm w b) :
    qm w (qn d a b)\/yc w (qn d a b):= by
  have rz : qm w rv:=Or.inr (fun h=>h.2.1 rfl)
  have ro : qm w v5:=Or.inr (fun h=>h.2.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=so haV
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=so hbV
  rcases s2 haV ha with rfl | rfl | ⟨ham,hap⟩
  · rw [s0];cases d <;> simp_all
  · rw [s0];cases d <;> simp_all
  rcases s2 hbV hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b;cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
lemma q30 (w : List q0) (a : q0) (haV : qb a) (ha : a ∈ w) :
    qm w (qx a)\/yc w (qx a):= by
  rcases s2 haV (Or.inl ha : qm w a) with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr (fun hh=>hh.2.2 v6.1))
  · exact Or.inl (Or.inr (fun hh=>hh.2.1 v6.2))
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
lemma q1j {w : List q0} {z : q0} {k t S} (h : qy k t S)
    (hz : qm w z\/yc w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1/\qy k' t' S'/\∀ a ∈ S',a ∈ w:= by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w\/a=z:= by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=qv h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:=S.erase (qx a)
        have ht : qy k t (insert (qx a) U):= by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:= by
          intro v hv;obtain ⟨hne,hmv⟩:=Finset.mem_erase.mp hv;simpa [hne] using sub v hmv
        have hf : qx a ∉ insert a U:= by
          intro hh;rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qy.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (qn d a b)
        have ht : qy k t (insert (qn d a b) U):= by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:= by
          intro v hv;obtain ⟨hne,hmv⟩:=Finset.mem_erase.mp hv;simpa [hne] using sub v hmv
        have hf : qn d a b ∉ insert a (insert b U):= by
          intro hh;rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qy.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha;have hn : a ≠ z:=fun hh=>hm (hh ▸ ha);simpa [hn] using sub a ha
def qp (i : Fin 4) (k : Nat) (S : Finset q0) : Prop :=
  ∃ m ≤ k,∃ t T,qy m t T/\T ⊆ S.image (q3 i)
lemma v2 (i : Fin 4) : ¬ qp i 10 rj.toFinset:= by
  rintro ⟨m,hm,t,T,h,hs⟩
  rw [q04] at hs
  have ht : ∀ a ∈ T,a ∈ rc:= by
    intro a ha
    rcases Finset.mem_insert.mp (hs ha) with eq | hmem
    · exact False.elim ((qv h _ ha).2.1 eq)
    · exact List.mem_toFinset.mp hmem
  let v:=rc.filter (fun a=>decide (a ∈ T))
  have he : v.toFinset=T:= by
    ext a;simp only [v,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha=>⟨ht _ ha,ha⟩⟩
  have hh:=q1m h v (y8.filter _) he
  have hr:=Theta.Run.map (inv':=(·^^^Theta.mask 232))
    (meet':=(·&&&·)) (join':=(·|||·)) r4 z4
    (fun a b=>x2 false a b) (fun a b=>x2 true a b) hh
  rw [xy] at hr
  apply Theta.noSub hm _ hr
  have sub:=List.Sublist.map r4
    (List.filter_sublist (l:=rc) (p:=fun a=>decide (a ∈ T)))
  rwa [uk] at sub
lemma za {i : Fin 4} {k k' : Nat} {S : Finset q0}
    (h : qp i k S) (hk : k ≤ k') : qp i k' S:= by
  obtain ⟨m,hm,t,T,hl,hs⟩:=h;exact ⟨m,hm.trans hk,t,T,hl,hs⟩
lemma x5 {i : Fin 4} {q : Nat} {S S' : Finset q0} {g : q0}
    (hs : S' ⊆ insert g S)
    (hr : qm (S.image (q3 i)).toList (q3 i g) ∨
      yc (S.image (q3 i)).toList (q3 i g))
    (h : qp i q S') : qp i (q+1) S:= by
  obtain ⟨m,hm,t,T,hl,ht⟩:=h
  have sub : ∀ a ∈ T,a ∈ (S.image (q3 i)).toList++[q3 i g]:= by
    intro a ha;obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m',t',T',hm',h',hT'⟩:=q1j hl hr sub
  exact ⟨m',by omega,t',T',h',fun a ha=>Finset.mem_toList.mp (hT' _ ha)⟩
lemma x6 {i : Fin 4} {q : Nat} {S S' : Finset q0} {g : q0}
    (hs : S' ⊆ insert g S)
    (hr : qm (S.image (q3 i)).toList (q3 i g))
    (h : qp i q S') : qp i q S:= by
  obtain ⟨m,hm,t,T,hl,ht⟩:=h
  refine ⟨m,hm,t,T,hl,?_⟩
  intro a ha;obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp=>hp (qv hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb
lemma va {i : Fin 4} {q : Nat} {a : q0} {U : Finset q0}
    (h : qp i q (insert (qx a) U)) : qp i (q+1) (insert a U):= by
  apply x5 (g:=qx a) (by simp [Finset.insert_subset_iff];exact fun _ h=>by simp [h]) _ h
  rw [uo]
  exact q30 _ _ (re i a) (by simp)
lemma un {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : qp i q (insert (qn d a b) U)) : qp i (q+1) (insert a (insert b U)):= by
  apply x5 (g:=qn d a b) (by simp [Finset.insert_subset_iff];exact fun _ h=>by simp [h]) _ h
  rw [vn]
  exact q35 _ (re i a) (re i b) (Or.inl (by simp)) (Or.inl (by simp))
lemma xj {i : Fin 4} {q : Nat} {a : q0} {U : Finset q0}
    (ha : ¬ qd (q3 i a)) (h : qp i q (insert (qx a) U)) :
    qp i q (insert a U):= by
  apply x6 (g:=qx a) (by simp [Finset.insert_subset_iff];exact fun _ h=>by simp [h]) _ h
  rcases s2 (re i a) (Or.inr ha : qm [] (q3 i a)) with hz | ho | hm
  · exact Or.inr (fun hp=>hp.2.2 (by rw [uo,hz,v6.1]))
  · exact Or.inr (fun hp=>hp.2.1 (by rw [uo,ho,v6.2]))
  · simp at hm
lemma rn {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (ha : ¬ qd (q3 i a)) (h : qp i q (insert (qn d a b) U)) :
    qp i q (insert a (insert b U)):= by
  apply x6 (g:=qn d a b) (by simp [Finset.insert_subset_iff];exact fun _ h=>by simp [h]) _ h
  rw [vn,s0]
  have hbv:=re i b
  rcases s2 (re i a) (Or.inr ha : qm [] (q3 i a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp=>hp.2.1 (so hbv).2.2.1)
    · rw [(so hbv).2.1];exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(so hbv).1];exact Or.inl (by simp)
    · exact Or.inr (fun hp=>hp.2.2 (so hbv).2.2.2.1)
  · simp at hm
lemma uq {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (hb : ¬ qd (q3 i b)) (h : qp i q (insert (qn d a b) U)) :
    qp i q (insert a (insert b U)):= by
  rw [s0] at h;rw [Finset.insert_comm];exact rn hb h
lemma ud {k t : Nat} {S : Finset q0} (h : qy k t S) (i : Fin 4) :
    qp i k S:= by
  induction h using qy.byInd with
  | stop=>refine ⟨0,Nat.le_refl _,0,{qc},qy.stop,?_⟩;simp [vm]
  | unary _ _ _ ih=>exact va ih
  | binary _ _ _ _ _ ih=>exact un ih
lemma ue {k t : Nat} {S : Finset q0} (h : qy k t S)
    (i : Fin 4) (a : q0) (ha : a ∈ S) (hc : ¬ qd (q3 i a)) :
    ∃ q<k,qp i q S:= by
  induction h using qy.byInd with
  | stop =>
    have ht : a=qc:=Finset.mem_singleton.mp ha
    exact (hc (by rw [ht,vm];exact vq)).elim
  | @unary k t U b _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k,by omega,xj hc (ud tail i)⟩
    · obtain ⟨q,hq,h⟩:=ih (Finset.mem_insert_of_mem ha);exact ⟨q+1,by omega,va h⟩
  | @binary k t U b c d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k,by omega,rn hc (ud tail i)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k,by omega,uq hc (ud tail i)⟩
      · obtain ⟨q,hq,h⟩:=ih (Finset.mem_insert_of_mem hU);exact ⟨q+1,by omega,un h⟩
def r3 (k : Nat) (S : Finset q0) : Prop :=
  ∀ i q,q+(if s5 i ∈ S then 1 else 0)<k->¬ qp i q S
lemma xf {k : Nat} (hk : k ≤ 12) : r3 k rj.toFinset:= by
  intro i q hq h;rw [ite_eq_left (x4 i)] at hq
  exact v2 i (za h (by omega))
lemma xu (a : q0) : a ∈ qf ↔ ∃ i,s5 i=a:= by
  rw [← List.mem_ofFn];rfl
lemma q0j {k : Nat} {a : q0} {U : Finset q0}
    (h : r3 (k+1) (insert a U)) : r3 k (insert (qx a) U):= by
  intro i q hq hf
  by_cases hp : s5 i ∈ insert a U
  · by_cases ht : s5 i ∈ insert (qx a) U
    · rw [ite_eq_left ht] at hq;exact h i (q+1) (by simp [hp];omega) (va hf)
    · rw [ite_eq_right ht] at hq
      have he : s5 i=a :=
        (Finset.mem_insert.mp hp).resolve_right (fun hm=>ht (Finset.mem_insert_of_mem hm))
      have hz : ¬ qd (q3 i a):= by rw [← he,r8];exact fun hz=>hz.2.1 rfl
      exact h i q (by simp [hp];omega) (xj hz hf)
  · exact h i (q+1) (by simp [hp];split at hq <;> omega) (va hf)
lemma zv {k : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : r3 (k+1) (insert a (insert b U))) : r3 k (insert (qn d a b) U):= by
  intro i q hq hf
  by_cases hp : s5 i ∈ insert a (insert b U)
  · by_cases ht : s5 i ∈ insert (qn d a b) U
    · rw [ite_eq_left ht] at hq;exact h i (q+1) (by simp [hp];omega) (un hf)
    · rw [ite_eq_right ht] at hq
      rcases Finset.mem_insert.mp hp with ha | hb
      · have hz : ¬ qd (q3 i a):= by rw [← ha,r8];exact fun hz=>hz.2.1 rfl
        exact h i q (by simp [hp];omega) (rn hz hf)
      · rcases Finset.mem_insert.mp hb with hb | hU
        · have hz : ¬ qd (q3 i b):= by rw [← hb,r8];exact fun hz=>hz.2.1 rfl
          exact h i q (by simp [hp];omega) (uq hz hf)
        · exact (ht (Finset.mem_insert_of_mem hU)).elim
  · exact h i (q+1) (by simp [hp];split at hq <;> omega) (un hf)
lemma xz {k t : Nat} {a : q0} {U : Finset q0}
    (h : r3 (k+1) (insert a U)) (tail : qy k t (insert (qx a) U)) :
    a ∉ qf:= by
  intro hm;obtain ⟨i,rfl⟩:=(xu _).mp hm
  have hz : ¬ qd (q3 i (s5 i)):= by rw [r8];exact fun hz=>hz.2.1 rfl
  have ho : ¬ qd (q3 i (qx (s5 i))):= by
    rw [uo,r8,v6.1];exact fun hp=>hp.2.2 rfl
  obtain ⟨q,hq,hf⟩:=ue tail i (qx (s5 i)) (Finset.mem_insert_self _ _) ho
  exact h i q (by simp;omega) (xj hz hf)
lemma xp {k t : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : r3 (k+1) (insert a (insert b U))) (tail : qy k t (insert (qn d a b) U)) :
    (a ∈ qf->d=true/\a ∉ U)/\(b ∈ qf->d=true/\b ∉ U):= by
  have leftSide {a b : q0} (h : r3 (k+1) (insert a (insert b U)))
      (tail : qy k t (insert (qn d a b) U)) (hm : a ∈ qf) : d=true/\a ∉ U:= by
    obtain ⟨i,rfl⟩:=(xu _).mp hm
    have hz : ¬ qd (q3 i (s5 i)):= by rw [r8];exact fun hz=>hz.2.1 rfl
    constructor
    · cases d
      · exfalso
        have ho : ¬ qd (q3 i (qn false (s5 i) b)):= by
          rw [vn,r8,s0,(so (re i b)).2.2.1]
          exact fun hp=>hp.2.1 rfl
        obtain ⟨q,hq,hf⟩:=ue tail i _ (Finset.mem_insert_self _ _) ho
        exact h i q (by simp;omega) (rn hz hf)
      · rfl
    · intro hU
      obtain ⟨q,hq,hf⟩:=ue tail i _ (Finset.mem_insert_of_mem hU) hz
      exact h i q (by simp;omega) (rn hz hf)
  refine ⟨leftSide h tail,?_⟩
  apply leftSide (a:=b) (b:=a)
  · rwa [Finset.insert_comm]
  · rwa [s0]
def q2  (k t : Nat) (S : Finset q0) : Prop :=
  ∀ (P : Nat → Nat → Finset q0 → Prop),(P 0 0 {qc}) →
    (∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (ih : P k t (insert (qx a) U)),P (k+1) (t+1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (ih : P k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) → P k t S
theorem q2.stop   : q2 0 0 {qc}:=by
  intro P stop unary binary
  exact @stop  
theorem q2.unary  {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)) : q2 (k+1) (t+1) (insert a U):=by
  intro P stop unary binary
  exact @unary k t U a ha hf hr (tail P stop unary binary)
theorem q2.binary  {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)) : q2 (k+1) t (insert a (insert b U)):=by
  intro P stop unary binary
  exact @binary k t U a b d ha hb hab hf hra hrb (tail P stop unary binary)
theorem q2.elimInd  {P : Nat → Nat → Finset q0 → Prop}
    (stop : P 0 0 {qc})
    (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)) (ih : P k t (insert (qx a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)) (ih : P k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset q0} (h : q2 k t S) : P k t S:=by
  apply And.right (a:=q2 k t S)
  apply h (fun k t S=>q2 k t S ∧ P k t S)
  · exact ⟨@q2.stop  ,@stop  ⟩
  · intro k t U a ha hf hr prev
    exact ⟨@q2.unary k t U a ha hf hr prev.1,@unary k t U a ha hf hr prev.1 prev.2⟩
  · intro k t U a b d ha hb hab hf hra hrb prev
    exact ⟨@q2.binary k t U a b d ha hb hab hf hra hrb prev.1,@binary k t U a b d ha hb hab hf hra hrb prev.1 prev.2⟩
theorem q2.elimCases  {P : Nat → Nat → Finset q0 → Prop}
    (stop : P 0 0 {qc})
    (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset q0} (h : q2 k t S) : P k t S:=by
  apply q2.elimInd (P:=P) (h:=h)
  · exact @stop  
  · intro k t U a ha hf hr prev ih
    exact @unary k t U a ha hf hr prev
  · intro k t U a b d ha hb hab hf hra hrb prev ih
    exact @binary k t U a b d ha hb hab hf hra hrb prev
theorem q2.byInd  {P : ∀ (k t : Nat) (S : Finset q0),q2 k t S → Prop}
  (stop : P 0 0 {qc} (@q2.stop ))
  (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)) (ih : P k t (insert (qx a) U) tail),P (k+1) (t+1) (insert a U) (@q2.unary k t U a ha hf hr tail))
  (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)) (ih : P k t (insert (qn d a b) U) tail),P (k+1) t (insert a (insert b U)) (@q2.binary k t U a b d ha hb hab hf hra hrb tail)) {k t : Nat} {S : Finset q0} (h : q2 k t S) : P k t S h:=by
  have aux : ∀ hx : q2 k t S,P k t S hx:=by
    apply q2.elimInd (P:=fun k t S=>∀ hx : q2 k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop 
    · intro k t U a ha hf hr prev ih hx
      exact @unary k t U a ha hf hr prev (ih prev)
    · intro k t U a b d ha hb hab hf hra hrb prev ih hx
      exact @binary k t U a b d ha hb hab hf hra hrb prev (ih prev)
  exact aux h
theorem q2.byCases  {P : ∀ (k t : Nat) (S : Finset q0),q2 k t S → Prop}
  (stop : P 0 0 {qc} (@q2.stop ))
  (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)),P (k+1) (t+1) (insert a U) (@q2.unary k t U a ha hf hr tail))
  (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U)) (@q2.binary k t U a b d ha hb hab hf hra hrb tail)) {k t : Nat} {S : Finset q0} (h : q2 k t S) : P k t S h:=by
  have aux : ∀ hx : q2 k t S,P k t S hx:=by
    apply q2.elimCases (P:=fun k t S=>∀ hx : q2 k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop 
    · intro k t U a ha hf hr prev hx
      exact @unary k t U a ha hf hr prev
    · intro k t U a b d ha hb hab hf hra hrb prev hx
      exact @binary k t U a b d ha hb hab hf hra hrb prev
  exact aux h
lemma q2.nlive {k t S} (h : q2 k t S) : qy k t S:= by
  induction h using q2.byInd with
  | stop=>exact qy.stop
  | unary ha hf _ _ ih=>exact qy.unary ha hf ih
  | binary ha hb hab hf _ _ _ ih=>exact qy.binary ha hb hab hf ih
lemma yl {k t S} (h : qy k t S) (hb : r3 k S) : q2 k t S:= by
  induction h using qy.byInd with
  | stop=>exact q2.stop
  | unary ha hf tail ih =>
    exact q2.unary ha hf (xz hb tail) (ih (q0j hb))
  | binary ha hg hab hf tail ih =>
    obtain ⟨h1,h2⟩:=xp hb tail
    exact q2.binary ha hg hab hf h1 h2 (ih (zv hb))
lemma xe (w : List Bool) {k t : Nat} {S : Finset q0}
    (h : q2 k t S) : q2 k t (S.image (q1 w)):= by
  induction h using q2.byInd with
  | stop=>simpa [vu] using q2.stop
  | @unary k t U a ha hf hr tail ih =>
    have hU : ∀ x ∈ U,qb x:=fun x hx =>
      (qv tail.nlive x (Finset.mem_insert_of_mem hx)).1
    simp only [Finset.image_insert,us] at ih ⊢
    have hne : qx (q1 w a) ∉ insert (q1 w a) (U.image (q1 w)):= by
      rw [← Finset.image_insert,← us]
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      have hyV : qb y:= by
        rcases Finset.mem_insert.mp hy with rfl | hu
        · exact ha.1
        · exact hU y hu
      exact hf (sf w hyV (ye ha.1) he ▸ hy)
    exact q2.unary (ui w ha) hne
      (fun hm=>hr ((s1 w ha.1).mp hm)) ih
  | @binary k t U a b d ha hb hab hf hra hrb tail ih =>
    have hU : ∀ x ∈ U,qb x:=fun x hx =>
      (qv tail.nlive x (Finset.mem_insert_of_mem hx)).1
    simp only [Finset.image_insert,su] at ih ⊢
    have hne : qn d (q1 w a) (q1 w b) ∉
        insert (q1 w a) (insert (q1 w b) (U.image (q1 w))):= by
      rw [← Finset.image_insert,← Finset.image_insert,← su]
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      have hyV : qb y:= by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact ha.1
        rcases Finset.mem_insert.mp hy with rfl | hu
        · exact hb.1
        · exact hU y hu
      exact hf (sf w hyV (x9 d ha.1 hb.1) he ▸ hy)
    have hm (v : q0) (hvV : qb v) (hv : v ∉ U) : q1 w v ∉ U.image (q1 w):= by
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hv (sf w (hU y hy) hvV he ▸ hy)
    refine q2.binary (ui w ha) (ui w hb)
      (fun e=>hab (sf w ha.1 hb.1 e)) hne ?_ ?_ ih
    · intro hx;obtain ⟨h1,h2⟩:=hra ((s1 w ha.1).mp hx)
      exact ⟨h1,hm _ ha.1 h2⟩
    · intro hx;obtain ⟨h1,h2⟩:=hrb ((s1 w hb.1).mp hx)
      exact ⟨h1,hm _ hb.1 h2⟩
lemma sj (t : Nat) : (!Nat.beq t 0)=decide (0<t):= by cases t <;> rfl
def rs (v : List q0) (g : q0) : Bool :=
  !(up g v)&&!(Nat.beq g.1 0&&Nat.beq g.2 0)&&!(Nat.beq g.1 rx&&Nat.beq g.2 rx)
lemma xi {v : List q0} {g : q0} (hg : g ∉ v) (hp : qd g) :
    rs v g=true:= by
  have hm : up g v=false:= by
    cases e : up g v;rfl;exact (hg ((y5 g v).mp e)).elim
  have h0 : (Nat.beq g.1 0&&Nat.beq g.2 0)=false:= by
    cases e : (Nat.beq g.1 0&&Nat.beq g.2 0);rfl
    simp only [Bool.and_eq_true,Nat.beq_eq] at e;exact (hp.2.1 (Prod.ext e.1 e.2)).elim
  have h1 : (Nat.beq g.1 rx&&Nat.beq g.2 rx)=false:= by
    cases e : (Nat.beq g.1 rx&&Nat.beq g.2 rx);rfl
    simp only [Bool.and_eq_true,Nat.beq_eq] at e;exact (hp.2.2 (Prod.ext e.1 e.2)).elim
  simp [rs,hm,h0,h1]
def v7 (k t : Nat) (r : List q0->Bool) (v rest : List q0) (n : Nat) (c : Nat)
    (g : q0) (keep : List (List q0)) : Bool :=
  let d:=!Nat.beq t 0
  let base:=r9 d g|||c
  if Nat.beq n (k - t) then
    Nat.beq base rx&&rs v g&&r (g :: rest)
  else keep.any (fun h=>Nat.ble (n+h.length) (k - t) &&
    Nat.beq (base|||q9 d h) rx&&rs v g&&r (g :: (h++rest)))
def q12 (k t len : Nat) (r : List q0->Bool) (v : List q0) (c : y3) (a : q0) : Bool :=
  !(qa a) &&
    v7 k t r v (vs a v) (len - 1) (vr c (r9 (!Nat.beq t 0) a))
      (qx a) [[],[a]]
def yf (k t len : Nat) (r : List q0->Bool) (v : List q0) : Bool :=
  let c:=qz (!Nat.beq t 0) v
  v.any (q12 k t len r v c)
def sr (a b : q0) (spa spb : Bool) : List (List q0) :=
  if spa then (if spb then [[]] else [[],[b]])
  else (if spb then [[],[a]] else [[],[a],[b],[a,b]])
def xk (r : List q0->Bool) (v : List q0)
    (a b : q0) (ua ub na1 nb1 : Nat) (spa spb : Bool) : Bool :=
  (Nat.beq (ua&&&nb1) 0&&Nat.beq (ub&&&na1) 0&&!spa&&!spb &&
    (let g:=(a.1&&&b.1,a.2&&&b.2);rs v g&&r (g :: ug a b v))) ||
  (Nat.beq (ua&&&b.2) 0&&Nat.beq (ub&&&a.2) 0 &&
    (let g:=(a.1|||b.1,a.2|||b.2);rs v g&&r (g :: ug a b v)))
def u5 (k t len : Nat) (r : List q0->Bool) (v : List q0) (c : y3)
    (a b : q0) (sa sb : Nat) (spa spb : Bool) : Bool :=
  let rest:=ug a b v
  let m:=uc c sa sb
  (!spa&&!spb &&
    v7 k t r v rest (len - 2) m (a.1&&&b.1,a.2&&&b.2) [[],[a],[b],[a,b]]) ||
    v7 k t r v rest (len - 2) m (a.1|||b.1,a.2|||b.2) (sr a b spa spb)
def v1 {α : Type} (p : α->α->Bool) : List α->Bool
  | []=>false
  | a :: t=>t.any (p a)||v1 p t
lemma u6 {α : Type} (p : α->α->Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b=true) (hba : p b a=true) : v1 p v=true:= by
  induction v with
  | nil=>simp at ha
  | cons h v ih =>
    simp only [v1,Bool.or_eq_true]
    by_cases eqA : a=h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b,(List.mem_cons.mp hb).resolve_left (Ne.symm hne),hab⟩)
    · have ha':=(List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b=h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a,ha',hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
def vt (k t len : Nat) (r : List q0->Bool) (v : List q0) : Bool :=
  if Nat.beq t 0&&Nat.beq len (k+2) then
    let u:=(zi v).2
    let acts:=v.map (fun a=>(a,u&&&r9 false a,rm a.1,qa a))
    v1 (fun x y=>xk r v x.1 y.1 x.2.1 y.2.1 x.2.2.1 y.2.2.1 x.2.2.2 y.2.2.2) acts
  else
    let d:=!Nat.beq t 0
    let c:=qz d v
    let items:=v.map (fun a=>(a,r9 d a,qa a))
    v1 (fun x y=>u5 k t len r v c x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2) items
def u1 : List q0->Bool
  | [a]=>rg a qc
  | _=>false
def v0 (k t : Nat) (v : List q0) (u b : List q0->Bool) : Bool :=
  let len:=v.length
  if Nat.blt (k+1) t||Nat.blt (k+2 - t) len then false else
    u1 v||(!Nat.beq t 0&&yf k (t - 1) len u v)||vt k t len b v
def xd : Nat->Nat->List q0->Bool
  | 0,_,v=>u1 v
  | k+1,t,v=>v0 k t v (xd k (t - 1)) (xd k t)
lemma xh {k t m : Nat} {v rest h : List q0} {g : q0} {opts : List (List q0)}
    {S : Finset q0} {r : List q0->Bool} (l : qy m t S)
    (hle : m ≤ k) (hp : qd g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g :: (h++rest)).Nodup) (he : (g :: (h++rest)).toFinset=S)
    (hr : r (g :: (h++rest))=true) :
    v7 k t r v rest rest.length (q9 (decide (0<t)) rest) g opts=true:= by
  obtain ⟨ht,hc⟩:=xg l
  rw [← he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length ≤ k - t:= by omega
  have cv:=q09 l he
  rw [q9,zm] at cv
  have cov : (r9 (decide (0<t)) g|||q9 (decide (0<t)) rest)|||q9 (decide (0<t)) h=rx:= by
    rw [← cv];ac_rfl
  have hav:=xi ha hp
  by_cases tight : rest.length=k - t
  · have hz : h.length=0:= by omega
    have hem : h=[]:=List.length_eq_zero_iff.mp hz
    subst h
    have ok : r9 (decide (0<t)) g|||q9 (decide (0<t)) rest=rx:= by
      simpa [q9] using cov
    simp only [v7,sj,tight,Nat.beq_refl,ite_true,ok,hav,Bool.and_true,Bool.true_and]
    simpa using hr
  · have hnt : Nat.beq rest.length (k - t)=false:= by
      cases e : Nat.beq rest.length (k - t);rfl;exact (tight (Nat.beq_eq.mp e)).elim
    simp only [v7,sj,hnt,Bool.false_eq_true,ite_false,List.any_eq_true,
      Bool.and_eq_true,Nat.ble_eq,Nat.beq_eq,hav,and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩
lemma x1 {c : y3} {a b : q0} (hc : sv c)
    (op : Bool) (h : r9 false (qn op a b)|||uc c (r9 false a) (r9 false b)=rx) :
    ((c.2.1&&&r9 false a)&&&(if op then b.2 else rm b.1)) |||
    ((c.2.1&&&r9 false b)&&&(if op then a.2 else rm a.1))=0:= by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases hi : i<252
  · have hh:=congrArg (fun z : Nat=>z.testBit i) h
    clear h
    cases op <;> simp only [r9,qn,ite_false,ite_true,uc,qg,
      Nat.testBit_and,Nat.testBit_or,q5 _ hi,Nat.zero_testBit,
      Bool.false_eq_true,hi,decide_true] at hh ⊢ <;>
      cases ax : a.1.testBit i <;> cases ay : a.2.testBit i <;>
      cases bx : b.1.testBit i <;> cases byy : b.2.testBit i <;>
      cases um : c.2.1.testBit i <;> simp [ax,ay,bx,byy,um] at hh ⊢
  · have hge : 252 ≤ i:= by omega
    simp [Nat.testBit_or,Nat.testBit_and,hc.2.1 i hge]
lemma q1e {k r v c a b} (hc : sv c)
    (hlen : v.length - 2=k)
    (h : u5 k 0 v.length r v c a b (r9 false a) (r9 false b) (qa a) (qa b)=true) :
    xk r v a b (c.2.1&&&r9 false a) (c.2.1&&&r9 false b) (rm a.1) (rm b.1)
      (qa a) (qa b)=true:= by
  have heq : Nat.beq (v.length - 2) (k - 0)=true:=Nat.beq_eq.mpr (by omega)
  simp only [u5,v7,heq,ite_true,Bool.or_eq_true,Bool.and_eq_true,
    Nat.beq_eq] at h
  simp only [xk,Bool.or_eq_true,Bool.and_eq_true,Nat.beq_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hcov,hav⟩,hr⟩ | ⟨⟨hcov,hav⟩,hr⟩
  · have h0:=x1 hc false hcov
    have h1 : (c.2.1&&&r9 false a)&&&rm b.1=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢;exact hi.1
    have h2 : (c.2.1&&&r9 false b)&&&rm a.1=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢;exact hi.2
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · have h0:=x1 hc true hcov
    have h1 : (c.2.1&&&r9 false a)&&&b.2=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢;exact hi.1
    have h2 : (c.2.1&&&r9 false b)&&&a.2=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢;exact hi.2
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩
lemma zz {m t k : Nat} {U : Finset q0} {a : q0} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a U) (hle : m ≤ k)
    (fresh : qx a ∉ insert a U) (ha : a ∉ qf) (l : q2 m t (insert (qx a) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qx a) U->r v=true) :
    yf k t v.length r v=true:= by
  let h:=s8 U [a];let rest:=qw [a] v
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩:=vz (del:=[a]) (U:=U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn;change (h++rest).toFinset=U at eq
  have nn : qx a ∉ v:=fun hm=>fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : qx a ∉ U:=fun hm=>fresh (Finset.mem_insert_of_mem hm)
  have hnd : (qx a :: (h++rest)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm=>nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (qx a :: (h++rest)).toFinset=insert (qx a) U:= by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]]:= by by_cases hm : a ∈ U <;> simp [h,s8,hm]
  apply List.any_eq_true.mpr;refine ⟨a,ah,?_⟩
  unfold q12;rw [sj,q0h]
  obtain ⟨hlen,hmask⟩:=q2b (decide (0<t)) hv hval ah
  rw [hlen,hmask];apply Bool.and_eq_true_iff.mpr
  have hna : qa a=false:= by cases es : qa a;rfl;exact (ha ((ri a).mp es)).elim
  exact ⟨by simp [hna],
    xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
lemma yi {m t k : Nat} {U : Finset q0} {a b : q0} {d : Bool} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a (insert b U)) (hle : m ≤ k)
    (hab : a ≠ b) (fresh : qn d a b ∉ insert a (insert b U))
    (hra : a ∈ qf->d=true/\a ∉ U) (hrb : b ∈ qf->d=true/\b ∉ U)
    (l : q2 m t (insert (qn d a b) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qn d a b) U->r v=true) :
    u5 k t v.length r v (qz (decide (0<t)) v) a b
      (r9 (decide (0<t)) a) (r9 (decide (0<t)) b) (qa a) (qa b)=true:= by
  let g:=qn d a b;let h:=s8 U [a,b];let rest:=qw [a,b] v
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩:=vz (del:=[a,b]) (U:=U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn;change (h++rest).toFinset=U at eq
  have nn : g ∉ v:=fun hm=>fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U:=fun hm=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g :: (h++rest)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm=>nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g :: (h++rest)).toFinset=insert g U:= by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]]:= by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,s8,ha,hb]
  have allow : h ∈ sr a b (qa a) (qa b):= by
    cases esa : qa a <;> cases esb : qa b <;> simp only [sr,ite_true,ite_false,Bool.false_eq_true]
    · exact opts
    · have hnb : b ∉ U:=(hrb ((ri b).mp esb)).2
      by_cases ha : a ∈ U <;> simp [h,s8,ha,hnb]
    · have hna : a ∉ U:=(hra ((ri a).mp esa)).2
      by_cases hb : b ∈ U <;> simp [h,s8,hna,hb]
    · have hna : a ∉ U:=(hra ((ri a).mp esa)).2
      have hnb : b ∉ U:=(hrb ((ri b).mp esb)).2
      simp [h,s8,hna,hnb]
  obtain ⟨hlen,hmask⟩:=q27 (decide (0<t)) hv hval ah bh hab
  unfold u5;dsimp only;rw [q0g,hlen,hmask]
  cases d with
  | false =>
    have na : qa a=false:= by cases es : qa a;rfl;exact (Bool.false_ne_true (hra ((ri a).mp es)).1).elim
    have nb : qa b=false:= by cases es : qa b;rfl;exact (Bool.false_ne_true (hrb ((ri b).mp es)).1).elim
    apply Bool.or_eq_true_iff.mpr;left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr;right
    exact xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)
lemma zw {m t k : Nat} {U : Finset q0} {a b : q0} {d : Bool} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a (insert b U)) (hle : m ≤ k)
    (hab : a ≠ b) (fresh : qn d a b ∉ insert a (insert b U))
    (hra : a ∈ qf->d=true/\a ∉ U) (hrb : b ∈ qf->d=true/\b ∉ U)
    (l : q2 m t (insert (qn d a b) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qn d a b) U->r v=true) :
    vt k t v.length r v=true:= by
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1:=yi hv hval he hle hab fresh hra hrb l ih
  have e' : v.toFinset=insert b (insert a U):= by rwa [Finset.insert_comm b a]
  have hf : qn d b a ∉ insert b (insert a U):= by rwa [s0 d b a,Finset.insert_comm b a]
  have ht : q2 m t (insert (qn d b a) U):= by rwa [s0 d b a]
  have h2:=yi hv hval e' hle hab.symm hf hrb hra ht (by simpa only [s0 d b a] using ih)
  unfold vt;split
  · rename_i cut
    simp only [Bool.and_eq_true,Nat.beq_eq] at cut
    obtain ⟨rfl,hvlen⟩:=cut
    have hlen : v.length - 2=k:= by omega
    have hc:=ru false hval
    have hcov2:=(q2c v).2
    let f:=fun x=>(x,(zi v).2&&&r9 false x,rm x.1,qa x)
    have na : f a ∈ v.map f:=List.mem_map_of_mem ah
    have nb : f b ∈ v.map f:=List.mem_map_of_mem bh
    exact u6 _ na nb (fun e=>hab (congrArg Prod.fst e))
      (by simpa only [f,hcov2] using q1e hc hlen h1)
      (by simpa only [f,hcov2] using q1e hc hlen h2)
  · rw [sj]
    let f:=fun x=>(x,r9 (decide (0<t)) x,qa x)
    have na : f a ∈ v.map f:=List.mem_map_of_mem ah
    have nb : f b ∈ v.map f:=List.mem_map_of_mem bh
    exact u6 _ na nb (fun e=>hab (congrArg Prod.fst e)) h1 h2
lemma xq {m t S : Nat} {s : Finset q0} {v : List q0} {u b : List q0->Bool}
    (h : q2 m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset=s)
    (hu : ∀ w,w.Nodup->∀ l ≤ S,q2 l (t - 1) w.toFinset->u w=true)
    (hb' : ∀ w,w.Nodup->∀ l ≤ S,q2 l t w.toFinset->b w=true) :
    v0 S t v u b=true:= by
  have size:=xg h.nlive
  have hval : ∀ x ∈ v,qb x:=fun x hx =>
    (qv h.nlive x (he ▸ List.mem_toFinset.mpr hx)).1
  rw [← he,List.toFinset_card_of_nodup hv] at size
  have hcond : (Nat.blt (S+1) t||Nat.blt (S+2 - t) v.length)=false:= by
    have h1 : Nat.blt (S+1) t=false:= by cases e : Nat.blt (S+1) t;rfl;have:=Nat.blt_eq.mp e;omega
    have h2 : Nat.blt (S+2 - t) v.length=false:= by cases e : Nat.blt (S+2 - t) v.length;rfl;have:=Nat.blt_eq.mp e;omega
    simp [h1,h2]
  unfold v0;dsimp only;rw [hcond];simp only [Bool.false_eq_true,ite_false,sj]
  cases h using q2.byCases with
  | stop =>
    have p : v.Perm [qc]:=List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    rw [List.perm_singleton.mp p];simp [u1,(rf qc qc).mpr rfl]
  | @unary m t U a _ hf hr tail =>
    apply Bool.or_eq_true_iff.mpr;left
    apply Bool.or_eq_true_iff.mpr;right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp,zz hv hval he (by omega) hf hr tail ?_⟩
    intro w hn hs;exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d _ _ hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr;right
    apply zw hv hval he (by omega) hab hf hra hrb tail
    intro w hn hs;exact hb' w hn m (by omega) (hs.symm ▸ tail)
lemma y9 {m t : Nat} {S : Finset q0} (h : q2 m t S) (k : Nat)
    (hk : m ≤ k) (v : List q0) (hv : v.Nodup) (hs : v.toFinset=S) : xd k t v=true:= by
  induction k generalizing m t S v with
  | zero =>
    have hm : m=0:= by omega
    subst m;cases h using q2.byCases
    have p : v.Perm [qc]:=List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    rw [List.perm_singleton.mp p];simp [xd,u1,(rf qc qc).mpr rfl]
  | succ k ih =>
    rw [xd]
    apply xq h hk hv hs <;> exact fun w hn l hl hh=>ih hh hl w hn rfl
def qs (k t : Nat) (v : List q0) : Prop :=
  ∀ m ≤ k,¬ q2 m t v.toFinset
lemma yy {k t : Nat} {v : List q0} (hv : v.Nodup) (hc : xd k t v=false) :
    qs k t v:= by
  intro m hm h;exact Bool.false_ne_true (hc.symm.trans (y9 h k hm v hv rfl))
lemma xv {k t : Nat} {v : List q0} {u b : List q0->Bool} (hv : v.Nodup)
    (hu : ∀ w,u w=false->qs k (t - 1) w)
    (hb : ∀ w,b w=false->qs k t w)
    (hc : v0 k t v u b=false) : qs (k+1) t v:= by
  intro m hm h
  have hu' : ∀ w,w.Nodup->∀ j ≤ k,q2 j (t - 1) w.toFinset->u w=true:= by
    intro w _ j hj r;cases e : u w;exact (hu _ e j hj r).elim;rfl
  have hb' : ∀ w,w.Nodup->∀ j ≤ k,q2 j t w.toFinset->b w=true:= by
    intro w _ j hj r;cases e : b w;exact (hb _ e j hj r).elim;rfl
  exact Bool.false_ne_true (hc.symm.trans (xq h hm hv rfl hu' hb'))
def q2z (mult : Nat) (a : q0) : Nat :=
  let x:=((a.1 % 1048573)*mult+a.2 % 1048573+317) % 1048573
  (x*x*x) % 1048573
def q0c (mult : Nat) : List q0->Nat
  | []=>0
  | a :: l=>q2z mult a+q0c mult l
def uf (mult : Nat) (v : List q0) : Nat :=
  q0c mult v % 1048573
def q6 : Nat->Nat
  | 0=>0x76543210 | 1=>0x25613740 | 2=>0x45670123 | 3=>0x16520473 | 4=>0x43076215 | 5=>0x13025746 | 6=>0x70345126 | _=>0x20316475
def q2w : Nat->Nat
  | 0=>0x4600408a1100140010c06007841005000400020aa0003e0070160003c0220160e804400054000380070660bc3640400a0bc044330110c8014000c40080782f0090b80140001c0b00242b0050002a0070120002800701a098044000940500680008c0182281001e0800140007c0780680101d0700440106d0400581006506005804009058024010550500580701103012410002040044010090300e40d002008074040050000a00901e0100880100a
  | 1=>0xbc0481821500407814009000820070950008007f01a17c074260090980147b011004564180490085a4021610087643200e040744110020b8094001c40440782e17d0b86e4610120b86c4100121a8044000880006806701e17c02400194190078040210b8624610060000203217d004048001741700780c00a0b85a42f00e0b85840c00e0b85641000e0b85441400e0b81242e0390b80842e0090b84e4180061300842e0110b84a4490060000402b021
  | 2=>0xc60010a9008c44001fc004744003042fc074002fc040068002f4274068002ec01c1f4002e42e0068000d80d8194b5011008038042cd210038002c4210068002bc2b80686101d080024022ad010058a90092a0058a701100001015009008a4450016008a248c016008a04110162780249d0160500140226d01003802265260038850110085442e062230188320622480442e00a0ac1880223d0b80488d009230048002140bc188890110bc02887009
  | 3=>0x418024010aa0082a40240d1240782f036214024023fd1b0068023f50101f8023ed010068f90ba124024363d9008f640005012802408049008f246c0023001083606d0d8564561b1008ec4051b23a8024db016008e8401016008e64031b2008e440336e0b86789217d380024df0120b8018dd0090780480236d050018023650040382e042130108320420ac108920053480142b00a3400144c00a0402a41001d3302e8a7009020c94023250001e00231d
  | 4=>0xd94654400e0206c436005021424140020b86488f0214f8028043252a00293b00a4e8044a701d2a0108363252a02e85f3254d0028040490d80e43604917c0e45f0490486c45f4b54b00080017c0e8028004a401c1547b00a498028010490200e523039034018c000a0800291f00a06c0451d00a1580442600a1c00291900a0011800c01e2300291500a230044920a90c80d82c00a0d40290f00a001060024350000c00242d428078a70124200240403a
  | 5=>0x17d0d58400a020f64013d91240157a00a0617d8002900017e007065000190005ec01c1b40006c2480488901245c0480d0122600281400a0d88543601d0d9704000605b8048020494980496b0120040e4e90123680481023e350048ce0122146c41005254c048970121440486a0120c8048300120115c4000400c40442b0520102255700a0045855500a1500155300a0054255100a0105840c24a538028df0115300280123d2740285c0a91708540d032
  | 6=>0x170039c500e0783649d00e01c585c100e0081f5b100e350038ce00e2180383300e1040383500e0c00381100e0c47645606d6d00085c01d274009b10020345f4da00225c008780020c00095c0496a80e4000343d94241206d04856579006664049230120057495b0060c45f59f006010bf4160124d001892006340018d2006078029050060202a4070213dc018970060601e8840063680188c07a130018320061400182b0060057043100510c01408571
  | 7=>0x7140580027400204014021001c50023da124028005640a8f64490421240740306e7e805807159001f80071b1001640b80620017217e00e00805867016378058dc0166c4058da0167b0058df00933c058ce01625c058900162180588401621419478016788058500110c005970065778038010650d8c98a7052008c980231e29c029d704200008000628214c940074c1380740064c0019600065c008c4800684001cc00901d5d00380726d72003861011
  | 8=>0x4040680d01a0601fa0401a25c0686701a370069b101a0600688601a8f00684907a7f80684901a004b9a3701a000090df01a004068c601a6280698901a8c00680140d8b806a0100560c06a2b01a60c0762901a2e00141c01a7780694401a890068015d17140680c01a8800680c0c53680687801a360068cf01a868069830093380683001a0440682c01a104068003380115c80757100067000414015749f801656c059590164a4048083da004f684e016
  | 9=>0x18468000440183180621685c07a2d01e01d5c8074369ec05a7b00a29c0799f01e9e0078040952a007a75006184079d701e00c228070229c0078022fd9b80780209510c0181040e3680787801e25c07a6701e1840158301e070078b801e7780781601e51007a1a01e014bf97b01a7640683607e0d80685f01a01233804866040259f801a564068002100057086201a940069d701d70c068032fe7e806a0101a0200680207e00a2d80201a
  | _=>0
def qk : Nat->Nat->Nat
  | 8,0=>1343
  | 8,1=>349
  | 8,2=>6
  | 9,0=>602
  | 9,1=>378
  | 9,2=>41
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3y : Nat->Nat->Nat
  | 8,0=>992
  | 8,1=>227
  | 8,2=>2
  | 9,0=>488
  | 9,1=>283
  | 9,2=>35
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3x : Nat->Nat->Nat
  | 8,0=>1335
  | 8,1=>333
  | 8,2=>6
  | 9,0=>602
  | 9,1=>378
  | 9,2=>41
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3w : Nat->Nat->Nat->Nat
  | 8,0,0=>0x132ff0002eff000fbff00029ff00030ff00084ff00081ff00089ff00225bf0010aff000cdff00171ff00083ff00214bf00211bf00135ff002597f0016cff00237bf0021cbf0021abf0012afe00141ff00142ff0022bbf00190ff00018bf00191ff00003ff0019dff000feff00143ff00215bf00212bf00210bf00250bf00129fe0000aff0015dff00100ff0023abf0021ebf0019cff00144ff0006a7f0015eff0013eff00002ff00060ff0016eff0007fff0022cbf00055ff00009ff00011ff00065ff000c8ff0001b7f000b8bf00001ff000d5ff0002fff000d7ff00000ff
  | 8,0,1=>0x1d6ff00131ff000cbff00024ff00153ff00041ff000ceff00025ff0008aff00193ff000ccff0020fbf0010bff00026ff000efff001a2fe00181ff000f0ff000f0fb0017fff00203ff0017eff000f1ff001fbff00226bf0013aff0015aff00066ff0006cff000dcff00114ff00048ff00139ff00161ff0022abf00146ff00136ff00046ff000d0ff00194ff000caff0008cff00045ff000d1ff0008fff0010dff000dbff00149ff00105ff00228bf00160ff0019fff000daff00148ff00195ff00082ff00172ff000c9ff00027ff00088ff00069ff0008bff0004aff00028ff
  | 8,0,2=>0x84009bf8402fbf84011bf001c7ff00062ff001fcff001cbff00057ff001cdff001c9ff00004ff001c6ff0005fff001feff001f0ff00040ff001f2ff0006bff001caff00063ff000bdff0003aff001ffff0003dff001c8ff000beff00113ff0003eff0020ebf00109ff0003bff001d3ff000c1ff00159ff00064ff00044ff000f3ff000b2bf0005cff000c6ff00068ff00130ff00110ff00127fe0002bff00059ff0008eff0010cff000cfff0002cff0008dff00170ff00087ff00223bf0010fff0002dff000c2ff001a4fe0016aff0012fff000c3ff00138ff000c4ff001d4ff
  | 8,0,3=>0x380adf0780abf3500afd0600abf06c0a7f0500adf2e00abf1940aef0480adf62c09fd57c11ef08c6a7f62cd5fd1f86a7f57cd7ef1a8017f1a8097f1a82f7f1a8117f2d944bf1a8995f265b1d708612bf77c9fdf2642fdf26411df8ba12bf2649adf2d801bf2d809bf94612bf6f470f76f42ff76f411f76c42ff76c411f790612bf6c471f784801bf84809bf8482fbf84811bf25d44df1aa103f840999f841b1b72a8acb79ea10bf25c98df78c2fdf78c11df8ba10bf2b0adf72a801bf2a809bf3d210bf2b090f72b02ff72b011f76dc2ff76dc11f790610bf1b4bcfe84001bf
  | 8,0,4=>0xfc1b7f06d5d7f06c2f7f06d007f06e4e3f06e055f35065fd06cd47d35060fd19460ef0a87e7f3516efd06e2c3f19455ef9ac1b7f1953eef350fefd06c145f06cb83f06c657f06c656f3fc1b7f3515efd06c027f06c607f9681b7f06c7f7f06c125f06c557f35144fd03944df07944bf57c0aef06c6a7f06c097f1a8c87f1a8145f1a8b83f1a8657f06d5f6f1a80a7f26465df06e123f2640adf2e212bf26413df2e0999f2e1b1b7051b1d784865bf06c995f8480abf78c65df06e103f78c0adf2e210bf2e009bf1b46efe2e1e39f038acd7078acb784065bf06de35f8400abf
  | 8,0,5=>0x5002df038fedf910b8bf02cedfe078febf2e0149f2e04fb70504fd707802bf4ec60fe950b8bf02d29fe16129fe2e002bf4ec55fe8ecb8bf02c0cfe2e0129f02c55fe93c09bf93809bf350d5fd06cc87f1f81b7f8b009bf5b4d5fb078d5bf070b8bf13ce7f713c2ff713c60f70502fdf05060df0799cbf038d5df3e0b8bf02d28fe1342ff702c60fe2e02fbf2e060bf81c65df93c65bf35009fd8e8d5bf7a4d5df06cd57f06cfe7f07865bf03865df06c1e3f06c0e5f5b460fb06065bf4441b7f5b4fefb05065df2e065bf7ac65df19411ef7ac60df04865df35055fd06c183f
  | 8,0,6=>0x9ecb8bf038a5df0722ebf13495f713cd3f702d68fe13d21f705163df13c75f7050fedf4ed3cfe2e0febf940b8bf94009bf078149f0784fb79f8b8bf038e4df070f8bf02cecfe2e0f9bf25090f74ed5cfe96c0e5f7d04fd79184fb795c149f4ed4dfe9ccb83f03810df02d2efe9a01e3f94cb8bf02d2bfe03802df03860df2e055bf0604fb787cb8bf02c73fe03855df07860bf13ce8f707855bf0484fd7900b8bf05055df9f0b8bf13caff7050e2df9062ebf078f5bf70c90f737cd3f702d66fe978145f8604fb779c4fd7884149f02d20fe9c81e3f13d62f79a8b83f05016df
  | 8,0,7=>0x1a8125f1a8557f6b055fe2a80abf8e210bf1b40cfe840129f1b455fe6f455f777c0adf06212bf6c475f76c455f72d855bf2d80abf049b1d78fe12bf26416df26455df84055bf048acd786e10bf1b473fe25c55df25c0adf06001bf854febf790fedf1a8fe7f04811df1e401bf8b001bf06c017f0a9117f08c1b7f04802df048fedf91018bf01d1efe06002bf060febf8f401bf85409bf854c8bf9415dbf1e409bf8b018bf04813df04860df2e0c8bf2e15dbf4a409fe050e6df134def713ce0f713d17f71354ff705119df13460f7050e9df13455f78b0b8bf7ac11df13c55f7
  | 8,0,8=>0x7807fdf6d87ff78b011bf06c117f4fc11f777811df0487fdf14541f7048b0df14460f79ec18bf048a5df0862ebf14495f7144d3f71454bf714551f704919df06060bf01d2cfe06051b78b418bf94c18bf01d02fe048e6df90e2ebf060f7bf6f071f725071f701d65fe970125f061bbb792051b7880129f01d20fe9c8183f01d2efe9a0183f04816df95418bf01d2afe1612afe01c60fe8f818bf01c08fe060129f8ac11bf01d9dfe060d7bf90c18bf01d1dfe1442ff706055bf0f1117f14455f76b855fe7a8d7df4fc55f701c55fe04855df06144bf62c0afd4446a7f1a87f7f
  | 8,0,9=>0x7082ff770811f714c2ff714c11f790a26bf14c72f789801bf89809bf8982fbf89811bf16028fd28936df0aa5f7f08e5f7f14c2ef76cc28f76cc2ef714c82f79c07e7f27429df06c287f84428bf76828df6c828f769828fe55c28ef06c297f76829df84429bf55c29ef1e402bf1e460bf9f22cbf4fd40f77ac02df57c60ef6e460f76ac60fe8e460bf7a060df62c60fd2496ef72487ff70722cbf818a5df8ba2cbf7ace6df94a2cbf24893f72482ff74fc2ff790e2cbf4fcd3f78b02fbf7ac2fdf0aa5a7f24811f78002fdf8702fbf6fc2ff78dc11bf78011df6d811f78dc7fbf
  | 8,0,10=>0x3b811fb160cdfd6e0cdf70348cef9d47e7f01c8bfe004cdfd06c8b7f2e08bbf0508bdf13c8bf702c8bfe1948bef0488bdf36028fd05c28fd36428fd62028fd9d07e7f8ce26bf14c54f714c8bf727428df27488df27445df2748bdf14c28f720045ef77027df61828fd06c277f76827df84427bf55c27ef06028bf35828fd2fc28fd07828bf03828df13428f74ec28fe35028fd5b428fb1e028fd14428f760c28fd01c28fe2e028bf05028df13c28f702c28fe19428ef04828df11c28fd9e626bf288a3df2742fdf27411df8ba26bf2749edf2a001bf2a009bf94e26bf70870f7
  | 8,0,11=>0x62c27fd2a827bf77c27df2d827bf25c27df8d818bf14452f71a8277f26427df84027bf0488fdf1442ef777011df03827df07827bf35027fd78427df07888bf03888df35088fd06088bf3f1117f06c887f05088df2e088bf3f01b7f5c889fb78488df3f411fb78489df0bc89fb04888df22045ef03445ef08cfc7f03845df07845bf35045fd03845cf24445ef06045bf06c457f05045df2e045bf19445ef04845df0aa617f77045df06027bf79827df360cdfd2208cef22c89fb0608bbf9d1117f3508bfd0788bbf0388bdf4ec8bfe1348bf79b81b7f1448bf7654cdfd6e08bf7
  | 8,0,12=>0x350f0fb9e01b7f5b4f0fb06e0c7f350f0fd350f0f982c0a7f5580aef1a9557f2d8efbf2a8efbf078efbf06d557f3bcf0fb7ecf0fb808f0fb5f4f0fd5f4f0f93c045fb08cf0fb55809ef638f0fb5f42efd004f0fb3c009fb2e0efbf06cef7f160f0fb0bcf0fb5f411fd3c011fb060efbf92cb8bf1344ef7958b8bf4ec4bfe9bc1b7f81827df8b027bf27427df8bc18bf01c4bfe57c27ef84827bf78c27df8d0b8bf13c50f7858b8bf02c4cfe9941b7f19466ef06cd17f050d1df2e0d1bf194d1ef05029df2e029bf19429ef85009bf84409bf964097f1e427bf7ac27df19427ef
  | 8,0,13=>0x26c9cdf1bc2ff71bc11f7914b2bf1bc70f72c801bf2c809bf2c82fbf2c811bf26d10df0aa5d7f08e5d7f1bc2cf761c2cfd6d42bf76d42cf71bc8bf776411df01da4fe68da4fe061d4bf060c3bf9dd117f41c0afb1a9067f84106bf2d906bf848c2bf78cc2df060c2bf89906bf06106bf750c3fb41c11fb024c3fb06cc27f2e0c2bf050c2df2e106bf07906bf06d067f0bcc3fb048c2df9b66b7f2fc25fd92801bf07824bf35024fd2e024bf06c247f06024bf9b47e7f61425fd83c24bf83c25bf69409fe4eda2fe3bda2fe07a02bf038f0df038f0db079fbbf078f0bf078f0bb
  | 8,0,14=>0x497bdf0601abf0611abf060a6bf0483ddf061ffbf8c401bf8c402bf8383abf2e0eabf0517bdf03834df03924df07876bf2e11bbf07820bf07915bf07877bf06c637f05063df2e063bf19463ef06d597f06c647f06c2c7f06e0d7f9f4b8bf079ffbf9f41b7f9f46a7f2d9ffbf9f610bf934f0fb3c027fb5f028fd89827bf26c27df1bc2bf72a027bf28827df05027df2e027bf04827df8b02bbf6c02bf749927fe16127fe2c802bf49860fe0e65d7f60c2cfd88c2fbf1442bf701c2bfe06c2b7f2e02bbf0782bbf13c2bf702c2bfe3502bfd0602bbf26c2fdf26c11df8c8b2bf
  | 8,0,15=>0x6019bf0781fbf2c8b3bf2a0a9bf82cd17f1e47abf06022bf060b5bf04832df04978df2e01dbf2e0bbbf07822bf0787cbf05036df05175df03838df03923df06c407f06df97f1a86b7f2d8b7bf2a8abbf82c277f55827ef2c827bf2a08bbf8382fbf6d02ff71e4bdbf06dcf7f0497adf
  | 8,1,0=>0x2e1b1b7051b1d706c995f06e103f2e1e39f038acd7078acb706de35f1a8995f265b1d71aa103f840999f841b1b72a8acb7000b3bf000a9bf0007abf0006b7f000b7bf000abbf000637f0017adf0020ebf000eabf000b2bf00127fe0010c7f001897d00223bf001a4fe00180fd001ce7d001537f0020fbf001a2fe00181fd000f0fb00226bf0022abf00228bf000277f00225bf00214bf00211bf002597f000d17f00237bf0021cbf0021abf0012afe0022bbf00018bf00215bf00212bf00210bf00250bf00129fe0023abf0021ebf0006a7f0022cbf0001b7f000b8bf00000ff
  | 8,1,1=>0x9a0183f060129f0bcd7eb444183f1a8125f0f18b7d840129f0f0aa3f049b1d7444b63f444975f048acd708c793f08d5d6f00409f98209fdb7b0e2db078149f0784fb771090f396c0e5f7d04fd79184fb795c149f9ccb83f9a01e3f4440e5f0604fb70484fd74441e3f2b8d3f3978145f8604fb779c4fd7884149f9c81e3f9a8b83f2e0149f2e04fb70504fd72e0129f0f01e3f004d5f967009f906c1e3f06c0e5f0bc11eb06c183f670d5f906e4e3f06e055f06cd47d0bc60eb06e2c3f06c145f06cb83f06c656f06c125f06c477d1a8145f1a8b83f06d5f6f06e123f2e0999f
  | 8,1,2=>0x3e82b7b0182b7b9d0d87d5a811eb1f9ce7d309ce7d4cc287d1f8c27d08d536f078243f74409f954c246f034246f60409f9038f0db078f0bb350f0f908df86f3bdf86f08cef6f5f4f0f9818275f8b0273f274275f57c276f848273f78c275f1e4273f62c277d2a8273f77c275f2d8273f25c275f038275f078273f350277d078883f03845cf060273f360287d050d15f2e0d13f194d16f7ac275f194276f264275f840273f784275f798275f360cd7d770275f768275f844273f55c276f1f99a7d16141ed7b0a5db06051b770071f3970125f061bbb792051b7880129f9c8183f
  | 8,1,3=>0x108276f280277d0cc275f07c273f280637d064273f5cc275f2e4273f108636f5d8275f5e4275f558276f2c8273f1f8bd7d0381f9f1341fb74ec1fbe3501fbd5b41fbb08c1f3f050635f2e0633f194636f2a0273f898273f3c0277b7dc276f3bc246f288275f754277d26c275f68c2b7b1f9897d7bc11eb4302b7b
  | 8,2,0=>0x1897d001ce7d
  | 9,0,0=>0x1ffff000efff00024ff000c2ff0002bff000b2bf00110ff0002cff001d4ff000c3ff000cbff00025ff001fbff000f0ff000f0fb00045ff00088ff00028ff0008bff0004aff000d1ff00069ff0008fff00089ff000c9ff00195ff000cdff00172ff0008cff00226bf00136ff0002eff00082ff00029ff0016cff0016eff0022cbf00009ff00065ff0001b7f0007fff00141ff0019dff000d7ff00001ff000feff00190ff00003ff00100ff00191ff00011ff00002ff00055ff000c8ff0015dff0000aff0019cff000d5ff0002fff00060ff00144ff0006a7f00212bf00210bf
  | 9,0,1=>0x2e02fbf2e011bf0fc09ff54809ff0bc09ff18009ff06c65ff05065df2e065bf0fc65ff350d5ff08c65ff08c1b7f5b409ff35009fd1f865ff35011ff00465ff19409ff19460ff0bc65ff19411ff19411ef06c145f06cb83f06c657f06c656f0fc1b7f350d5fd1f81b7f19460ef06c017f06c097f06c2f7f06c117f06c0aff06c0a7f31c0aff0500adf2e00abf1940aff1940aef57c09ff1a8097f84809bf84009bf08c0aff0340aff1f80aff0180aff0040aff0240aff0bc0aff0440aff1a80aff1a80a7f2640adf8400abf00027ff000bdff0003dff0003aff001caff00063ff
  | 9,0,2=>0x8d00ff9ac02ff00c02ff3fd00ff3fcfeff2fcfeff0e4feff08d91ff00411ff08cfeff004feff644feff3f8c8ff5bcfeff9ac2fff160feff3fc01ff08c60ff0bc55ff00801ff00460ff0082fff0bcfeff9ac11ff2fc11ff00811ff3f811ff08c55ff06001bf00455ff3f809ff67001ff08cc8ff024c8ff57409ff17409ff3fc09ff24409ff00809ff5bc09ff06009bf15409ff18011ff2e0149f2e04fb70504fd7070b8bf0389fdf0502fdf05011df8b8b8bf050e2df07801bf07809bf3e0b8bf13490f71342ff713411f713c2ff713c11f7904b8bf13cd3f72e001bf2e009bf
  | 9,0,3=>0xa02eff20828ff0a029ff0bd6cff00c2fff16100ff3fc02ff3fc60ff1e060ff00860ff1f96eff4fc2ff716060ff0a860ff18460ff3e87fff7ac60df1f860ff0bc60ff3e811ff6782fff1f87fff0447fff63011ff60c11ff4f411ff0482fdf04811df8b818bf048a5df1442ff714411f790c18bf14471f70602fbf06011bf99811ff60811ff16011ff44455ff14455f71f855ff47011ff16055ff11c11ff15855ff358d7ff11c60ff0a855ff0a9117f64811ff15411ff4440aff1f40aff0480adf1540aff62c11ff1a8117f84011bf26411df6c411f72b011f700590ff00c01ff
  | 9,0,4=>0x3445ff03445ef1f845ff01845ff00445ff02445ff0bc45ff04445ff08c45ff32445ff1142eff01827ff65427ff33427ff5c827ff23027ff3608bff2208bff22c45ff1f88bff10c11ff08c8bff40c09ff1608bff36011ff6548bff22ccdff5c88bff22c8cff0a88bff9d07e7f7e811ff0048bff22c09ff0bc8bff22c11ff36028ff36028fd22028ff11428ff22c28ff12428ff1f827ff27427df20027ff09c2eff20827ff09c29ff05c28ff05c28fd08c28ff03428ff16028ff16028fd01428ff0a828ff01828ff00428ff02428ff0bc28ff04428ff1f828ff14c28f720028ff
  | 9,0,5=>0x3bc2fff3bc11ff3f827ff09c45ff03827df07827bf5b427ff35027fd22027ff24427ff3e827ff09c28ff06027bf47027ff5bc27ff22c27ff9ac27ff63c27ff17427ff65401ff0044aff09c4aff06c27ff06c277f1080aff05027df2e027bf19427ff19427ef34409ff34427ff02429ff3fc27ff5ac27ff00827ff18027ff5c82fff16069ff09c69ff44427ff2800aff04827df15427ff09c0aff23c11ff23c27ff0142eff03427ff22427ff08c88ff08cfc7f74809ff1f888ff16c11ff00488ff22009ff5c888ff22089ff0bc88ff22011ff22045ff22045ef08c27ff32427ff
  | 9,0,6=>0x2427ff0bc27ff04427ff9ac2bff5502bff2c82fbf1f910ff0a82cff1602bff0142bff0a82bff0182bff0042bff0242bff0bc2bff0442bff1bc2bf75602bff0ac2cff22c2bff93011ff61011ff060c2bf41855ff4180aff5a42fff5a411ff30828ff4182fff41811ff750c2ff308c3ff30801ff30809ff3082fff30811ff3fc24ff3f824ff08ccbff08c25ff08c24ff03424ff00424ff02424ff0bc24ff04424ff22024ff32c24ff09025ff83009ff55809ff55809ef078efbf55465ff06d557f5540aff55401ff55409ff3bc45ff7ecefff3bcf0ff3bcf0fb3bc01ff3bc09ff
  | 9,0,7=>0x10827ff28027ff28024ff55427ff2802bff41827ff3f045ff9d028ff0bc3aff7b82fff82860ff06019bf0443dff0f03dff93411ff08c3aff0e43aff72801ff824feff0781fbf02463ff06c63ff06c637f83409ff9f40aff3bc27ff09c24ff3f027ff10845ff7e827ff10828ff30827ff09c2bff9b827ff28028ff74827ff28045ff40c27ff16828ff00427ff
  | 9,1,0=>0xefff00024ff000c2ff0002bff000b2bf00110ff0002cff001d4ff000c3ff000cbff00025ff001fbff000f0ff000f0fb00045ff00088ff00028ff0008bff0004aff000d1ff00069ff0008fff00089ff000c9ff00195ff000cdff00172ff0008cff00226bf00136ff0002eff00082ff00029ff000d17f0016cff0016eff0022cbf00009ff00065ff0001b7f0007fff00141ff0019dff000d7ff00001ff000feff00190ff00003ff00100ff00191ff00011ff00002ff00055ff000c8ff0015dff0000aff0019cff000d5ff0002fff00060ff00144ff0006a7f00212bf00210bf
  | 9,1,1=>0x6009bf11c09fd2e0149f2e04fb70504fd7070b8bf0389fdf0502fdf05011df8b8b8bf050e2df07801bf07809bf3e0b8bf13490f71342ff713411f713c2ff713c11f7904b8bf13cd3f72e001bf08c1e3f2e009bf2e02fbf2e011bf05065df2e065bf08c1b7f35009fd19411ef06c145f06cb83f06c657f06c656f0fc1b7f350d5fd1f81b7f19460ef06c017f06c097f06c2f7f06c117f06c0a7f0500adf2e00abf1940aef1a8097f84809bf84009bf1a80a7f2640adf8400abf00027ff000277f000bdff00019bf0003dff0003aff001caff0001fbf00063ff000637f001ffff
  | 9,1,2=>0x16028fd1f8287f14c28f7174277f09c4a7f050275f2e0273f194277f194276f344097f344277f008277f180277f09c697f048275f154277f09c0a7f23c277f224277f220457f324277f654277f334277f5c8277f230277f3608b7f360287f360287d274275f200277f09c2e7f208277f09c297f00860fb4fc2ff77ac60df0bc60fb0bc60ef0bc60eb0482fdf04811df8b818bf048a5df1442ff714411f790c18bf14471f70602fbf06011bf14455f716055ef0a9117f5bc11ef0480adf11c0afd1a8117f84011bf26411df6c411f72b011f70e4fefb00460fb0bcfefb06001bf
  | 9,1,3=>0x182b7f0182b7b1f82b7f1bc2bf79b82b7f060c2bf1f8c27f1f8c27d30828fd034247f034246f3f0247f55809ef078efbf06d557f08cef7f08cef6f3bc45ef3bcf0fb3f8277f09c457f03827df07827bf35027fd038275f078273f5b4277f350277d220277f244277f3e8277f09c287f06027bf060273f470277f5bc277f22c277f9ac277f63c277f06c277f1080aef05027df2e027bf19427ef3fc277f5ac277f444277f2800afd04827df034277f08cfc7f74809fd22045ef08c277f03445ef08c457f018277f1f88b7f9d07e7f7e811ef36028fd1f8277f27427df05c28fd
  | 9,1,4=>0x108277f280277f28024fd554277f2802bfd418277f5d811df06019bf0341fbf0781fbf024637f06c637f3f0277f10845ef9b8277f28028fd7e8277f10828ef3bc277f09c247f40c277f16828fb748277f28045fd308277f09c2b7f2c82fbf
  | 9,2,0=>0x182b7b1f8c27d034246f08cef6f038275f078273f350277d060273f050275f2e0273f194276f048275f360287d274275f0bc60eb2e0149f2e04fb70504fd708c1e3f06c145f06cb83f06c656f000277f00019bf0001fbf000637f000b2bf000f0fb00226bf000d17f0022cbf0001b7f0006a7f00212bf00210bf
  | 10,0,0=>0x10827ff28027ff0a82bff5a411ff08c24ff55409ff08c27ff03427ff1f827ff01827ff00427ff02427ff0bc27ff04427ff22027ff09c45ff22c27ff09c28ff1f82fff0082fff16060ff1602fff0a87e7f1f811ff05c11ff16011ff01811ff0bc11ff04811df11c11ff0440aff08c01ff00801ff08cfeff0042fff00411ff08c09ff03409ff00409ff0bc09ff02411ff2e009bf19409ff06c097f0240aff00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,1,0=>0xbc27ff04427ff22027ff09c45ff22c27ff09c28ff004277f024277f0bc277f044277f220277f09c457f22c277f09c287f1f82fff0082fff16060ff1602fff0a87e7f1f811ff05c11ff16011ff01811ff0bc11ff0bc11ef0bc11eb04811df11c11ff0440aff08c01ff00801ff08cfeff0042fff00411ff08c09ff03409ff00409ff00409fd00409f90bc09ff02411ff2e009bf19409ff06c097f0240aff00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,1,1=>0x10827ff28027ff108277f108276f280277f280277d0a82bff5a411ff08c24ff55409ff08c27ff08c277f03427ff034277f1f827ff1f8277f01827ff018277f00427ff02427ff
  | 10,2,0=>0x108277f108276f280277f280277d08c277f034277f1f8277f018277f004277f024277f0bc277f044277f220277f09c457f22c277f09c287f0a87e7f0bc11ef0bc11eb04811df00409fd00409f92e009bf06c097f00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,3,0=>0x108276f280277d0bc11eb00409f900018bf000b8bf0001b7f00000ff
  | 11,0,0=>0x27ff0002fff00011ff00001ff00009ff
  | 11,1,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,2,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,3,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,4,0=>0x277f
  | _,_,_=>0
def q3v : Nat->Nat->Nat->Nat
  | 8,0,0=>0x6c65045bc1b2e0652f0fc1b195bc1b1955d6f06c01195bc1b0bc656f06c65181be3a350d5bd7a4d4357741b350d57d7ac651833c1b050095f06cb8024fc1b194096f0a87e195bc2a1f8d47d06c120457c1b0500a5f0504f02b5c1b2e00a3f2e01402a7cb813c0ab72e00b02af81b1940a6f0506502b3cb81940aaf1a8140297c6a2e00a3f1a865029bc6a050095f1a8b8024fc1b57c096f06c990297cb82640a9f051b102b5cb86c40ab72646502b3c6a264095f265b10275c1b848093f2e0990267cb86c409b7051b10275c1b264095f06e10028fe100500a9f8404f02adcb81b40abe8406502abc6a840093f840990267e106c409b778db70275c1b840093f2e1e30267cb86dc09b7051b70275c1b78c095f1a8990297c996c40ad71aa10028fe102640a9f841b102ade101b40abe
  | 8,0,1=>0x396d27f6c4f19411e7050650473cb8050659f2e04f196dcb802c65be08c1b0517c0e35009dd1356d243cc0b19411ee2e065046bcb835009bd050d4027741219411cf06e050257c1b938093f06cd4025f41b8b0093f06c120257c1b0504f570d41b0517c0b19528ee1f81b0517cb819460af06ce10517c1b13cd3770fc1b0517c0e350d5dd06ce50517c0e3509fdd06c4f0bddc1b13c11770a81b0517c0b19460ee06dec0517c1b050e25f06c140057c1b0502f5f06c140457c1b2e0141f06cb813cdc1b2e00b3e0701b2e0fc4f194e7e71f81b2e0fc1419460cf06e2e2e0fc14194e2cf0fc1b2e0fc1e350d5bd06cf82e0fc4d35090f506c0b0bdf81b02c117e0a81b2e0fc4f19460e706e412e0fc4f194d3e706cb8004fc1b2e02f3f06cb8044fc1b050655f06cb8194fcd45b4d5f9
  | 8,0,2=>0x384d0475cb82b84fb72e04f34edcb813c01b72e04f0bedcb813c11b72e01413e5e6c0504fd70784d242ddf50504fd70504f6bf5c1e13401b70784d026dc1437c4fd70393b27f781e1342fb70784d046dc143484fd70504f38b5c142b84fd70504f34f5c1413c01d70504f0bf5c1413c11d7070232e0fc1e050099f0784f026dc0e13c09d79884d241de3c13490b77884d2435c4d6a090f61358d243d44d56c90e70842a078fc2a1f81e3f0484d0475c1c0a8b83f0a87e2e0fc1213c11d713c2f34fce6413cd3778604f34edde713cd3d713da934fd84f628d3f513d6234f9c2108c1e3f2e0140267cb813c09b70504f0275c351f8145f0a87e0517c2a1f80e5f0dc7e0397cb8048119f06c0e0257c1b078093f06c18024fc2306c656f3516d027e41413c65d708c1b2e0fc1e35009bd
  | 8,0,3=>0xf07e0497c2a1f8477d1a8120297c6a048115f8401202a7c6a840113f840120467c6a264115f840990467c126c40ad71a9b1045de106c411b7265b10475c126c411d78405102adc6a1b4117e2a8ac046dddf2b011d76c46d047d8122b011d708423060fc0b65809fc7d04f0275e4613c09b795c140267e732e0093f2e199026f41813c09b70484f0275e5e050095f8604f026dde713c09d7884140267c4f62809f59a8b8024fcb8048099f960b80527c4f02da0f60780e0067c1e038099f3e0b80527c4d4ec90f62e0e50527c1e0389f9f13c0b0bfd84f02c11f62e0e10527c4f02cd3f62e1ec0527cb8050e29f2e0140067cb80502f9f2e0140467e472e04fb70500b68778b83484fb70500b38b780e13401d70384d0275cf82e04fb70384d2435cb837c4fb70384d27f5c0e1342fd7
  | 8,0,4=>0x38ef1173c0e3bcf0db078ef3c2ec1b558096f06d550517c1b2e1553f06d55195bcef350f0f93bd7d3c3e40e13427d708c0e09f3c1e038279f0784d09edc1e4ec27be078d409ef40e35027dd134d409fd53b35027fc3516d09fe41b050275f0504f09f5c1b2e0273f2e01409e7cb813c27b72e00b09ef81b194276f0506509f3cb819427af038271173c0e03445cf0780d116bcd403445ed0a87e361f45336028f5060170a2f4580bc28ed14c170a3d4d214c28f514c580a3d41c0aa2c3f4fc2f34fcc2a06e2c3f0a87e66df42a1fa065f0a87e8b0fe5c048115f7b4120475c1276011d7880120467e0404811cf049970473c210a8183f0a87e060fc1214411d798c511c5de1714471b7774511c75c5169c71f61458a1c7d45156c71e70a87e0497c311f8125f060120467c3c1f8477d
  | 8,0,5=>0x1e0381f9f0784d07edc1e4ec1fbe078d407ef41e5b41fbb06c1418d7c1b2e0633f06c6518dbc2a1f89b5f9d87e26d7c2a1f9877d9d07e26d7e741f8d87d4cc170a1f4233f0886f82d56025bdf6034456f034f0117ac1455809cf2e156026bcb8554149f2e15513edd550504fd7
  | 8,1,0=>0x38d409d744d35027754ecd409df0d45b427791609109db40e09c454f0504f09d5c4f00427752e01409c7cb813c27372e00b09cf8b8004273d0506509d3cb8194272f004d1025e42f180276b14cd80a1d5eb0bc60cb0093d047a4120bc11cb1442f0478c180bc11ab1445815794581540ae91a82f045ae100bc11ab2642f0472db10bc11e32b02f0478c0217409e906001026e45815409e908c1e0387c230780e0f08c1e4ecf8b80504f9708c1e134dc230784d270502f0472c1e00409b91342f0478c4f004d3f12e001026e4230782f2f2e02f046ac230796d2f06c1413d5c1b13c017506c140057423038d44d06cb80507c1b2e04f3706cb802cf81b2e0013d08cd45b5b41b2e0652f06c01195b41b004656906c01025e41b0bc116b0046502ba46a004097984801026e61000409b9
  | 8,1,1=>0x2800d091b5550042779280060ade506160276d5d82f0472c230341f2f0040918de41e108272f108d409db418280273d0604209cbcb8108272f108f009dac42360286d8984209cbca014427752e0a009cf414280275d2804f09dd4a013427752806509db4a014c2775048a009d749b280275d168d80a1e49d280275d2c82f046ac070182b7a1bc060adcc7e060c23d0780d090bcd4034246d00556027a423078ef2f08cef351b4233bcf06b08c0e09d3c0e13427570780e09c7c1e13427370793b09cf81e350273d
  | 8,2,0=>0x8c1e0383c230784d2708c0e351341b0046569
  | 9,0,0=>0x48580477c1201811df7b0120477c1229411df0482f0477c3c1f8117f048470477c120440adf1a811029fe100440abf2641102b7db10440af71b41102bf82a1f8017f08c2a1f9fc1200411df0a87e025fc7e16009fd048090477c1c2e009bf0380d27f7c140bc09df050090477e2e2e009bf050e20277c232e009bf2e00d026fcf82e009bf1340d243dc0b0bc09fe02c09047f84f0bc09f713c09047de412e009bf13cd3027dcb800409bf2e02f026fcb802411bf2e0140267cb813c09b70504f0275c2306c097f06c0d025fc6502411ef050650277cb819409bf0fc1b025fc1b548097f1f81b025fc6518009ef06c01025fc1b0bc097f06c09045fc1b050095f06cb8024fc1b194097f06c65025bc1b0240a7f0500902b7cb80240abf1940902bbc6a0240a7f2640902b7e100240abf
  | 9,0,1=>0x49760477c1e0341fbf06c0918dfc2a1f82b7f0a86f0afde6e0a82b7f308170a3f56904811df08cfc091fd5555809ef3bc0d117bcb855409bf06d55025fc2303427ef0380d09f7c1e03427bf3500d09ff42a1f8277f0a80609fec0701827fe06c0909dfc1402427df2e00909efc6502427ef1602f09fbc7e16027fd0481109f7c2322027ef03427117bc8809c45ef1f8d809ff41709c28fd160270a3f4d809c28fd14c270a3ddeb16060df16065183bc2a1f81b7f3fc2a1f9fc7e16060fd9ac2a1f9fc580bc60ef0a87e0bdfc2a1f8587d0a87e045fc580bc11ef1f8120477c1805c11bf804120477c5101471f7
  | 9,1,0=>0xa8060aded690bc11eb08c0d091bd5500409f908c0d09dbc0e034275f0780d09cfcd4034277d0a80609dec07018277e0040909fe47e160277d0bc1109fac23220276f03427115bc7e360277d05c270a1f401024277d0040909de414024275f2e00909cfc65024276f1602f09dbc2f044277b0bc1109dbc2f044276b0481109d7c8809c456f160270a1f4d809c287d14c270a1dc580bc60eb0a87e161f4580bc11eb0a806045ec7e0bc11eb1f817045f4020bc11eb0bd3d047ac120bc11cf0482f0472c470bc11eb0bc1102bac010bc11eb08c01027e423034096f00801027e40117409f90042f027e40102411f90bc09047ac1400409dd2e001026f4b800409b92e0140267cb813c09b70504f0275c0119409f906c01025f41b004097906c140257c1b2e0093f06c65025bc010240af9
  | 9,1,1=>0x42280276f108a009df442280276d08c4209dbc42034276f1f8a009df45a018277b1082f09dbc42044276f1088809dbc4209c456f1080109dbc42024276f3bc4209dbc4209c246f1088b09dbc4209c286f2805809df45a044277b2800109df4a0024277d280d809df4a009c287d2802f09df4a0044277d308a009df45a09c2b7b2808809df4a009c457d2808b09df45a09c287b
  | 9,2,0=>0x108a009db40102427790bc1109dac120bc11cb2e001026e41b0040979
  | _,_,_=>0
def q3u : Nat->Nat->Nat
  | 8,0=>0xa87e1602f6d0a87e1602f692e01413c099706c1413c095706cb8050091f06cb813c093706cb802c093e06cb8194092f
  | 8,1=>0x1684228027691080102427692802f04427690500102427592e00102427390046502427690482f044274b0a87e1602f691f8170bc116908c0103409692e01400409992e04f00409b10504f00409d106c14004095906cb8004093906c011940969
  | _,_=>0
def s7 : Nat->Nat->Nat->Nat
  | 8,0,0=>0x37a08b15bc88e1a3ed3bd492da7c6f9001a026dd7196559271fd10eb27250275dc48d1a12d98965b4b2c3cb541e0d65b1ba3fdb2527b4e79589c4693a0c7817f5cf991ef17e422ddfff33fa27d4c2a21901d17115dd07cf82454a242269d193c4af670e820116700e859e5e4129b076924324c58b8dcc84900be7a2916d99fad2436d059697ee64a45da57de3be5dec3abde0b5dda3d977658cf672cf6169fd57f3ead3f84179f3b55e421766a1f2f1ecc714967509b6e264091f9d0dc2a461685b84ba9020dc417a7124979ea5e13214a5203ed2a143e8474586cb3b459129a
  | 8,0,1=>0x1ea6fc84bd41408fa5b10e2950972891c93a527fc2865781656d3955db19b024861db1f4d9a40dd1d1b854600f498520c49be4c745fd0b76b19c1d7f9c9ab0859bd4428692c2c8de349c49a6b279d8e7a2c877795840e1534618999d2708644635223264c958bcceb7bc4a4e8de564c8cdd33971fa585a1b26d93d666f77ec4a4ba3c023f8fc4e6f5be56e921247422ef0b97812636b9045d6387fcb0f19504de5604ee483a41245cfc1a1a09c9a69420ff93b9d4e9154d46f6b20d133ed182b1070c5971a47596f74d51630543b8b0950b5f984bf16249f288929a461a405a
  | 8,0,2=>0x644c000a26983f2831ed96c8c4b3345e3210dca4414ec1f456d29784575400008a4000843df5ba0457d3063e2f73cd515a203608b00aa33b5b9dd91815e8894010d3043541e93b45b390000fb15d1e9e502f40000da620f01298732dfcdf206c60512e3a79d2428eab000104e000244f3d08df9100901a0c45dbd77ee31109d4a216001601685282fa6d0aec51dcabea5054c99a64e3094856f120a03d96a64cec1412302144c955a79c291a2040013344a6966c938999a501b236417169e61b100008eb0ec5b1d443e9b14d4452100008631ff27098304b436d3a139744484f
  | 8,0,3=>0x864dbe18b21bb722b621138d16d423a61bf96e65ca29ce2d903089d60002079331464053058b952bc00000029399195113092856a005400022ac623967cb6301cc23915680007fc5c723c28ee00b260b19232287a0240008d7d2fd39a60f50000000039445c4715d51016c4fc6e05f8168a09b168fcb45a6f668f3b854ec2dbd3d9600dc59413ce772e4682190f01c4085220777329b2877c18400001199765ad91d240b3000055c54bdc1021adaa90224000a3e272087a4d9786050750002135000000061259a27a220846dc4f016b3891966d82117584851010d6af6d64937
  | 8,0,4=>0x1b0da3d1c716f569c1086698114bdd491aed5633ac8d91917dc0100015e003480006bc648936966611c4a05901344761be81c71845d2985354379b046500002497427e6b15d062c46b46909a0a4e3fa19e0557c3dcb778e52ae07645ba53e5a2496d95d9778253b3205929a1fe8b98d290ae07440e90ad5a0139363393faa98791d4061343078b9a04281a78422b5e2664226b21298e45ba623cd570738537960e58c925dc00000000a92b7e7ac715549184643a558e451d1cec0000925bfb6b6d0f70171b2e3d30eeb2f822f982180000001b9a5e1df6100000760fadaaa
  | 8,0,5=>0x4c1980b51e49dc04464840625f21505a2598d6c4014774d3214653e517480517f846aa2080d1e028536723e45e002098c36afc6257f0c00072fe439348c00044b0ea73eea6016544000a20250040e5f3551c55390b059371c5a6a98704e714b9654b6475af967f06615784b71876400064658143bc9fb527286cb090402d4ea50018cc58610001df1384dc0a7330000000126d57e624359bd9b962dc3f98bc4d7958c48fb29813703ccd0bf19ad2098fb53ed6725eb8a064287809d5c97748011945454c4ea210900b04071f040005b25a6ca1ddae92d95f8f857e87909a4000
  | 8,0,6=>0x975479813108377a8a0217de40006cd9aef5a297b985fc000911d9593bdc5f15edda84829c07906bc12100602892c784784c9e47c5ae4490a2a58414f361c920fe4c1866d4d9a4c510547d22a51e25cb100000008f7179f608476f5c852c52844b6915840002f7296a8e129f44af5df45e9c2daa14c0f3555e3636771753557c9f90a653c13b187ee8505c7c260c0000001bad48c96b196e0aa3828cd816d50a015d84ee99094ea558b19096cfc92d8444f21230c5540bc4f7704549aa2cd02a1a404dc18d580006fd4000812d5a99c8425f1069a497d456d17fa4b2a7069541
  | 8,0,7=>0x80fe4190aad3b979087ae17a53ae560c83da07c131048a57b038a8af1e51c45244a2cb2a058570f103290000b32713d90d0001ee9000154988bce7f271472978d8f1200000ef74b40490040000575caf89ebc00088528d76d440003e9cd95000258ba670ab800ac1ce6f04000098590325327312a34a9d1688b8c8024cd91e4662e67ce1b3696dde15b2daa42e056cf6ea902103d5cd52175db40e65b2a9928000a57d0370001f29308dcdf00014b1571e3a1648414501f867a22a63cb0000000216c080768d99b30786d99005a7333e655b095d2e92d64231311c000577da20
  | 8,0,8=>0x64cda10262d8ec07c66649440dbea344ef104a40343c307ac637949f8644f03170c6341b948395b5e7e7044e33f954614576309975070c4b53c634118e03417cf57bb88dc0006c0a7b9a6640008344ca92838d89a1e0b7b7884ba76e944e836fe1799268a131bd8b7c6605ab40cedf5762769722c464825efde4c2c7d0480cc593103453d5048e231932d16b6d1db0619b50cc946915624b846880a60f77f044557f152111cce174a02144278646996ee64b15946081631c212908e14f2705c3d0d0c8b39ba5cb916c63a993857ec2b3c17b21d4ebba21068c93f25790088a27
  | 8,0,9=>0x6784be9030549997c4199a70d2236d3c20886a53917f646c302108110070d590351bcd2c249d441ee92773686ed6d9db913a243c3a104ce873398a38ca4c89158d4a956c5331a004aaa28a61833df63e61ad5d672a89abd62961572214af401b62df026630801de36098846b96f81a717965a295bae4331b05a112ce62d173a450991464691fc60cb9bc45ff0f057da273a52a90a64a98d506911015f7f20ac7b47e9c87d54c68ab8b3e35846dc0090bac79201c47f9a735bf88c2e4ba32f0351127e7547e65d9b7739b996d70f69652d6a7326e00305a585f5b8da9638243b9
  | 8,0,10=>0x71fe86a00000009d760f3110400000005cd65c52cd946539a00014b91078e212d2dad32bc896f3415e92000197b3bda3f9a250344085545700028690001c76a4c030925cd451299a46733c03918a268d9280d7c20ac669196ec0698f45b129d0436b4bbe5693becea93560000691c09c91bc01971955c161443e1244000037540d336d60c934440a320057c160c60d700022c00001bb83a8164183e513ba6fc0425910d935de55118665469a58655920ec0319de249032d87d41a5d1f167049cd23c5c5d6d6dd3387d661780e4d7c77a67ea46346b17f7d0ad31ce0f1a5e46e9
  | 8,0,11=>0x27cd0cf6a2649547656179445f873ad271aa3b04aaa4860418dc5c289219e7800004d0645e9a19ae5c8431903495fa84371eb4a511c698ab222caa1686dd31333a92f67ea50aa644ea336701080000c2f48f1222042680710247fb5a38e99a40e249316a9f11ffd81b00c87089ce593430e44045ff285740346a1658a3b19fbc7091f5cff15384eda90c475127323045d5a80c000005e14e5c2219624b987f62e165e5a59774e23b6165f6977e9dc60a700a22d1c429a78dcf759a56a149089ba512658168327191e5c000553d691078a27931a697730c40001065a8b006d9d4
  | 8,0,12=>0x91253fa0149547228685964adca550a4fd75284aea54fe6e14304091623e8638f25149650c3f12645893040529110515a15afca6e00bd75a3e4886100001df52244db77927139a868122e5a7e16861ab155c55e9a6e40c91f38c550c843e98d656619ea047214c5c856a307f62dcc951368592591f8f5633d22290000af08f3c15f382cebca0edfad2fecbbe66b00440001459212e96738ba6f871adcfb58697390e842e08064000569e0cf2ed87711b14af9a288000201c000a03d1c77d2d70190b4a441c0005f8ee408150cd99399f1e018ac471ca27a7f107d800010e4000
  | 8,0,13=>0x9270fe46e4878d04a876c99500007b30000a2444615d9880b2ac84c036c40007a2c40627bc38769a071e97b68e127004d582d497c6d4ce1c6bd153757ee923003da2e120632b6fc289f58908e37d9e7494c7c7d109f083a6a349b3a14496115289b90825c4987ae8f38565af51a9def929da29d9d6c0003a7677f2d25131219e1e1229c7e194959a665715af75a44af89fc00069f4630000193b3b0cef33cf95e40784f298da4a9521a697b92464e912761f1215dc996955dc40de54979d91f892ee578f27a664082216d8986cf25841045048651f9635c8df25a52d536204e9
  | 8,0,14=>0x1deda62a231e2e139dc6a2ffc10c287e4be961e86107d1d5b56e421f21cd48f228d60972a49fb48a9eba46619b428edf11564620900011e17dc400001c84c20d8c0f90c640411e8603732984993e38ad40001b793a5475f7d0cec429f815e070657359de28f107514e4bc47e474a0426a6edfbb337902d8525788198010a519c9144d061bd72065ff266c9719f64fee9184dfb96a40398aa484d08dc59221bcc11650650242bc0ff529c000154a7d154a4ab09d4506119cc0007f250e68a467005484a646821f018334fc7448653200a54818a068c900025a2982483c827c1a9
  | 8,0,15=>0x8f69498c3d5773e3e25b10f659711e5acd0000fbe2f0e7908e64c517aa58470030ca45e465e34a2e1c3712860153fe26973c4d4741f930e2740000508c5e5574563ca4a5c1288e65a48ba596f653d06b6591687152093f21960d305d433d5964daf69ee24b1eec7798a840000291bc52a640005aa4000000282b4f2624100024a27e44e876f30bc096ac4a77c25a3774043c970119926e8528132fd25d8e247627ea40c436c81f77fbccef494e0171f651e959fe6d179a400046e51740800e4676aa4534ec57291ab8240323e0ff816e9aa12440001fa67c503f5e54416e911
  | 8,0,16=>0x8744f9f0000e5b9ca60673f24bc9000199178f28a11c8d9837491c359c04c9929d09398a65db901fc000541d73327ae1b980c52ac4fca0891524ac18c697097b080215d919042b25bbd68aa636a0e4ecf4d7d71d3c55d530faa14b968695887ee5206fc4da4958d280a5ce96b248c6f85a64f1967b022c301c6d52785a09255c90245b810b2d50a877f44a378314e1e40b938170a423c3e592781d9925194e464c0e248b96810f3f037dee44665f77537ce6d5000a7935a4e818f54dcf0164c95757d1a206542e7160a1217e85f3387e5ae30881009a5810548f90a7c8265319
  | 8,0,17=>0x89cce750a89827a05e2fc40505a9224d59f00010859d695513a68f5c78c5b6f12b8cb84ed48f4518616115c87ef18b03077c646071cc68e9301298f55a5ce5a08c06358d0d724e4a9a967c5c316a515f126d65995b05bd19e6c1411efdd0a6fe8a3f3b8ccd2916400000000b73c453028b7502f93d4d4b33a9ba224b20d99708e0748063e5a47c14979919992a248061e8cb5f4dc52dd94fce6b741ded40000000448056c5ec42246fa5cf55d641629e1c9083dbcbf96a6c8416a0626164b1349687079c74fd3018f340008284d3a1ce4ddd4045409088e54107e156f8806255
  | 8,0,18=>0x30357cf1b36765003a8db31f4b9f46da9925dba83161fd71c6b84ad8396262386ae509064d4b791e9517a725c973f846e19375797a73c799081cea14c44bba4744f1d2ae414d52fe7e91f9a6f971d69d315e9881000151fa3e4342205e011748a7c984c407d403e571419dd0e7e8e0690dc57a928c69895a242321fdc20a9fe49de00017f485e013b4f15c1876040aa4c85eda46a58094fa6471092d14c3f647a2756558f479dc8f0a8e4fa5b7c6c9420d7a17346169151e0b924a4adc359c47174e6077845c88970b4ec18c24b011fb60e12a141bd6cc424c11de29b6936847
  | 8,0,19=>0xa114bb83ae20d52624eb6a7642dc714514633129ae26a676f626e9a64ca59358fb02a90f45b7a63e83a993b6477a1240b92bfe899055c8ec941000d6284ae175e54c7a7a67a4091d81708128714e76619936558707182f92fe09f10da81a619060a96a8843a00cc95907ce70a7c7d5012fc9a23183cff722654e789add2b17e4e67736e2c9886c61d4ada2b92cc04f1461829a2090e739b2671b2205ff988a0f813ab42b93806797235d27660b5e12a2c58f72505cc293544b08184bd11a0558964e4b41539a7b34244de95d2556c133c871a4644b88b4d3e1247e804593a4cd
  | 8,0,20=>0x3b64a6357a2591a0ce7ff21e58d25665a5193468c440383e2594e54574663e267aa2b781c665c5609a8f6585d418f04f66a37d9942c5d5dc1ee42d17e7c012869602f3d1da8382f49f450fd4081f251aa0dcc2212fd0a396f265894d656f444658016fb524720713af339e4cf2410fc1
  | 8,1,0=>0x9546894dc681023ad972543900051c58b6b46a253307ea610cba030009528b992e2096a46d13e90b53928ef4679ef6419bf81f045721a4f2992b948fac10614e783934a85f1eb3a497a8f14cf3c99798c14890918c32934d72c905b6c19a75c954f0006699690d354900041d2474274e1804a410009890ab0923a1048a2f3910b952b5fd6b97fd1f50d928a5aa1108df7d00002dd7ec0124e99495b70003215f149b9998898ab9d00426237f29019399747c99590597f930d5594a92964a3779
  | 8,1,1=>0x9c1739a7700a36147fa8100096079000098d0003fd7038c902f52d2139b95b91289211b94495240009d84e8389819a58696129a799dc1ef20d3f1a7f6d96aa9f90009099f0829441acb4de3ae352a5c8d1445a996386301b194b73171136900caa9461663723a6345903f289a2b4128b38fc4f79914711cc4bf8516016e17299719149f532295e6e94438318412336f197727c50c20320b031ad1ab469929c4e4a5aa697d411d82c9436b61fd00060d4b79818d95712a2a50a0f371812253
  | 8,1,2=>0x39c33e8bc7e0a596a9a0999586196c0db8499d932e19991c27907fa237b99616ec9cc0f14fa3822bb9479a11a140608264943b3e36435318d39084934d18cd751a3100b3d476455791921fa217da2ef7739314c76186395d175f8794a12740552f164d0a76224fe9d100055261f0006cb65175d7b01f13eda520ef8813b60241d4871a0b5205c148151400095a22105d05375b6dc95c6f97419731bf0131644b154374944d3af0001377e18f90000a11842a139a0d528da0d4d94773488fa65e
  | 8,1,3=>0x1e1011581823a4977127658c5e924ba1179d9c7a4d19f22999f6e2a835f996b3d93793161c32619ff24f66f9340217018e92397102a97d157c9329cf16c0001898f62e692aa2d69186779f6d3a13561acf1d009b1e90000000000003b9ac986a92f9107ff3816714c16799639b07532ac7595d97835f07f625f7c17a142971f6f41af2596774d340f0ad33570989138a6c978c6a10f97b124936801b71935f70dab901906b13d14408988726e79190705f62c876a7b00f7bc3090931a983477f
  | 8,1,4=>0xa914975842317dc45f2c378a7810779e14510008cf7ea04f50a6ca69e25ba0114937b90f1d842d6bc8666f72b47f4000a3c77d00062768226c9d75357de694001000000632821a64a292d11514990141013c45e15b197521991128300054768c5a1227159ae16b1a3989f04131b8af7ac46f8b7814201a19655504450abb02b14d8993074f117c26500da897fb1f92411175995881db062ac78e029e2f94ef8a149179932f8b152765c0e464f9240351e73e6a512949b15900c58699f36611c5
  | 8,1,5=>0x941a201710001943703199c82814b90f54329e469a5060498e180a000aa1929000a715916195690da7d993a8a976900953bab1
  | 8,2,0=>0x247118a0000a81690
  | 9,0,0=>0x686077ce767d93cabf5d9c23f9714be5e1a6ad748b8e05fd4cd96193f7db4ae574b78f8c000e3a433c30427e0000000f0df329ef06880a5e6290c000351d6a285102fa8e617723f728903520a26b8bd2345ab27720488000b22ffb2a2afdca0459028b88a63f88315ce42461c304f738c645a43019712462d4d60e97f89dc544f02529fb4f93e44380c19dd816a95079cafb4cda2e1171c77cbd21fa5c980021a32211ccaea5bb2f798384a451f2eb202201c21f2c9514640c5b7e429598a0065926669040c0c96e0c30b49be4353198
  | 9,0,1=>0x46b8dc529895b2a1cac974e10164dc764512b4b7dac7a5102f8958da11dbef06a300c925fb2f01611a106372f91518800134e9b9540bf44c5275100013e6426f4789cb10cd026ab2413104df81c11b48d5ce6e110444931015a52d20c99ca4d6bf9234c549aa83bf1f4902648627f5290e859622491c90d1d4c87061e3800000109a2d500c8e4465f25e324ccfd1466b89ec64b4c8b78425dca1308128582663349215678001c289fc115866e2e2e30941b5c8d1cc2b6d0a73e544ae151b897ccc2afe23cc086301207200a624252493
  | 9,0,2=>0x811b609552bd4734a5c59026311b989e192ebc95178e6d38266c3639cd0d42de21420945ce65197f645b0dd485922c3178b183d15d6b0297325957072ee58f65144538b3c672fc15ed23de19529a2acb58a0deb4965525856d8e110a3b30cb171476bc95bd9128df2721664682f2260494eceb4af85ac80005168a914eae1dbb430d1dc9511fe69792be0ea8a691d764e058470622c205b8b04fce590abc60625814967d9ac462b0b34a08000aaf27544ba6c54fef6f1111da519ea79563b12e402ad992a3ef51b270406480e9b8519f
  | 9,0,3=>0x7f0b3895644b17b5c1cc8bc8197b89bd4da83916a317697fe8e189095a60e325f185c9851fec94005c185ba031c7f4b4a8ef205e514b18d7d2e5b1648644d22c5a5feaeda3e21411ef9499a3e3291e49ba5933045600b171822def07cc87c98a7a74f880c05562378be3ba44ea837710c5306c20f143dc988a8242d028b04d996669945adc55d2abf679a8840b8fb31c59a7c0d43930b7ae045d26e1668a17d9826a694d8000b58000580c624c928578fcb629ca6189730a7e9ed307530cc7864e23c143987c4b0abcc090b771a0910c
  | 9,0,4=>0x8a4801dc8217425dc3a6022000629abe8000f2438cb805b12f492df3ce06ceebc51fc82e3280000d8b2843432292b0a1ea2c246338982ae253131188a43c868d5195c9e440009578d8b34cb42bc171909c5e829310e130a50e27052a8a7d20a29193cc0ec5252edc5613e4ddb05113eb45a542273c3010b2df72b2f684ac24e2045371b23a41731192949d04b0c999927cadd3222d92289931d98d3269207a4fe238c434c1ed762db19398d7ddf12574f0b2a47ae9a117b80686f46bf7140951be30390dc809c2dcde12c0b9ac892107
  | 9,0,5=>0x11511686a2000674bbf00005e27949e159b62140004811e9e13167a2a44440d8c74dad85f1f2818c281c40000597d091c41125d1271c5d45364ea304b6640008c71c4b871b3ad841408000d5a58a928afd081e9f96b48001e132238a8ac45722a693b095c4db2b7275481e87e29e7120ae318d312421e09584726772de30e84eedd56012c852252596a51e5813419368c3c68f3206974499d817b1c72d4b64439e1397cfa0e604f0492dc8d25a021ab6ca97e8a924da5f7bc5ddc245c7a88f661124e1210a6049e223168a8a5e002457
  | 9,0,6=>0x71f25a4e38679335b45856303d4d480024720002c6af5d7129b78369ee50de127180c60d8368611c509da39e5162242f862b2bc85cf878501266a5e84664f8c00057892a55feaa10004590f2edb7918800000127c1ac9ca89425ab4881f3de2af190368001432000457c68553228300038dc3a02d10de0be620220391c3c61c7200083741b067e20a86cb6482320007d4a9585e313c8301dbd93e081010accc00051b7f5b5855f23096988e8d4be499804b27535e0006388d0cd5215900000013d270d11f836e19600067889e4d6c899
  | 9,0,7=>0x4e48755ec307733203482f71c9500b368e92a591908a857887f93b295ee2088c973c89857be9d1664c4d12a218b00034520ae00059dc1ad12200000015e98c0b415fe422d5ce37e34397c5b7282f384194400000035f1be0368dcf2bb42c8af2e44908976527284f7e4a82484a2917908000a42b79269bf6e4811c10bc49e814c27c26d9fa64980018169885b530ac22b391e26a7e2177c3106f9250725bb110f26e220aa04658870f2a6af1c1832777c0a2c54e2f67749ab0138e2578bfa305972bcf4889470e840e626c972531e755
  | 9,0,8=>0x47894b0572c5190cafc5892c796f4b0859644550bc957c00047b30a2085e5600d43914f0c8e7da6418e1e15253118b8d3da407b755981259f22c76fc800151e394000387dc7e7e159bc3c62de60a85080010ef24169f80aa512dc104a2574996d9a5209180b98ab1160ca85f4f26913db065f76d1d5f996259224b9630b6409d25c10bba81d5790935578604d92d5c5b4915050473122936f4a6efbf49fc5ed093109239c6a4b6267f61c9e24b28a730ccb93c346bd1913af6402202d59c8455fce3317524744000f0b58c98f02d5069
  | 9,0,9=>0x6b5383d6532b15fa81840000000b89c499f8b434a3b926222c6b0209a9d6f672922036049ace5570ccaa4a989d9796398e2f08b9726c2e646ae8355cb8258e6cea6f289a54931797acc59de40ba19048c4e22865e0001d910fe7c10003eac4b80003d741057f6259244932505322b
  | 9,1,0=>0x7048287384db307b4bbc35598493580f4d18698393c12d517249c1419a4403a193bb4c96995874629a739b617bc92cb021625539ba9a5769a7da79b831a049dd7fd5c92af4ef66b44902a6ca94990783406db3197268832f8ef32bb99a913578993417925a17a32e1b717ef761529bc87c19191795ff2b9ac181730385c81c314ad99f998131125493d63fb2768f6f16416b70e6619779749ab1721044771bc45d100045195c4b10008948795419cc96a86649d35d92d429ae4032784071000
  | 9,1,1=>0xac90001a11c96e4b2fa3905cb69aa90015978d174840d99139e1714a5b01041789b3fbbbb39b2c2897289c40003ca5273390006f785737c1830001d858a0002139a1b8f3f900014f39f83bab90692597bc3a60001910004597e13917394673887cb0b581953145d90ba9995b27bbc19dbba1b4b000000a5f73ab3727d8a19b95518c3a1c62ca416d125f2d36912e94df8f72dc4d566404934c55f03a0bd6d39133a058b07a959b8d0f1b51051a712a960fb552387d22398b87946eb409b610d2
  | 9,1,2=>0x2995f17b36879997d969f7410004f99ef8ada7f0e91805e49290009c54d94e16f47980006b900072fa8918b3134cb649ad50001b39d1000ae19051014a85095d30d18ba11d7094aa82e8af7a1b0973072439d5cf7527b136136910f301a43a74a313e95f97f18d05bb84b62f76748d2b17270118417371ab5c10f92c3b341a36113fb4b4249b578c4ad192b4ba0ab37549e4908b067a000979202466b19824177867811ade0941896a173f25395159f6514f760176912f2b78dbaef7ea6e95b1
  | 9,1,3=>0x1d7871b214a793902d3db4818d36718b1aa763940c24a7cca4d1517e9aaf8510ad1614018f9b4d56960769819b12166918130f55926947734e7817518b28cc1e7b9182965903031264a5992670c34ab47a3993a47c9af7a59061602aa02093c34243849699acb292c908905e7960009556f96b35898c1921000b4fb97b8124bb796c35e931b0007b9329aaa5d77316b18431189634945217349f71b9bcb3a2b472d74f1a618c969e9ba6849e902980a9d51a90db8fb000193000a49007a09579
  | 9,1,4=>0x9e15476e172c74c000aa499c5b9701a987aaa3f000a111298e924c9f139ab9f000261a800006a96c18140a68626ff40486b88c9719b22774310c1a971317164413e13d14c29890b9681a909096d906a511b5952f56f67b8e109121c47645c630199a819313192d1805a296fc74f9d92526c914741c70d00b1b12f978376517caf4631a9f76ba3ba3717f49186098c321a4fb3e3518f13094c18d97f9a2b809a2384900d4176bb8f3a79059439561bb91f19cf3f71c19d8a018553ab05f2919c1
  | 9,1,5=>0x45482133151f2cdab22420002a19b1a2177a2815a9af12ff099000a9caff0009a98287c21bc22c0c979968abb1a6993b5d9000390a83571719b933b950f4d3411307ae97474a071194d6af74401a1f9479b41a0c8b929b7fa50102738072954939caec4cd61f0007f5aa1b49b112511ca901000581139679a8d3a8b381c4000961b5364c0817732c109a81fac22979c9353371b891e941975727178b469adf92f8bc85946f22210988115f3fcb482f13f13b11765e136da517a97599416a3bc7
  | 9,1,6=>0x603169327a7c1dd14929f000
  | 9,2,0=>0x510c4b77d2e6531161a106ae19cb5c00c99a3a212d38cc6d0d027480576c11d9a5167b51a8436f192d0493310037d620b38a94f2296e484460757991df239391432f208b9276f73f8e5747780b9e2ad968802866330951f2ec4c96614cf068012200
  | 10,0,0=>0x185b51c9196e19726cc15500068d3157c00590423e4006240002c006fc8d39df9368093945f38c34730b515d21000000a9a9705b74b169094271e8f47e137315342e5815e40030ca12dc2c209b167c1b0f801405ca425e1670a33104f2fd71045775fd4a4d8e9509ab3c941724ef665b92ac3f584d11454b57911000003ed91264e400114711ed1a4006eca904d51064ed000b36e994745f12f53931da12f1c2
  | 10,0,1=>0xc93b0b13ac9108ce10cc003644e768210c50c4a4592ec0c
  | 10,1,0=>0x2e67f485a1a2691744917d189085f172cf4506196e4593f6718a8b59e23c8c6179e53c94632565628bcd91c96a82dd9861a9209e91864c1a4f30fd615592432584a65f73ed7f55d74096236453975ce9a0000928c134400a62219f0c3424f987e41144137847a000b70c400410bc8063a0a82c70e2215ca189d02545116d1b1605298a6817e43e9b41113e2b2a6490265a001bf5f954384005ae2028d3131e34
  | 10,1,1=>0x994645f0319f3a8009128b26cfc3fd0b6dc272c5c134dff8e5c965e09525fc0000002c33856113c4193d4b32ed995c41b0d0233148d108c480d4c6f0bf875df138f72f51c006422ae61
  | 10,2,0=>0x9b210fc4b07164c426590048d620c003e5a4012b802927a39084008d88bfc9f488ea44c2d359b9c4e8218c6664007e47e88a5a3d46133404845723e004a9b322270d05423903c552335097e08cc4c8024e006080192a789c06a60b001440139004b2430b34ca436e174d05be19a000000a3
  | 10,3,0=>0x44b89702ca80524cd3172000a1
  | 11,0,0=>0x74005949826181590a6828808d1
  | 11,1,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,2,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,3,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,4,0=>0x320410
  | _,_,_=>0
def s6 : Nat->Nat->Nat->Nat
  | 8,0,0=>0xb43f015e6064040144d0343a0201d0d8240200008800000a500805110010180c0642a080021bc020885a0141802c1200428028ad010191303804842020150000f024010082a064430dc17150220202a05c1c204000e80803000004030284a008031800400882194310180d0200000c34110093b0000ec000080800012074470100c004c1008930243c03002000000000d0000401c030442101c080001d00802
  | 8,0,1=>0x43b244030b42a0040101cbe0284500417000030705869880000001581a0082a08c00004236ac540dc2f034620581c0006515401000040444304c0400004018841b81e0443902412190070044e0580e000c7354150186b06806038a50000400c1d08c0f018010e8000040415800168050c801038000641500c0810006058451e00122801000000481500c000547000029000000000200c480001d1dc0008c04
  | 8,0,2=>0x4522ac05371610000b084162a8120443f000111292f2441a0c00307d280800605c00008b106c0c0140721615004010180a04c1c3840c278be358000300e02c012cc0817c010041a0f00911c4f0102205c4c014001500b0a0000fc06018cb0883e0087c1540500003044680b44800c3e06424058022fdb34711601cdc074210740e4dc130080f004010082a0d0061700604c2b0080105003000100200601002
  | 8,0,3=>0x3ad61084010d80b0103a030002d0063c00d00c0004402128031984d61114018090000607e250254b0981c1440004c0f004050586a014000301a34c1b0ec0a000a21581b02c01400698b0071f99406c030483136c1503493518020681017006000140480000001318010a88e7280a0341a1c90d010910d0bf124000e4020d8890d815008680841d0040201c5a5ac2d03424054aa29078134204540e0cc0005928
  | 8,0,4=>0xda094095502b0282a83088104010006836c0d1ee43390071f40b0e9760040803dfd05515010a96340c46414080bd088a50bc1d2a80401c25005f50049e1f0543e08a0440100002284610000c01c31030000047406816600021440102c77368000a0416702d06d0f0001609959010a3008a70005a31000278010599b064b626802208070000900044669b101401
  | 8,1,0=>0x1305a27c543001002c70455860585502c020380800084028001647200c0505c1211c0a038030ac060000a37c040042e4540200001001a209404000020540c04c1001c770547d0dca80cc14260020902f000020a8050741203410000000e8610001805802000180b000390000844d1800104c0934c091500003438018350002000000000000006b004020381c0201a01c0113c191480101c240440d008031d428
  | 8,1,1=>0x1d3440109c2a018060d4aa2188104425024080a81c01211568ea0700b01c231bc722e0b2030f105417
  | 8,2,0=>0x2a0
  | 9,0,0=>0x6000158ea0020004b8240080900006012e1b41382500a000898840400640082a04a0c81209e0000040a03f0083ec2d009012014000240ba1600183b0bc00402006030008020000900000001001a0300d014006000450040620480e8510000c80005600a0341d82400201c210511820681102c01a004000030060000400c0600e00080102e00c000000082400b0030080180102a0000000d021078010050160040f40300700a048060a201a0080281e
  | 9,0,1=>0x144bc1102e00006c7f0000b402c000040220000900c07000403801010080048110b40140303d0000a4e48000c605c4e8840020680900105e0e00089a0001981c00419e0080a80005e008010a501e0e8e58010d0014d00210000240000f2c82ac9005c002054000973cc21c018300182ac7c80400c0289f83703a0282a8290162681400601a1400280c03804c000640025f0078070260b00c049024004330000201040082d01247c1c00d01200005003
  | 9,0,2=>0xf8073290102681902f28a1f00c00a15e0100082f06014c0703b0020a4520102373005b8012e61dc498b40000a0cb825
  | 9,1,0=>0x28c0a27890020190940c03c0d0008501c362000f00928000ac27c581bc0102c110ac23008001145a000170440c018050040101410164a007c8203416224c81180d02483000000fc2800c050000000875020011bc2c01805000010780a0186e07c000c81e07001044000a44b02000038090cc1a1a8040788212c991a0170000034c0e02823004002100004004044030ec22004230e00001800000010ac0e03414
  | 9,1,1=>0xe2585a0d831208000347a060cb13c0067c052d4311d8210bc12084a0240000001c3596687c0005c340200d94c300080c0000a0344a10ca702402000041c4000200c09ddf05c0e
  | 9,2,0=>0x16502c19604827001e589800894c043a2df1f
  | 10,0,0=>0x58a70d85da24738464c249120001902387a04804d85063cc0a0034408
  | 10,1,0=>0x105ca970402a002eb869d13088088fa20529eb42041904181830ca11e70408007180c4810a31dd4
  | 10,2,0=>0xe410310a49814070431800340400101c6
  | 10,3,0=>0x1c1
  | 11,0,0=>0xf0cd
  | 11,1,0=>0xf4d220
  | 11,2,0=>0xf4d220
  | 11,3,0=>0xf4d220
  | _,_,_=>0
def zg (k t : Nat) (w : List q0) : Nat :=
  match k,t with
  | 8,0 =>
    let h:=uf 65565 w
    let bkt:=h % 625
    let d:=(s6 8 0 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*1) % 1048573+d) % 2624
    (s7 8 0 (slot>>>7)>>>(14*(slot&&&127)))&&&16383
  | 8,1 =>
    let h:=uf 65543 w
    let bkt:=h % 161
    let d:=(s6 8 1 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*17) % 1048573+d) % 674
    (s7 8 1 (slot>>>7)>>>(12*(slot&&&127)))&&&4095
  | 8,2 =>
    let h:=uf 65537 w
    let bkt:=h % 3
    let d:=(s6 8 2 0>>>(4*bkt))&&&15
    let slot:=((h*1) % 1048573+d) % 11
    (s7 8 2 0>>>(6*slot))&&&63
  | 9,0 =>
    let h:=uf 65540 w
    let bkt:=h % 291
    let d:=(s6 9 0 (bkt>>>7)>>>(11*(bkt&&&127)))&&&2047
    let slot:=((h*31) % 1048573+d) % 1220
    (s7 9 0 (slot>>>7)>>>(13*(slot&&&127)))&&&8191
  | 9,1 =>
    let h:=uf 65545 w
    let bkt:=h % 185
    let d:=(s6 9 1 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*17) % 1048573+d) % 776
    (s7 9 1 (slot>>>7)>>>(12*(slot&&&127)))&&&4095
  | 9,2 =>
    let h:=uf 65539 w
    let bkt:=h % 21
    let d:=(s6 9 2 0>>>(7*bkt))&&&127
    let slot:=((h*31) % 1048573+d) % 87
    (s7 9 2 0>>>(9*slot))&&&511
  | 10,0 =>
    let h:=uf 65537 w
    let bkt:=h % 34
    let d:=(s6 10 0 0>>>(7*bkt))&&&127
    let slot:=((h*31) % 1048573+d) % 147
    (s7 10 0 (slot>>>7)>>>(10*(slot&&&127)))&&&1023
  | 10,1 =>
    let h:=uf 65546 w
    let bkt:=h % 45
    let d:=(s6 10 1 0>>>(7*bkt))&&&127
    let slot:=((h*1000) % 1048573+d) % 187
    (s7 10 1 (slot>>>7)>>>(10*(slot&&&127)))&&&1023
  | 10,2 =>
    let h:=uf 65538 w
    let bkt:=h % 22
    let d:=(s6 10 2 0>>>(6*bkt))&&&63
    let slot:=((h*1001) % 1048573+d) % 101
    (s7 10 2 0>>>(9*slot))&&&511
  | 10,3 =>
    let h:=uf 65537 w
    let bkt:=h % 4
    let d:=(s6 10 3 0>>>(3*bkt))&&&7
    let slot:=((h*31) % 1048573+d) % 15
    (s7 10 3 0>>>(7*slot))&&&127
  | 11,0 =>
    let h:=uf 65540 w
    let bkt:=h % 4
    let d:=(s6 11 0 0>>>(4*bkt))&&&15
    let slot:=((h*17) % 1048573+d) % 18
    (s7 11 0 0>>>(6*slot))&&&63
  | 11,1 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 1 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 1 0>>>(6*slot))&&&63
  | 11,2 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 2 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 2 0>>>(6*slot))&&&63
  | 11,3 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 3 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 3 0>>>(6*slot))&&&63
  | 11,4 =>
    let h:=uf 65538 w
    let bkt:=h % 1
    let d:=(s6 11 4 0>>>(1*bkt))&&&1
    let slot:=((h*17) % 1048573+d) % 6
    (s7 11 4 0>>>(4*slot))&&&15
  | _,_=>0
lemma ym : ∀ (g j : Fin 8),
    (q6 g.val>>>(4*j.val))&&&7=vo (uu g) j.val:= by decide +kernel
lemma q03 (j : Nat) (hj : j<8) :
    (q6 0>>>(4*j))&&&7=j:= by
  simpa [uu,vo] using ym 0 ⟨j,hj⟩
lemma xr (g : Fin 8) (j : Nat) (hj : j<8) :
    si ((q6 g.val>>>(4*j))&&&7) =
      r1 g (si ((q6 0>>>(4*j))&&&7)):= by
  rw [q03 j hj];simp only [r1,s3 _ j hj]
  exact congrArg si (ym g ⟨j,hj⟩)
def u2 (permCode : Nat) : Nat->Nat->q0
  | 0,_=>rv
  | fuel+1,i =>
    if Nat.blt i 8 then si ((permCode>>>(4*i))&&&7)
    else
      let k:=i - 8
      let c:=(q2w (k>>>6)>>>(22*(k&&&63)))&&&0x3fffff
      let op:=c&&&3
      let a:=(c>>>2)&&&1023
      if Nat.beq op 0 then qx (u2 permCode fuel a)
      else
        let x:=u2 permCode fuel a
        let y:=u2 permCode fuel (c>>>12)
        if Nat.beq op 1 then (x.1&&&y.1,x.2&&&y.2) else (x.1|||y.1,x.2|||y.2)
lemma rt : ∀ (fuel i : Nat),qb (u2 (q6 0) fuel i)
  | 0,_=>vg
  | fuel+1,i=>by
    unfold u2
    split
    · exact y4 _
    · dsimp only
      split
      · exact ye (rt fuel _)
      · split
        · exact x9 false (rt fuel _) (rt fuel _)
        · exact x9 true (rt fuel _) (rt fuel _)
lemma rp (g : Fin 8) :
    ∀ (fuel i : Nat),u2 (q6 g.val) fuel i=r1 g (u2 (q6 0) fuel i)
  | 0,_=>(xw _).symm
  | fuel+1,i=>by
    unfold u2
    split
    · rename_i hi;exact xr g i (Nat.blt_eq.mp hi)
    · dsimp only
      split
      · rw [rp g fuel _];simp only [r1,us]
      · split
        · rw [rp g fuel _,rp g fuel _]
          exact (su (uu g) false _ _).symm
        · rw [rp g fuel _,rp g fuel _]
          exact (su (uu g) true _ _).symm
def r6 (permCode code j : Nat) (acc : List q0) : List q0 :=
  if code.testBit j then si ((permCode>>>(4*j))&&&7) :: acc else acc
def qq (permCode e : Nat) (acc : List q0) : List q0 :=
  if Nat.beq e 0 then acc else u2 permCode 5 (e+7) :: acc
def ur (permCode code : Nat) (acc : List q0) : List q0 :=
  r6 permCode code 0 (r6 permCode code 1 (r6 permCode code 2 (r6 permCode code 3
    (r6 permCode code 4 (r6 permCode code 5 (r6 permCode code 6 (r6 permCode code 7 acc)))))))
lemma qt (code j : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ r6 (q6 0) code j acc,qb x:= by
  unfold r6;split
  · intro x hx;rcases List.mem_cons.mp hx with rfl | ht;exact y4 _;exact ha x ht
  · exact ha
lemma qi (e : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ qq (q6 0) e acc,qb x:= by
  unfold qq;split
  · exact ha
  · intro x hx;rcases List.mem_cons.mp hx with rfl | ht;exact rt 5 _;exact ha x ht
lemma qo (g : Fin 8) (code j : Nat) (hj : j<8) (acc : List q0) :
    (r6 (q6 0) code j acc).map (r1 g) =
      r6 (q6 g.val) code j (acc.map (r1 g)):= by
  unfold r6;split <;> simp [xr g j hj]
lemma sl (g : Fin 8) (e : Nat) (acc : List q0) :
    (qq (q6 0) e acc).map (r1 g) =
      qq (q6 g.val) e (acc.map (r1 g)):= by
  unfold qq;split <;> simp [rp]
lemma ux (code : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ ur (q6 0) code acc,qb x:= by
  unfold ur
  exact qt _ _ (qt _ _ (qt _ _ (qt _ _
    (qt _ _ (qt _ _ (qt _ _ (qt _ _ ha)))))))
lemma uh (g : Fin 8) (code : Nat) (acc : List q0) :
    (ur (q6 0) code acc).map (r1 g) =
      ur (q6 g.val) code (acc.map (r1 g)):= by
  simp only [ur,qo g _ 0 (by omega),qo g _ 1 (by omega),
    qo g _ 2 (by omega),qo g _ 3 (by omega),
    qo g _ 4 (by omega),qo g _ 5 (by omega),
    qo g _ 6 (by omega),qo g _ 7 (by omega)]
def st (permCode k t i : Nat) : List q0 :=
  let c2:=q3y k t
  if Nat.blt i c2 then
    let code:=(q3w k t (i>>>6)>>>(28*(i&&&63)))&&&0xfffffff
    qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
      (ur permCode code []))
  else
    let c3:=q3x k t
    if Nat.blt i c3 then
      let j:=i - c2
      let code:=(q3v k t (j>>>6)>>>(38*(j&&&63)))&&&0x3fffffffff
      qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
        (qq permCode ((code>>>28)&&&1023) (ur permCode code [])))
    else
      let code:=(q3u k t>>>(48*(i - c3)))&&&0xffffffffffff
      qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
        (qq permCode ((code>>>28)&&&1023) (qq permCode ((code>>>38)&&&1023)
          (ur permCode code []))))
def q8 (k t i : Nat) : List q0:=st (q6 0) k t i
lemma sx (k t i : Nat) : ∀ x ∈ q8 k t i,qb x:= by
  unfold q8 st;dsimp only
  split
  · exact qi _ (qi _ (ux _ (by simp)))
  · split
    · exact qi _ (qi _ (qi _ (ux _ (by simp))))
    · exact qi _ (qi _ (qi _ (qi _ (ux _ (by simp)))))
lemma xa (g : Fin 8) (k t i : Nat) :
    (q8 k t i).map (r1 g)=st (q6 g.val) k t i:= by
  unfold q8 st;dsimp only
  split
  · simp only [sl,uh,List.map_nil]
  · split
    · simp only [sl,uh,List.map_nil]
    · simp only [sl,uh,List.map_nil]
def r5 (k t : Nat) (w : List q0) : Bool :=
  let n:=zg k t w
  if Nat.beq n 0 then false
  else
    let m:=n - 1
    let i:=m>>>3
    Nat.blt i (qk k t) &&
      vp w (st (q6 (m&&&7)) k t i)
lemma rk {k t : Nat}
    (h : ∀ i<qk k t,qs k t (q8 k t i)) {w : List q0}
    (hw : r5 k t w=true) : qs k t w:= by
  unfold r5 at hw;dsimp only at hw
  split at hw
  · contradiction
  · simp only [Bool.and_eq_true,Nat.blt_eq] at hw
    obtain ⟨hi,hp⟩:=hw
    have hp':=yp hp
    have hlt : (zg k t w - 1)&&&7<8:= by have : (zg k t w - 1)&&&7 ≤ 7:=Nat.and_le_right;omega
    let g : Fin 8:=⟨(zg k t w - 1)&&&7,hlt⟩
    rw [← xa g k t ((zg k t w - 1)>>>3)] at hp'
    intro m hm hr
    apply h _ hi m hm
    have himg : w.toFinset.image (zk g)=(q8 k t ((zg k t w - 1)>>>3)).toFinset:= by
      ext x
      simp only [Finset.mem_image,List.mem_toFinset,hp'.mem_iff,List.mem_map]
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        have hzv:=sx k t _ z hz
        rwa [zk,r1,ut (uu g) hzv]
      · intro hx
        exact ⟨r1 g x,⟨x,hx,rfl⟩,ut (uu g) (sx k t _ x hx)⟩
    rw [← himg]
    exact xe (uu g).reverse hr
def rb (k t i : Nat) : Bool :=
  let v:=q8 k t i
  v4 v&&!xd k t v
def q4 (k t i : Nat) : Bool :=
  let v:=q8 (k+1) t i
  v4 v &&
    !v0 k t v (fun w=>!r5 k (t - 1) w) (fun w=>!r5 k t w)
def vk (t : Nat) : Bool :=
  !v0 11 t rj (fun w=>!r5 11 (t - 1) w) (fun w=>!r5 11 t w)
lemma ya {k t i : Nat} (h : rb k t i=true) :
    qs k t (q8 k t i):= by
  simp only [rb,Bool.and_eq_true,Bool.not_eq_true'] at h
  exact yy (ve h.1) h.2
lemma sk {k t i : Nat} (ht : t ≤ 5)
    (hp : ∀ t ≤ 5,∀ i<qk k t,qs k t (q8 k t i))
    (h : q4 k t i=true) : qs (k+1) t (q8 (k+1) t i):= by
  simp only [q4,Bool.and_eq_true,Bool.not_eq_true'] at h
  apply xv (ve h.1) _ _ h.2
  · intro w hw;exact rk (hp (t - 1) (by omega)) (by simpa using hw)
  · intro w hw;exact rk (hp t ht) (by simpa using hw)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3c : Theta.span (rb 8 0) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2v : Theta.span (rb 8 0) 250 250=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2u : Theta.span (rb 8 0) 250 500=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2t : Theta.span (rb 8 0) 250 750=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1q : Theta.span (rb 8 0) 250 1000=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1p : Theta.span (rb 8 0) 93 1250=true:= by decide +kernel
lemma q2r : Theta.span (rb 8 0) 1343 0=true:=(@Theta.span_join (rb 8 0) 750 0 593 (@Theta.span_join (rb 8 0) 250 0 500 q3c (@Theta.span_join (rb 8 0) 250 250 250 q2v q2u)) (@Theta.span_join (rb 8 0) 250 750 343 q2t (@Theta.span_join (rb 8 0) 250 1000 93 q1q q1p)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3b : Theta.span (rb 8 1) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2s : Theta.span (rb 8 1) 99 250=true:= by decide +kernel
lemma q2q : Theta.span (rb 8 1) 349 0=true:=(@Theta.span_join (rb 8 1) 250 0 99 q3b q2s)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2p : Theta.span (rb 8 2) 6 0=true:= by decide +kernel
lemma q2o : Theta.span (rb 8 3) 0 0=true:=rfl
lemma q2n : Theta.span (rb 8 4) 0 0=true:=rfl
lemma q2m : Theta.span (rb 8 5) 0 0=true:=rfl
lemma q1r (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 8 t) : rb 8 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q2r i (Nat.zero_le i) hi
  · exact Theta.span_ok q2q i (Nat.zero_le i) hi
  · exact Theta.span_ok q2p i (Nat.zero_le i) hi
  · exact Theta.span_ok q2o i (Nat.zero_le i) hi
  · exact Theta.span_ok q2n i (Nat.zero_le i) hi
  · exact Theta.span_ok q2m i (Nat.zero_le i) hi
lemma zt (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 8 t) : qs 8 t (q8 8 t i) :=
  ya (q1r t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3a : Theta.span (q4 8 0) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2l : Theta.span (q4 8 0) 250 250=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2k : Theta.span (q4 8 0) 102 500=true:= by decide +kernel
lemma q2i : Theta.span (q4 8 0) 602 0=true:=(@Theta.span_join (q4 8 0) 250 0 352 q3a (@Theta.span_join (q4 8 0) 250 250 102 q2l q2k))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q39 : Theta.span (q4 8 1) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2j : Theta.span (q4 8 1) 128 250=true:= by decide +kernel
lemma q2h : Theta.span (q4 8 1) 378 0=true:=(@Theta.span_join (q4 8 1) 250 0 128 q39 q2j)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2g : Theta.span (q4 8 2) 41 0=true:= by decide +kernel
lemma q2f : Theta.span (q4 8 3) 0 0=true:=rfl
lemma q2e : Theta.span (q4 8 4) 0 0=true:=rfl
lemma q2d : Theta.span (q4 8 5) 0 0=true:=rfl
lemma q1o (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 9 t) : q4 8 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q2i i (Nat.zero_le i) hi
  · exact Theta.span_ok q2h i (Nat.zero_le i) hi
  · exact Theta.span_ok q2g i (Nat.zero_le i) hi
  · exact Theta.span_ok q2f i (Nat.zero_le i) hi
  · exact Theta.span_ok q2e i (Nat.zero_le i) hi
  · exact Theta.span_ok q2d i (Nat.zero_le i) hi
lemma zr (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 9 t) : qs 9 t (q8 9 t i) :=
  sk ht zt (q1o t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q23 : Theta.span (q4 9 0) 64 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q22 : Theta.span (q4 9 1) 84 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q21 : Theta.span (q4 9 2) 43 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q20 : Theta.span (q4 9 3) 8 0=true:= by decide +kernel
lemma q1z : Theta.span (q4 9 4) 0 0=true:=rfl
lemma q1y : Theta.span (q4 9 5) 0 0=true:=rfl
lemma q0z (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 10 t) : q4 9 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q23 i (Nat.zero_le i) hi
  · exact Theta.span_ok q22 i (Nat.zero_le i) hi
  · exact Theta.span_ok q21 i (Nat.zero_le i) hi
  · exact Theta.span_ok q20 i (Nat.zero_le i) hi
  · exact Theta.span_ok q1z i (Nat.zero_le i) hi
  · exact Theta.span_ok q1y i (Nat.zero_le i) hi
lemma zb (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 10 t) : qs 10 t (q8 10 t i) :=
  sk ht zr (q0z t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1x : Theta.span (q4 10 0) 5 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1w : Theta.span (q4 10 1) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1v : Theta.span (q4 10 2) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1u : Theta.span (q4 10 3) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1t : Theta.span (q4 10 4) 1 0=true:= by decide +kernel
lemma q1s : Theta.span (q4 10 5) 0 0=true:=rfl
lemma q0y (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 11 t) : q4 10 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q1x i (Nat.zero_le i) hi
  · exact Theta.span_ok q1w i (Nat.zero_le i) hi
  · exact Theta.span_ok q1v i (Nat.zero_le i) hi
  · exact Theta.span_ok q1u i (Nat.zero_le i) hi
  · exact Theta.span_ok q1t i (Nat.zero_le i) hi
  · exact Theta.span_ok q1s i (Nat.zero_le i) hi
lemma x7 (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 11 t) : qs 11 t (q8 11 t i) :=
  sk ht zb (q0y t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v3 : vk 0=true/\vk 1=true/\vk 2=true/\vk 3=true/\vk 4=true/\vk 5=true:= by decide +kernel
lemma q02 (t : Nat) (ht : t ≤ 5) : vk t=true:= by
  interval_cases t
  · exact v3.1
  · exact v3.2.1
  · exact v3.2.2.1
  · exact v3.2.2.2.1
  · exact v3.2.2.2.2.1
  · exact v3.2.2.2.2.2
lemma yk (t : Nat) (ht : t ≤ 5) : qs 12 t rj:= by
  have h:=q02 t ht
  simp only [vk,Bool.not_eq_true'] at h
  apply xv q19 _ _ h
  · intro w hw;exact rk (x7 (t - 1) (by omega)) (by simpa using hw)
  · intro w hw;exact rk (x7 t ht) (by simpa using hw)
theorem no_live12 {k t : Nat} {S : Finset Sig} (hk : k ≤ 12) (h : Live k t S)
    (hsub : ∀ a ∈ S,a ∈ raw) : False:= by
  have hn : qy k t (S.image y7):=z5 h
  have hnsub : ∀ a ∈ S.image y7,a ∈ rj:= by
    intro a ha;obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ha
    exact q00 (hsub x hx)
  have eq:=q1l hn hnsub
  rw [← eq] at hn
  have sz:=xg hn
  rw [List.toFinset_card_of_nodup q19] at sz
  have hlen : rj.length=8:=rfl
  have ht : t ≤ 5:= by omega
  exact yk t ht k hk (yl hn (xf hk))
end Base1007
namespace Main3346

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BF := (Fin 9 → Bool) → Bool

def F9 : BF := fun x4 =>
  x4 (0 : Fin 9) && x4 (1 : Fin 9) || x4 (1 : Fin 9) && x4 (2 : Fin 9) ||
  x4 (2 : Fin 9) && x4 (3 : Fin 9) || x4 (3 : Fin 9) && x4 (4 : Fin 9) ||
  x4 (4 : Fin 9) && x4 (0 : Fin 9) || x4 (0 : Fin 9) && x4 (5 : Fin 9) ||
  x4 (1 : Fin 9) && x4 (6 : Fin 9) || x4 (2 : Fin 9) && x4 (7 : Fin 9) ||
  x4 (3 : Fin 9) && x4 (8 : Fin 9) || x4 (5 : Fin 9) && x4 (7 : Fin 9) ||
  x4 (6 : Fin 9) && x4 (8 : Fin 9) || x4 (8 : Fin 9) && x4 (5 : Fin 9)

def wVar (i : Fin 9) : BF := fun x => x i
def w09 : BF := fun x => x 4 || x 6
def cFalse : BF := fun _ => false
def cTrue : BF := fun _ => true
def neg9 (φ : BF) : BF := fun x => !(φ x)
def bin9 (d : Bool) (φ ψ : BF) : BF := if d then fun x => φ x || ψ x else fun x => φ x && ψ x
def proper9 (φ : BF) : Prop := φ ≠ cFalse ∧ φ ≠ cTrue

def wireBase (i : Nat) : BF :=
  if h : i < 9 then wVar ⟨i, h⟩
  else if i = 9 then w09
  else cFalse

def sBase : List BF := (List.ofFn wVar) ++ [w09]

lemma mem_sBase_var (i : Fin 9) : wVar i ∈ sBase := by
  simp only [sBase, List.mem_append, List.mem_ofFn]
  exact Or.inl ⟨i, rfl⟩

lemma mem_sBase_w09 : w09 ∈ sBase := by
  simp [sBase]

lemma getD_sBase (i : Nat) : sBase.getD i cFalse = wireBase i := by
  unfold wireBase sBase
  by_cases h9 : i < 9
  · simp only [h9, dite_true]
    interval_cases i <;> rfl
  · simp only [h9, dite_false]
    by_cases he : i = 9
    · subst he
      rfl
    · simp only [he, ite_false]
      rw [List.getD_eq_default _ _ (by simp; omega)]

lemma F9_ne_cFalse : F9 ≠ cFalse := by
  intro h
  have h1 := congrFun h (fun i => decide (i = 0 ∨ i = 1))
  revert h1
  decide

lemma F9_ne_cTrue : F9 ≠ cTrue := by
  intro h
  have h1 := congrFun h (fun _ => false)
  revert h1
  decide

lemma F9_proper : proper9 F9 := ⟨F9_ne_cFalse, F9_ne_cTrue⟩

def Live9 (k t : Nat) (S : Finset BF) : Prop :=
  ∀ (P : Nat → Nat → Finset BF → Prop),
    P 0 0 {F9} →
    (∀ {k t : Nat} {U : Finset BF} {a : BF}, proper9 a → neg9 a ∉ insert a U →
      P k t (insert (neg9 a) U) → P (k + 1) (t + 1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset BF} {a b : BF} {d : Bool}, proper9 a → proper9 b → a ≠ b →
      bin9 d a b ∉ insert a (insert b U) →
      P k t (insert (bin9 d a b) U) → P (k + 1) t (insert a (insert b U))) →
    P k t S

theorem Live9.stop : Live9 0 0 {F9} := fun _ hs _ _ => hs

theorem Live9.unary {k t : Nat} {U : Finset BF} {a : BF}
    (ha : proper9 a) (hf : neg9 a ∉ insert a U) (tail : Live9 k t (insert (neg9 a) U)) :
    Live9 (k + 1) (t + 1) (insert a U) :=
  fun P hs hu hb => hu ha hf (tail P hs hu hb)

theorem Live9.binary {k t : Nat} {U : Finset BF} {a b : BF} {d : Bool}
    (ha : proper9 a) (hb : proper9 b) (hab : a ≠ b) (hf : bin9 d a b ∉ insert a (insert b U))
    (tail : Live9 k t (insert (bin9 d a b) U)) :
    Live9 (k + 1) t (insert a (insert b U)) :=
  fun P hs hu hb' => hb' ha hb hab hf (tail P hs hu hb')

theorem Live9.elimInd {P : Nat → Nat → Finset BF → Prop}
    (stop : P 0 0 {F9})
    (unary : ∀ {k t : Nat} {U : Finset BF} {a : BF}, proper9 a → neg9 a ∉ insert a U →
      Live9 k t (insert (neg9 a) U) → P k t (insert (neg9 a) U) → P (k + 1) (t + 1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset BF} {a b : BF} {d : Bool}, proper9 a → proper9 b → a ≠ b →
      bin9 d a b ∉ insert a (insert b U) →
      Live9 k t (insert (bin9 d a b) U) → P k t (insert (bin9 d a b) U) → P (k + 1) t (insert a (insert b U)))
    {k t : Nat} {S : Finset BF} (h : Live9 k t S) : P k t S := by
  apply And.right (a := Live9 k t S)
  apply h (fun k t S => Live9 k t S ∧ P k t S)
  · exact ⟨Live9.stop, stop⟩
  · intro k t U a ha hf prev
    exact ⟨Live9.unary ha hf prev.1, unary ha hf prev.1 prev.2⟩
  · intro k t U a b d ha hb hab hf prev
    exact ⟨Live9.binary ha hb hab hf prev.1, binary ha hb hab hf prev.1 prev.2⟩

lemma live9_proper {k t : Nat} {S : Finset BF} (h : Live9 k t S) : ∀ a ∈ S, proper9 a := by
  apply Live9.elimInd (h := h)
  · intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact F9_proper
  · intro k t U a ha _ _ ih x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · exact ha
    · exact ih x (Finset.mem_insert_of_mem hxU)
  · intro k t U a b d ha hb _ _ _ ih x hx
    rcases Finset.mem_insert.mp hx with rfl | hx1
    · exact ha
    · rcases Finset.mem_insert.mp hx1 with rfl | hxU
      · exact hb
      · exact ih x (Finset.mem_insert_of_mem hxU)

lemma live9_sep {k t : Nat} {S : Finset BF} (h : Live9 k t S) :
    ∀ p q : Fin 9 → Bool, F9 p ≠ F9 q → ∃ φ ∈ S, φ p ≠ φ q := by
  apply Live9.elimInd (h := h)
  · intro p q hpq
    exact ⟨F9, Finset.mem_singleton_self _, hpq⟩
  · intro k t U a _ _ _ ih p q hpq
    obtain ⟨φ, hφ, hneq⟩ := ih p q hpq
    rcases Finset.mem_insert.mp hφ with rfl | hφU
    · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
      intro heq
      exact hneq (congrArg Bool.not heq)
    · exact ⟨φ, Finset.mem_insert_of_mem hφU, hneq⟩
  · intro k t U a b d _ _ _ _ _ ih p q hpq
    obtain ⟨φ, hφ, hneq⟩ := ih p q hpq
    rcases Finset.mem_insert.mp hφ with rfl | hφU
    · by_cases ha : a p = a q
      · refine ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
        intro hb
        apply hneq
        cases d <;> simp [bin9, ha, hb]
      · exact ⟨a, Finset.mem_insert_self _ _, ha⟩
    · exact ⟨φ, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hφU), hneq⟩

def rep9 (w : List BF) (z : BF) : Prop := z ∈ w ∨ ¬ proper9 z

def wit9 (w : List BF) (z : BF) : Prop :=
  (∃ a ∈ w, proper9 a ∧ z = neg9 a) ∨
  (∃ a ∈ w, ∃ b ∈ w, ∃ d : Bool, proper9 a ∧ proper9 b ∧ a ≠ b ∧ z = bin9 d a b)

lemma op9_cases {w : List BF} {a : BF} (ha : rep9 w a) :
    a = cFalse ∨ a = cTrue ∨ (a ∈ w ∧ proper9 a) := by
  by_cases h0 : a = cFalse
  · exact Or.inl h0
  · by_cases h1 : a = cTrue
    · exact Or.inr (Or.inl h1)
    · have hp : proper9 a := ⟨h0, h1⟩
      rcases ha with hm | hnp
      · exact Or.inr (Or.inr ⟨hm, hp⟩)
      · exact (hnp hp).elim

lemma neg9_cFalse : neg9 cFalse = cTrue := rfl
lemma neg9_cTrue : neg9 cTrue = cFalse := rfl

lemma bin9_laws (a : BF) :
    bin9 false a cTrue = a ∧ bin9 true a cFalse = a ∧
    bin9 false a cFalse = cFalse ∧ bin9 true a cTrue = cTrue ∧
    bin9 false a a = a ∧ bin9 true a a = a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext x <;> simp [bin9, cFalse, cTrue]

lemma bin9_comm (d : Bool) (a b : BF) : bin9 d a b = bin9 d b a := by
  cases d <;> funext x <;> simp [bin9, Bool.and_comm, Bool.or_comm]

lemma neg9_rep {w : List BF} {a : BF} (ha : rep9 w a) : rep9 w (neg9 a) ∨ wit9 w (neg9 a) := by
  rcases op9_cases ha with rfl | rfl | ⟨hm, hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg9_cFalse)
  · exact Or.inl (Or.inr fun h => h.1 neg9_cTrue)
  · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)

lemma bin9_rep (d : Bool) {w : List BF} {a b : BF} (ha : rep9 w a) (hb : rep9 w b) :
    rep9 w (bin9 d a b) ∨ wit9 w (bin9 d a b) := by
  rcases op9_cases ha with rfl | rfl | ⟨ham, hap⟩
  · cases d
    · rw [bin9_comm, (bin9_laws b).2.2.1]; exact Or.inl (Or.inr fun h => h.1 rfl)
    · rw [bin9_comm, (bin9_laws b).2.1]; exact Or.inl hb
  · cases d
    · rw [bin9_comm, (bin9_laws b).1]; exact Or.inl hb
    · rw [bin9_comm, (bin9_laws b).2.2.2.1]; exact Or.inl (Or.inr fun h => h.2 rfl)
  · rcases op9_cases hb with rfl | rfl | ⟨hbm, hbp⟩
    · cases d
      · rw [(bin9_laws a).2.2.1]; exact Or.inl (Or.inr fun h => h.1 rfl)
      · rw [(bin9_laws a).2.1]; exact Or.inl (Or.inl ham)
    · cases d
      · rw [(bin9_laws a).1]; exact Or.inl (Or.inl ham)
      · rw [(bin9_laws a).2.2.2.1]; exact Or.inl (Or.inr fun h => h.2 rfl)
    · by_cases hab : a = b
      · subst hab
        cases d
        · rw [(bin9_laws a).2.2.2.2.1]; exact Or.inl (Or.inl ham)
        · rw [(bin9_laws a).2.2.2.2.2]; exact Or.inl (Or.inl ham)
      · exact Or.inr (Or.inr ⟨a, ham, b, hbm, d, hap, hbp, hab, rfl⟩)

lemma pull_gate9 {k t : Nat} {S : Finset BF} {w : List BF} {z : BF}
    (hl : Live9 k t S) (hz : rep9 w z ∨ wit9 w z) (hsub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ l u T, l ≤ k + 1 ∧ Live9 l u T ∧ ∀ a ∈ T, a ∈ w := by
  by_cases hzw : z ∈ w
  · refine ⟨k, t, S, by omega, hl, fun a ha => ?_⟩
    rcases List.mem_append.mp (hsub a ha) with haw | haz
    · exact haw
    · simp only [List.mem_singleton] at haz; exact haz ▸ hzw
  · by_cases hzS : z ∈ S
    · have hzp : proper9 z := live9_proper hl z hzS
      rcases hz with hrep | hwit
      · rcases hrep with hm | hnp
        · exact (hzw hm).elim
        · exact (hnp hzp).elim
      · let U := S.erase z
        have hSU : insert z U = S := Finset.insert_erase hzS
        have hUsub : ∀ x ∈ U, x ∈ w := by
          intro x hx
          have hxne : x ≠ z := (Finset.mem_erase.mp hx).1
          have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
          rcases List.mem_append.mp (hsub x hxS) with hxw | hxz
          · exact hxw
          · simp only [List.mem_singleton] at hxz; exact (hxne hxz).elim
        rcases hwit with ⟨a, haw, hap, rfl⟩ | ⟨a, haw, b, hbw, d, hap, hbp, hab, rfl⟩
        · have hfresh : neg9 a ∉ insert a U := by
            intro hm
            rcases Finset.mem_insert.mp hm with heq | hmU
            · rw [heq] at hzw; exact hzw haw
            · exact (Finset.mem_erase.mp hmU).1 rfl
          refine ⟨k + 1, t + 1, insert a U, le_refl _, Live9.unary hap hfresh (hSU.symm ▸ hl), ?_⟩
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxU
          · exact haw
          · exact hUsub x hxU
        · have hfresh : bin9 d a b ∉ insert a (insert b U) := by
            intro hm
            rcases Finset.mem_insert.mp hm with heq | hm1
            · rw [heq] at hzw; exact hzw haw
            · rcases Finset.mem_insert.mp hm1 with heq | hmU
              · rw [heq] at hzw; exact hzw hbw
              · exact (Finset.mem_erase.mp hmU).1 rfl
          refine ⟨k + 1, t, insert a (insert b U), le_refl _,
            Live9.binary hap hbp hab hfresh (hSU.symm ▸ hl), ?_⟩
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx1
          · exact haw
          · rcases Finset.mem_insert.mp hx1 with rfl | hxU
            · exact hbw
            · exact hUsub x hxU
    · refine ⟨k, t, S, by omega, hl, fun a ha => ?_⟩
      rcases List.mem_append.mp (hsub a ha) with haw | haz
      · exact haw
      · simp only [List.mem_singleton] at haz; exact (hzS (haz ▸ ha)).elim

def gateBF (w : List BF) (g : Gate) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (w.getD i cFalse) x)

def wiresBF (gs : List Gate) (s : List BF) : List BF :=
  gs.foldl (fun w g => w ++ [gateBF w g]) s

lemma gateBF_eval (w : List BF) (g : Gate) (x : Fin 9 → Bool) :
    gateBF w g x = g.op.eval (g.inputs.map fun i => (w.map fun f => f x).getD i false) := by
  unfold gateBF
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
    rfl

lemma wiresBF_map (gs : List Gate) : ∀ (s : List BF) (x : Fin 9 → Bool),
    (wiresBF gs s).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (s.map fun f => f x) := by
  induction gs with
  | nil => intro s x; rfl
  | cons g gs ih =>
    intro s x
    change (wiresBF gs (s ++ [gateBF s g])).map (fun f => f x) = _
    rw [ih (s ++ [gateBF s g]) x]
    simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_cons]
    rw [gateBF_eval]

lemma gateBF_step (w : List BF) (g : Gate)
    (hok : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    rep9 w (gateBF w g) ∨ wit9 w (gateBF w g) := by
  have hget : ∀ i : Nat, rep9 w (w.getD i cFalse) := by
    intro i
    by_cases hi : i < w.length
    · left
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · right
      rw [List.getD_eq_default _ _ (by omega)]
      exact fun h => h.1 rfl
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hok
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact Or.inl (Or.inr fun h => h.2 (by funext x; rfl))
    · have heq : gateBF w ⟨GateOp.and, [a]⟩ = w.getD a cFalse := by
        funext x; simp [gateBF, GateOp.eval]
      rw [heq]; exact Or.inl (hget a)
    · have heq : gateBF w ⟨GateOp.and, [a, b]⟩ = bin9 false (w.getD a cFalse) (w.getD b cFalse) := by
        funext x; simp [gateBF, GateOp.eval, bin9]
      rw [heq]; exact bin9_rep false (hget a) (hget b)
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact Or.inl (Or.inr fun h => h.1 (by funext x; rfl))
    · have heq : gateBF w ⟨GateOp.or, [a]⟩ = w.getD a cFalse := by
        funext x; simp [gateBF, GateOp.eval]
      rw [heq]; exact Or.inl (hget a)
    · have heq : gateBF w ⟨GateOp.or, [a, b]⟩ = bin9 true (w.getD a cFalse) (w.getD b cFalse) := by
        funext x; simp [gateBF, GateOp.eval, bin9]
      rw [heq]; exact bin9_rep true (hget a) (hget b)
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact Or.inl (Or.inr fun h => h.2 (by funext x; rfl))
    · have heq : gateBF w ⟨GateOp.not, a :: l⟩ = neg9 (w.getD a cFalse) := by
        funext x; simp [gateBF, GateOp.eval, neg9]
      rw [heq]; exact neg9_rep (hget a)

lemma extract9 (gs : List Gate) : ∀ s : List BF,
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    F9 ∈ wiresBF gs s →
    ∃ k u S, k ≤ gs.length ∧ Live9 k u S ∧ ∀ a ∈ S, a ∈ s := by
  induction gs with
  | nil =>
    intro s _ hmem
    exact ⟨0, 0, {F9}, le_refl _, Live9.stop, by simpa [wiresBF] using hmem⟩
  | cons g gs ih =>
    intro s hok hmem
    have hmem' : F9 ∈ wiresBF gs (s ++ [gateBF s g]) := hmem
    obtain ⟨k, u, S, hk, hl, hsub⟩ := ih (s ++ [gateBF s g])
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hmem'
    have hstep := gateBF_step s g (hok g List.mem_cons_self)
    obtain ⟨l, u', T, hl', hlt, hT⟩ := pull_gate9 hl hstep hsub
    exact ⟨l, u', T, by rw [List.length_cons]; omega, hlt, hT⟩

def packNat (g : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => packNat g n ||| (if g n then 2 ^ n else 0)

lemma packNat_testBit (g : Nat → Bool) (n i : Nat) :
    (packNat g n).testBit i = (decide (i < n) && g i) := by
  induction n with
  | zero => simp [packNat]
  | succ n ih =>
    rw [packNat, Nat.testBit_or, ih]
    rcases Nat.lt_trichotomy i n with h | h | h
    · have h1 : i < n + 1 := by omega
      have h2 : n ≠ i := by omega
      cases hg : g n <;> simp [h, h1, h2]
    · rw [h]
      cases hg : g n <;> simp
    · have h1 : ¬ i < n + 1 := by omega
      have h0 : ¬ i < n := by omega
      have h2 : n ≠ i := by omega
      cases hg : g n <;> simp [h0, h1, h2]

def pos8 (j : Nat) (i : Fin 8) : Bool := (Base1007.raw.getD i.val Base1007.zero).1.getLsbD j
def neg8 (j : Nat) (i : Fin 8) : Bool := (Base1007.raw.getD i.val Base1007.zero).2.getLsbD j

def lift8 (emb : Fin 8 → Fin 9) (y : Fin 8 → Bool) (v : Fin 9) : Bool :=
  (List.finRange 8).any (fun i => decide (emb i = v) && y i)

lemma lift8_hit {emb : Fin 8 → Fin 9} (hinj : Function.Injective emb) (y : Fin 8 → Bool) (i : Fin 8) :
    lift8 emb y (emb i) = y i := by
  unfold lift8
  cases hy : y i
  · rw [Bool.eq_false_iff]
    intro h
    obtain ⟨j, _, hj⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    have hji : j = i := hinj hj.1
    subst hji
    rw [hy] at hj
    exact Bool.false_ne_true hj.2
  · apply List.any_eq_true.mpr
    exact ⟨i, List.mem_finRange i, by simp [hy]⟩

lemma lift8_miss {emb : Fin 8 → Fin 9} {d : Fin 9} (hmiss : ∀ i : Fin 8, emb i ≠ d) (y : Fin 8 → Bool) :
    lift8 emb y d = false := by
  unfold lift8
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨j, _, hj⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
  exact hmiss j hj.1

def proj8 (emb : Fin 8 → Fin 9) (φ : BF) : Base1007.Sig :=
  (BitVec.ofNat 252 (packNat (fun j => φ (lift8 emb (pos8 j))) 252),
   BitVec.ofNat 252 (packNat (fun j => φ (lift8 emb (neg8 j))) 252))

lemma top8_bit (j : Nat) (hj : j < 252) : Base1007.top.getLsbD j = true := by
  rw [Base1007.top, BitVec.getLsbD_allOnes]
  simp [hj]

lemma zero8_bit1 (j : Nat) : Base1007.zero.1.getLsbD j = false := BitVec.getLsbD_zero
lemma zero8_bit2 (j : Nat) : Base1007.zero.2.getLsbD j = false := BitVec.getLsbD_zero
lemma target8_bit2 (j : Nat) : Base1007.target.2.getLsbD j = false := BitVec.getLsbD_zero

lemma proj8_fst_bit (emb : Fin 8 → Fin 9) (φ : BF) (j : Nat) (hj : j < 252) :
    (proj8 emb φ).1.getLsbD j = φ (lift8 emb (pos8 j)) := by
  unfold proj8
  rw [BitVec.getLsbD_ofNat, packNat_testBit]
  simp [hj]

lemma proj8_snd_bit (emb : Fin 8 → Fin 9) (φ : BF) (j : Nat) (hj : j < 252) :
    (proj8 emb φ).2.getLsbD j = φ (lift8 emb (neg8 j)) := by
  unfold proj8
  rw [BitVec.getLsbD_ofNat, packNat_testBit]
  simp [hj]

lemma sig8_ext {a b : Base1007.Sig}
    (h1 : ∀ j < 252, a.1.getLsbD j = b.1.getLsbD j)
    (h2 : ∀ j < 252, a.2.getLsbD j = b.2.getLsbD j) : a = b :=
  Prod.ext (BitVec.eq_of_getLsbD_eq h1) (BitVec.eq_of_getLsbD_eq h2)

lemma proj8_false (emb : Fin 8 → Fin 9) : proj8 emb cFalse = Base1007.zero := by
  apply sig8_ext <;> intro j hj
  · rw [proj8_fst_bit _ _ _ hj, zero8_bit1]; rfl
  · rw [proj8_snd_bit _ _ _ hj, zero8_bit2]; rfl

lemma proj8_true (emb : Fin 8 → Fin 9) : proj8 emb cTrue = Base1007.one := by
  apply sig8_ext <;> intro j hj
  · rw [proj8_fst_bit _ _ _ hj, Base1007.one, top8_bit _ hj]; rfl
  · rw [proj8_snd_bit _ _ _ hj, Base1007.one, top8_bit _ hj]; rfl

lemma proj8_neg (emb : Fin 8 → Fin 9) (φ : BF) :
    proj8 emb (neg9 φ) = Base1007.neg (proj8 emb φ) := by
  apply sig8_ext <;> intro j hj
  · rw [proj8_fst_bit _ _ _ hj, Base1007.neg, BitVec.getLsbD_not, proj8_fst_bit _ _ _ hj]
    simp [hj, neg9]
  · rw [proj8_snd_bit _ _ _ hj, Base1007.neg, BitVec.getLsbD_not, proj8_snd_bit _ _ _ hj]
    simp [hj, neg9]

lemma proj8_bin (emb : Fin 8 → Fin 9) (d : Bool) (φ ψ : BF) :
    proj8 emb (bin9 d φ ψ) = Base1007.bin d (proj8 emb φ) (proj8 emb ψ) := by
  cases d <;> apply sig8_ext <;> intro j hj
  · rw [proj8_fst_bit _ _ _ hj, Base1007.bin, if_neg Bool.false_ne_true, BitVec.getLsbD_and,
      proj8_fst_bit _ _ _ hj, proj8_fst_bit _ _ _ hj]; rfl
  · rw [proj8_snd_bit _ _ _ hj, Base1007.bin, if_neg Bool.false_ne_true, BitVec.getLsbD_and,
      proj8_snd_bit _ _ _ hj, proj8_snd_bit _ _ _ hj]; rfl
  · rw [proj8_fst_bit _ _ _ hj, Base1007.bin, if_pos rfl, BitVec.getLsbD_or,
      proj8_fst_bit _ _ _ hj, proj8_fst_bit _ _ _ hj]; rfl
  · rw [proj8_snd_bit _ _ _ hj, Base1007.bin, if_pos rfl, BitVec.getLsbD_or,
      proj8_snd_bit _ _ _ hj, proj8_snd_bit _ _ _ hj]; rfl

lemma proj8_var_hit {emb : Fin 8 → Fin 9} (hinj : Function.Injective emb) (i : Fin 8) :
    proj8 emb (wVar (emb i)) = Base1007.raw.getD i.val Base1007.zero := by
  apply sig8_ext <;> intro j hj
  · rw [proj8_fst_bit _ _ _ hj, wVar, lift8_hit hinj]; rfl
  · rw [proj8_snd_bit _ _ _ hj, wVar, lift8_hit hinj]; rfl

lemma proj8_var_miss {emb : Fin 8 → Fin 9} {d : Fin 9} (hmiss : ∀ i : Fin 8, emb i ≠ d) :
    proj8 emb (wVar d) = Base1007.zero := by
  apply sig8_ext <;> intro j hj
  · rw [proj8_fst_bit _ _ _ hj, wVar, lift8_miss hmiss, zero8_bit1]
  · rw [proj8_snd_bit _ _ _ hj, wVar, lift8_miss hmiss, zero8_bit2]

lemma sig8_bin_laws (a : Base1007.Sig) :
    Base1007.bin false a Base1007.one = a ∧ Base1007.bin true a Base1007.zero = a ∧
    Base1007.bin false a Base1007.zero = Base1007.zero ∧ Base1007.bin true a Base1007.one = Base1007.one ∧
    Base1007.bin false a a = a ∧ Base1007.bin true a a = a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply sig8_ext <;> intro j hj
  · rw [Base1007.bin, if_neg Bool.false_ne_true, BitVec.getLsbD_and, Base1007.one, top8_bit _ hj, Bool.and_true]
  · rw [Base1007.bin, if_neg Bool.false_ne_true, BitVec.getLsbD_and, Base1007.one, top8_bit _ hj, Bool.and_true]
  · rw [Base1007.bin, if_pos rfl, BitVec.getLsbD_or, zero8_bit1, Bool.or_false]
  · rw [Base1007.bin, if_pos rfl, BitVec.getLsbD_or, zero8_bit2, Bool.or_false]
  · rw [Base1007.bin, if_neg Bool.false_ne_true, BitVec.getLsbD_and, zero8_bit1, Bool.and_false]
  · rw [Base1007.bin, if_neg Bool.false_ne_true, BitVec.getLsbD_and, zero8_bit2, Bool.and_false]
  · rw [Base1007.bin, if_pos rfl, BitVec.getLsbD_or, Base1007.one, top8_bit _ hj, Bool.or_true]
  · rw [Base1007.bin, if_pos rfl, BitVec.getLsbD_or, Base1007.one, top8_bit _ hj, Bool.or_true]
  · rw [Base1007.bin, if_neg Bool.false_ne_true, BitVec.getLsbD_and, Bool.and_self]
  · rw [Base1007.bin, if_neg Bool.false_ne_true, BitVec.getLsbD_and, Bool.and_self]
  · rw [Base1007.bin, if_pos rfl, BitVec.getLsbD_or, Bool.or_self]
  · rw [Base1007.bin, if_pos rfl, BitVec.getLsbD_or, Bool.or_self]

lemma sig8_bin_comm (d : Bool) (a b : Base1007.Sig) :
    Base1007.bin d a b = Base1007.bin d b a := by
  cases d <;> simp [Base1007.bin, BitVec.and_comm, BitVec.or_comm]

lemma sig8_neg_laws :
    Base1007.neg Base1007.zero = Base1007.one ∧ Base1007.neg Base1007.one = Base1007.zero := by
  constructor <;> apply sig8_ext <;> intro j hj
  · rw [Base1007.neg, BitVec.getLsbD_not, zero8_bit1, Base1007.one, top8_bit _ hj]; simp [hj]
  · rw [Base1007.neg, BitVec.getLsbD_not, zero8_bit2, Base1007.one, top8_bit _ hj]; simp [hj]
  · rw [Base1007.neg, BitVec.getLsbD_not, Base1007.one, top8_bit _ hj, zero8_bit1]; simp [hj]
  · rw [Base1007.neg, BitVec.getLsbD_not, Base1007.one, top8_bit _ hj, zero8_bit2]; simp [hj]

lemma live8_proper {m t : Nat} {T : Finset Base1007.Sig} (h : Base1007.Live m t T) :
    ∀ z ∈ T, Base1007.proper z := by
  apply Base1007.Live.elimInd (h := h)
  · intro z hz
    rw [Finset.mem_singleton.mp hz]
    exact ⟨by decide, by decide⟩
  · intro _ _ U a ha _ _ ih z hz
    rcases Finset.mem_insert.mp hz with rfl | hzU
    · exact ha
    · exact ih z (Finset.mem_insert_of_mem hzU)
  · intro _ _ U a b _ ha hb _ _ _ ih z hz
    rcases Finset.mem_insert.mp hz with rfl | hz1
    · exact ha
    · rcases Finset.mem_insert.mp hz1 with rfl | hzU
      · exact hb
      · exact ih z (Finset.mem_insert_of_mem hzU)

def Feasible8 (emb : Fin 8 → Fin 9) (q : Nat) (S : Finset BF) : Prop :=
  ∃ m ≤ q, ∃ t T, Base1007.Live m t T ∧ T ⊆ S.image (proj8 emb)

lemma feasible8_mono {emb : Fin 8 → Fin 9} {q1 q2 : Nat} {S : Finset BF}
    (h : Feasible8 emb q1 S) (hq : q1 ≤ q2) : Feasible8 emb q2 S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  exact ⟨m, hm.trans hq, t, T, hl, hs⟩

lemma feasible8_subset {emb : Fin 8 → Fin 9} {q : Nat} {S1 S2 : Finset BF}
    (h : Feasible8 emb q S1) (hsub : S1.image (proj8 emb) ⊆ S2.image (proj8 emb)) :
    Feasible8 emb q S2 := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  exact ⟨m, hm, t, T, hl, hs.trans hsub⟩

lemma free8_unary {emb : Fin 8 → Fin 9} {q : Nat} {U : Finset BF} {a : BF}
    (hc : ¬ Base1007.proper (proj8 emb a))
    (h : Feasible8 emb q (insert (neg9 a) U)) : Feasible8 emb q (insert a U) := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  refine ⟨m, hm, t, T, hl, fun x hx => ?_⟩
  have hxm := hs hx
  rw [Finset.image_insert] at hxm ⊢
  rcases Finset.mem_insert.mp hxm with rfl | hxU
  · exfalso
    have hp := live8_proper hl _ hx
    have hcases : proj8 emb a = Base1007.zero ∨ proj8 emb a = Base1007.one := by
      by_cases h0 : proj8 emb a = Base1007.zero
      · exact Or.inl h0
      · by_cases h1 : proj8 emb a = Base1007.one
        · exact Or.inr h1
        · exact (hc ⟨h0, h1⟩).elim
    rw [proj8_neg] at hp
    rcases hcases with h0 | h1
    · rw [h0, sig8_neg_laws.1] at hp; exact hp.2 rfl
    · rw [h1, sig8_neg_laws.2] at hp; exact hp.1 rfl
  · exact Finset.mem_insert_of_mem hxU

lemma pull8_unary {emb : Fin 8 → Fin 9} {q : Nat} {U : Finset BF} {a : BF}
    (h : Feasible8 emb q (insert (neg9 a) U)) : Feasible8 emb (q + 1) (insert a U) := by
  by_cases hc : Base1007.proper (proj8 emb a)
  · obtain ⟨m, hm, t, T, hl, hs⟩ := h
    by_cases hna : Base1007.neg (proj8 emb a) ∈ T
    · by_cases hin : Base1007.neg (proj8 emb a) ∈ insert (proj8 emb a) (T.erase (Base1007.neg (proj8 emb a)))
      · rcases Finset.mem_insert.mp hin with heq | hmem
        · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
          have hxm := hs hx
          rw [Finset.image_insert, proj8_neg] at hxm
          rw [Finset.image_insert]
          rcases Finset.mem_insert.mp hxm with rfl | hxU
          · rw [heq]; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hxU
        · exact ((Finset.mem_erase.mp hmem).1 rfl).elim
      · refine ⟨m + 1, by omega, t + 1, insert (proj8 emb a) (T.erase (Base1007.neg (proj8 emb a))),
          Base1007.Live.unary hc hin (by rwa [Finset.insert_erase hna]), ?_⟩
        intro x hx
        rw [Finset.image_insert]
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · exact Finset.mem_insert_self _ _
        · have hxne := (Finset.mem_erase.mp hxU).1
          have hxT := (Finset.mem_erase.mp hxU).2
          have hxm := hs hxT
          rw [Finset.image_insert, proj8_neg] at hxm
          rcases Finset.mem_insert.mp hxm with heq | hxI
          · exact (hxne heq).elim
          · exact Finset.mem_insert_of_mem hxI
    · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
      have hxm := hs hx
      rw [Finset.image_insert, proj8_neg] at hxm
      rw [Finset.image_insert]
      rcases Finset.mem_insert.mp hxm with rfl | hxU
      · exact (hna hx).elim
      · exact Finset.mem_insert_of_mem hxU
  · exact feasible8_mono (free8_unary hc h) (by omega)

lemma free8_binary_left {emb : Fin 8 → Fin 9} {q : Nat} {U : Finset BF} {a b : BF} {d : Bool}
    (hc : ¬ Base1007.proper (proj8 emb a))
    (h : Feasible8 emb q (insert (bin9 d a b) U)) : Feasible8 emb q (insert a (insert b U)) := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  refine ⟨m, hm, t, T, hl, fun x hx => ?_⟩
  have hxm := hs hx
  rw [Finset.image_insert, proj8_bin] at hxm
  rw [Finset.image_insert, Finset.image_insert]
  rcases Finset.mem_insert.mp hxm with rfl | hxU
  · have hp := live8_proper hl _ hx
    have hcases : proj8 emb a = Base1007.zero ∨ proj8 emb a = Base1007.one := by
      by_cases h0 : proj8 emb a = Base1007.zero
      · exact Or.inl h0
      · by_cases h1 : proj8 emb a = Base1007.one
        · exact Or.inr h1
        · exact (hc ⟨h0, h1⟩).elim
    rcases hcases with h0 | h1 <;> cases d
    · rw [h0, sig8_bin_comm, (sig8_bin_laws _).2.2.1] at hp; exact (hp.1 rfl).elim
    · rw [h0, sig8_bin_comm, (sig8_bin_laws _).2.1]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h1, sig8_bin_comm, (sig8_bin_laws _).1]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h1, sig8_bin_comm, (sig8_bin_laws _).2.2.2.1] at hp; exact (hp.2 rfl).elim
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)

lemma free8_binary_right {emb : Fin 8 → Fin 9} {q : Nat} {U : Finset BF} {a b : BF} {d : Bool}
    (hc : ¬ Base1007.proper (proj8 emb b))
    (h : Feasible8 emb q (insert (bin9 d a b) U)) : Feasible8 emb q (insert a (insert b U)) := by
  rw [Finset.insert_comm]
  rw [bin9_comm] at h
  exact free8_binary_left hc h

lemma pull8_binary {emb : Fin 8 → Fin 9} {q : Nat} {U : Finset BF} {a b : BF} {d : Bool}
    (h : Feasible8 emb q (insert (bin9 d a b) U)) : Feasible8 emb (q + 1) (insert a (insert b U)) := by
  by_cases ha : Base1007.proper (proj8 emb a)
  · by_cases hb : Base1007.proper (proj8 emb b)
    · by_cases hab : proj8 emb a = proj8 emb b
      · obtain ⟨m, hm, t, T, hl, hs⟩ := h
        refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
        have hxm := hs hx
        rw [Finset.image_insert, proj8_bin, hab] at hxm
        rw [Finset.image_insert, Finset.image_insert]
        rcases Finset.mem_insert.mp hxm with rfl | hxU
        · cases d
          · rw [(sig8_bin_laws _).2.2.2.2.1]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · rw [(sig8_bin_laws _).2.2.2.2.2]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)
      · obtain ⟨m, hm, t, T, hl, hs⟩ := h
        let c := Base1007.bin d (proj8 emb a) (proj8 emb b)
        by_cases hcT : c ∈ T
        · by_cases hfresh : c ∈ insert (proj8 emb a) (insert (proj8 emb b) (T.erase c))
          · rcases Finset.mem_insert.mp hfresh with heq | hm1
            · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
              have hxm := hs hx
              rw [Finset.image_insert, proj8_bin] at hxm
              rw [Finset.image_insert, Finset.image_insert]
              rcases Finset.mem_insert.mp hxm with rfl | hxU
              · change c ∈ _; rw [heq]; exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)
            · rcases Finset.mem_insert.mp hm1 with heq | hmU
              · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
                have hxm := hs hx
                rw [Finset.image_insert, proj8_bin] at hxm
                rw [Finset.image_insert, Finset.image_insert]
                rcases Finset.mem_insert.mp hxm with rfl | hxU
                · change c ∈ _; rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)
              · exact ((Finset.mem_erase.mp hmU).1 rfl).elim
          · refine ⟨m + 1, by omega, t, insert (proj8 emb a) (insert (proj8 emb b) (T.erase c)),
              Base1007.Live.binary ha hb hab hfresh (by rwa [Finset.insert_erase hcT]), ?_⟩
            intro x hx
            rw [Finset.image_insert, Finset.image_insert]
            rcases Finset.mem_insert.mp hx with rfl | hx1
            · exact Finset.mem_insert_self _ _
            · rcases Finset.mem_insert.mp hx1 with rfl | hxU
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              · have hxne := (Finset.mem_erase.mp hxU).1
                have hxT := (Finset.mem_erase.mp hxU).2
                have hxm := hs hxT
                rw [Finset.image_insert, proj8_bin] at hxm
                rcases Finset.mem_insert.mp hxm with heq | hxI
                · exact (hxne heq).elim
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxI)
        · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
          have hxm := hs hx
          rw [Finset.image_insert, proj8_bin] at hxm
          rw [Finset.image_insert, Finset.image_insert]
          rcases Finset.mem_insert.mp hxm with rfl | hxU
          · exact (hcT hx).elim
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)
    · exact feasible8_mono (free8_binary_right hb h) (by omega)
  · exact feasible8_mono (free8_binary_left ha h) (by omega)

lemma not_proper8_bin_consts {a b : Base1007.Sig} (d : Bool)
    (ha : ¬ Base1007.proper a) (hb : ¬ Base1007.proper b) :
    ¬ Base1007.proper (Base1007.bin d a b) := by
  have h1 : a = Base1007.zero ∨ a = Base1007.one := by
    by_cases h0 : a = Base1007.zero; exact Or.inl h0
    by_cases h1 : a = Base1007.one; exact Or.inr h1
    exact (ha ⟨h0, h1⟩).elim
  have h2 : b = Base1007.zero ∨ b = Base1007.one := by
    by_cases h0 : b = Base1007.zero; exact Or.inl h0
    by_cases h1 : b = Base1007.one; exact Or.inr h1
    exact (hb ⟨h0, h1⟩).elim
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> cases d
  · rw [(sig8_bin_laws _).2.2.1]; exact fun h => h.1 rfl
  · rw [(sig8_bin_laws _).2.1]; exact fun h => h.1 rfl
  · rw [sig8_bin_comm, (sig8_bin_laws _).2.2.1]; exact fun h => h.1 rfl
  · rw [(sig8_bin_laws _).2.2.2.1]; exact fun h => h.2 rfl
  · rw [(sig8_bin_laws _).2.2.1]; exact fun h => h.1 rfl
  · rw [(sig8_bin_laws _).2.1]; exact fun h => h.2 rfl
  · rw [(sig8_bin_laws _).1]; exact fun h => h.2 rfl
  · rw [(sig8_bin_laws _).2.2.2.1]; exact fun h => h.2 rfl

lemma live9_feasible8 {emb : Fin 8 → Fin 9} (hF : proj8 emb F9 = Base1007.target)
    {k t : Nat} {S : Finset BF} (h : Live9 k t S) : Feasible8 emb k S := by
  apply Live9.elimInd (h := h)
  · refine ⟨0, le_refl _, 0, {Base1007.target}, Base1007.Live.stop, ?_⟩
    simp [hF]
  · intro _ _ _ _ _ _ _ ih; exact pull8_unary ih
  · intro _ _ _ _ _ _ _ _ _ _ _ ih; exact pull8_binary ih

lemma feasible8_const {emb : Fin 8 → Fin 9} (hF : proj8 emb F9 = Base1007.target)
    {k t : Nat} {S : Finset BF} (h : Live9 k t S) (a : BF) (ha : a ∈ S)
    (hca : ¬ Base1007.proper (proj8 emb a)) :
    ∃ q, q + 1 ≤ k ∧ Feasible8 emb q S := by
  revert a
  apply Live9.elimInd (h := h)
  · intro a ha hca
    rw [Finset.mem_singleton.mp ha, hF] at hca
    exact (hca ⟨by decide, by decide⟩).elim
  · intro k t U c _ _ tail ih a ha hca
    rcases Finset.mem_insert.mp ha with rfl | haU
    · exact ⟨k, le_refl _, free8_unary hca (live9_feasible8 hF tail)⟩
    · obtain ⟨q, hq, hf⟩ := ih a (Finset.mem_insert_of_mem haU) hca
      exact ⟨q + 1, by omega, pull8_unary hf⟩
  · intro k t U c e d _ _ _ _ tail ih a ha hca
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · exact ⟨k, le_refl _, free8_binary_left hca (live9_feasible8 hF tail)⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · exact ⟨k, le_refl _, free8_binary_right hca (live9_feasible8 hF tail)⟩
      · obtain ⟨q, hq, hf⟩ := ih a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q + 1, by omega, pull8_binary hf⟩

lemma feasible8_two_consts {emb : Fin 8 → Fin 9} (hF : proj8 emb F9 = Base1007.target)
    {k t : Nat} {S : Finset BF} (h : Live9 k t S) (a b : BF) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ Base1007.proper (proj8 emb a)) (hcb : ¬ Base1007.proper (proj8 emb b)) :
    ∃ q, q + 2 ≤ k ∧ Feasible8 emb q S := by
  revert a b
  apply Live9.elimInd (h := h)
  · intro a b ha hb hab _ _
    exact (hab ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)).elim
  · intro k t U c _ _ tail ih a b ha hb hab hca hcb
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      obtain ⟨q, hq, hf⟩ := feasible8_const hF tail b (Finset.mem_insert_of_mem hbU) hcb
      exact ⟨q, by omega, free8_unary hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · obtain ⟨q, hq, hf⟩ := feasible8_const hF tail a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q, by omega, free8_unary hcb hf⟩
      · obtain ⟨q, hq, hf⟩ := ih a b (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) hab hca hcb
        exact ⟨q + 1, by omega, pull8_unary hf⟩
  · intro k t U c e d _ _ _ _ tail ih a b ha hb hab hca hcb
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · have hce : ¬ Base1007.proper (proj8 emb (bin9 d a b)) := by
            rw [proj8_bin]; exact not_proper8_bin_consts d hca hcb
          obtain ⟨q, hq, hf⟩ := feasible8_const hF tail (bin9 d a b) (Finset.mem_insert_self _ _) hce
          exact ⟨q, by omega, free8_binary_left hca hf⟩
        · obtain ⟨q, hq, hf⟩ := feasible8_const hF tail b (Finset.mem_insert_of_mem hbU) hcb
          exact ⟨q, by omega, free8_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · have hce : ¬ Base1007.proper (proj8 emb (bin9 d b a)) := by
            rw [proj8_bin]; exact not_proper8_bin_consts d hcb hca
          obtain ⟨q, hq, hf⟩ := feasible8_const hF tail (bin9 d b a) (Finset.mem_insert_self _ _) hce
          exact ⟨q, by omega, free8_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · obtain ⟨q, hq, hf⟩ := feasible8_const hF tail b (Finset.mem_insert_of_mem hbU) hcb
            exact ⟨q, by omega, free8_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible8_const hF tail a (Finset.mem_insert_of_mem haU) hca
          exact ⟨q, by omega, free8_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · obtain ⟨q, hq, hf⟩ := feasible8_const hF tail a (Finset.mem_insert_of_mem haU) hca
            exact ⟨q, by omega, free8_binary_right hcb hf⟩
          · obtain ⟨q, hq, hf⟩ := ih a b (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) hab hca hcb
            exact ⟨q + 1, by omega, pull8_binary hf⟩

lemma no_feasible8_12 {emb : Fin 8 → Fin 9} {S : Finset BF}
    (hsub : ∀ φ ∈ S, proj8 emb φ = Base1007.zero ∨ proj8 emb φ ∈ Base1007.raw)
    (hf : Feasible8 emb 12 S) : False := by
  obtain ⟨m, hm, t, T, hl, hT⟩ := hf
  apply Base1007.no_live12 hm hl
  intro z hz
  obtain ⟨φ, hφS, rfl⟩ := Finset.mem_image.mp (hT hz)
  rcases hsub φ hφS with h0 | hr
  · exact ((live8_proper hl _ hz).1 h0).elim
  · exact hr

lemma no_feasible8_11_or {emb : Fin 8 → Fin 9} {S : Finset BF} {a b : Base1007.Sig}
    (ha : a ∈ Base1007.raw) (hb : b ∈ Base1007.raw)
    (hap : Base1007.proper a) (hbp : Base1007.proper b) (hab : a ≠ b)
    (hcraw : Base1007.bin true a b ∉ Base1007.raw)
    (hsub : ∀ φ ∈ S, proj8 emb φ = Base1007.zero ∨ proj8 emb φ ∈ Base1007.raw ∨ proj8 emb φ = Base1007.bin true a b)
    (hf : Feasible8 emb 11 S) : False := by
  obtain ⟨m, hm, t, T, hl, hT⟩ := hf
  let c := Base1007.bin true a b
  have hTall : ∀ z ∈ T, z ∈ Base1007.raw ∨ z = c := by
    intro z hz
    obtain ⟨φ, hφS, rfl⟩ := Finset.mem_image.mp (hT hz)
    rcases hsub φ hφS with h0 | hr | hc
    · exact ((live8_proper hl _ hz).1 h0).elim
    · exact Or.inl hr
    · exact Or.inr hc
  by_cases hcT : c ∈ T
  · let U := T.erase c
    have hUraw : ∀ z ∈ U, z ∈ Base1007.raw := by
      intro z hz
      rcases hTall z (Finset.mem_erase.mp hz).2 with hr | heq
      · exact hr
      · exact ((Finset.mem_erase.mp hz).1 heq).elim
    have hfresh : c ∉ insert a (insert b U) := by
      intro hm'
      change c ∉ Base1007.raw at hcraw
      rcases Finset.mem_insert.mp hm' with hca | hm1
      · rw [hca] at hcraw; exact hcraw ha
      · rcases Finset.mem_insert.mp hm1 with hcb | hmU
        · rw [hcb] at hcraw; exact hcraw hb
        · exact (Finset.mem_erase.mp hmU).1 rfl
    have hl' : Base1007.Live (m + 1) t (insert a (insert b U)) :=
      Base1007.Live.binary hap hbp hab hfresh (by rwa [Finset.insert_erase hcT])
    apply Base1007.no_live12 (by omega : m + 1 ≤ 12) hl'
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz1
    · exact ha
    · rcases Finset.mem_insert.mp hz1 with rfl | hzU
      · exact hb
      · exact hUraw z hzU
  · apply Base1007.no_live12 (by omega : m ≤ 12) hl
    intro z hz
    rcases hTall z hz with hr | heq
    · exact hr
    · exact (hcT (heq ▸ hz)).elim

def M7 : Nat := Base1007.Theta.mask 232
def G7 : Nat := Base1007.Theta.goal 232
def Valid7 (z : Nat) : Prop := ∀ j, 464 ≤ j → z.testBit j = false
def proper7 (z : Nat) : Prop := Valid7 z ∧ z ≠ 0 ∧ z ≠ M7
def neg7 (z : Nat) : Nat := z ^^^ M7
def bin7 (d : Bool) (a b : Nat) : Nat := if d then a ||| b else a &&& b

lemma testBit_M7 (j : Nat) : M7.testBit j = decide (j < 464) := by
  simpa [M7] using Base1007.Theta.zn 232 j

lemma valid7_zero : Valid7 0 := fun _ _ => Nat.zero_testBit _
lemma valid7_M7 : Valid7 M7 := fun j hj => by rw [testBit_M7]; simp [show ¬ j < 464 by omega]
lemma valid7_G7 : Valid7 G7 := fun j hj => by
  simp only [G7, Base1007.Theta.xo]
  simp [show ¬ j - 232 < 232 by omega]

lemma valid7_neg {a : Nat} (ha : Valid7 a) : Valid7 (neg7 a) := fun j hj => by
  rw [neg7, Nat.testBit_xor, ha j hj, testBit_M7]
  simp [show ¬ j < 464 by omega]

lemma valid7_bin {d : Bool} {a b : Nat} (ha : Valid7 a) (hb : Valid7 b) : Valid7 (bin7 d a b) := by
  cases d <;> intro j hj
  · rw [bin7, if_neg Bool.false_ne_true, Nat.testBit_and, ha j hj]; rfl
  · rw [bin7, if_pos rfl, Nat.testBit_or, ha j hj, hb j hj]; rfl

lemma neg7_laws : neg7 0 = M7 ∧ neg7 M7 = 0 := by
  constructor <;> simp [neg7]

lemma bin7_comm (d : Bool) (a b : Nat) : bin7 d a b = bin7 d b a := by
  cases d <;> simp [bin7, Nat.and_comm, Nat.or_comm]

lemma bin7_laws {a : Nat} (ha : Valid7 a) :
    bin7 false a M7 = a ∧ bin7 true a 0 = a ∧
    bin7 false a 0 = 0 ∧ bin7 true a M7 = M7 ∧
    bin7 false a a = a ∧ bin7 true a a = a := by
  have h1 : a &&& M7 = a := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_M7]
    by_cases hj : j < 464
    · simp [hj]
    · simp [hj, ha j (by omega)]
  have h2 : a ||| M7 = M7 := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_M7]
    by_cases hj : j < 464
    · simp [hj]
    · simp [hj, ha j (by omega)]
  simp [bin7, h1, h2]

lemma G7_proper : proper7 G7 :=
  ⟨valid7_G7, by
    intro h
    have ht := congrArg (fun n => n.testBit 232) h
    rw [G7, Base1007.Theta.xo] at ht
    simp at ht, by
    intro h
    have ht := congrArg (fun n => n.testBit 0) h
    rw [G7, M7, Base1007.Theta.xo, Base1007.Theta.zn] at ht
    simp at ht⟩

def Live7 (k t : Nat) (S : Finset Nat) : Prop :=
  ∀ (P : Nat → Nat → Finset Nat → Prop),
    P 0 0 {G7} →
    (∀ {k t : Nat} {U : Finset Nat} {a : Nat}, proper7 a → neg7 a ∉ insert a U →
      P k t (insert (neg7 a) U) → P (k + 1) (t + 1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset Nat} {a b : Nat} {d : Bool}, proper7 a → proper7 b → a ≠ b →
      bin7 d a b ∉ insert a (insert b U) →
      P k t (insert (bin7 d a b) U) → P (k + 1) t (insert a (insert b U))) →
    P k t S

theorem Live7.stop : Live7 0 0 {G7} := fun _ hs _ _ => hs
theorem Live7.unary {k t : Nat} {U : Finset Nat} {a : Nat}
    (ha : proper7 a) (hf : neg7 a ∉ insert a U) (tail : Live7 k t (insert (neg7 a) U)) :
    Live7 (k + 1) (t + 1) (insert a U) :=
  fun P hs hu hb => hu ha hf (tail P hs hu hb)
theorem Live7.binary {k t : Nat} {U : Finset Nat} {a b : Nat} {d : Bool}
    (ha : proper7 a) (hb : proper7 b) (hab : a ≠ b) (hf : bin7 d a b ∉ insert a (insert b U))
    (tail : Live7 k t (insert (bin7 d a b) U)) :
    Live7 (k + 1) t (insert a (insert b U)) :=
  fun P hs hu hb' => hb' ha hb hab hf (tail P hs hu hb')

theorem Live7.elimInd {P : Nat → Nat → Finset Nat → Prop}
    (stop : P 0 0 {G7})
    (unary : ∀ {k t : Nat} {U : Finset Nat} {a : Nat}, proper7 a → neg7 a ∉ insert a U →
      Live7 k t (insert (neg7 a) U) → P k t (insert (neg7 a) U) → P (k + 1) (t + 1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Nat} {a b : Nat} {d : Bool}, proper7 a → proper7 b → a ≠ b →
      bin7 d a b ∉ insert a (insert b U) →
      Live7 k t (insert (bin7 d a b) U) → P k t (insert (bin7 d a b) U) → P (k + 1) t (insert a (insert b U)))
    {k t : Nat} {S : Finset Nat} (h : Live7 k t S) : P k t S := by
  apply And.right (a := Live7 k t S)
  apply h (fun k t S => Live7 k t S ∧ P k t S)
  · exact ⟨Live7.stop, stop⟩
  · intro k t U a ha hf prev; exact ⟨Live7.unary ha hf prev.1, unary ha hf prev.1 prev.2⟩
  · intro k t U a b d ha hb hab hf prev; exact ⟨Live7.binary ha hb hab hf prev.1, binary ha hb hab hf prev.1 prev.2⟩

lemma live7_proper {k t : Nat} {S : Finset Nat} (h : Live7 k t S) : ∀ z ∈ S, proper7 z := by
  apply Live7.elimInd (h := h)
  · intro z hz; rw [Finset.mem_singleton.mp hz]; exact G7_proper
  · intro _ _ U a ha _ _ ih z hz
    rcases Finset.mem_insert.mp hz with rfl | hzU
    · exact ha
    · exact ih z (Finset.mem_insert_of_mem hzU)
  · intro _ _ U a b _ ha hb _ _ _ ih z hz
    rcases Finset.mem_insert.mp hz with rfl | hz1
    · exact ha
    · rcases Finset.mem_insert.mp hz1 with rfl | hzU
      · exact hb
      · exact ih z (Finset.mem_insert_of_mem hzU)

lemma nodup_perm_of_toFinset_eq {L1 L2 : List Nat}
    (h1 : L1.Nodup) (h2 : L2.Nodup) (heq : L1.toFinset = L2.toFinset) : L1.Perm L2 := by
  rw [List.perm_ext_iff_of_nodup h1 h2]
  intro x
  rw [← List.mem_toFinset, heq, List.mem_toFinset]

lemma live7_to_run {k t : Nat} {S : Finset Nat} (h : Live7 k t S) :
    ∀ L : List Nat, L.Nodup → L.toFinset = S →
      Base1007.Theta.NatRun M7 G7 k L := by
  apply Live7.elimInd (h := h)
  · intro L hnd htf
    have hp : [G7].Perm L := nodup_perm_of_toFinset_eq (List.nodup_singleton G7) hnd (by simpa using htf.symm)
    exact Base1007.Theta.Run.perm hp Base1007.Theta.Run.done
  · intro k t U a ha hf _ ih L hnd htf
    let sa : Bool := decide (a ∈ U)
    let rest := (U.erase a).toList
    have hrest_nd : rest.Nodup := Finset.nodup_toList _
    have ha_rest : a ∉ rest := by simp [rest]
    have hna_rest : neg7 a ∉ rest := by
      intro hm
      have hmU : neg7 a ∈ U := (Finset.mem_erase.mp (Finset.mem_toList.mp hm)).2
      exact hf (Finset.mem_insert_of_mem hmU)
    have hna_ne_a : neg7 a ≠ a := fun e => hf (by rw [e]; exact Finset.mem_insert_self _ _)
    have hp : (a :: rest).Perm L := by
      apply nodup_perm_of_toFinset_eq (List.nodup_cons.mpr ⟨ha_rest, hrest_nd⟩) hnd
      rw [htf]
      ext x
      simp [rest]
    have hkept_nd : (neg7 a :: Base1007.Theta.kept sa a rest).Nodup := by
      cases hsa : sa
      · simp [Base1007.Theta.kept, hna_rest, hrest_nd]
      · simp [Base1007.Theta.kept, hna_ne_a, hna_rest, ha_rest, hrest_nd]
    have hkept_tf : (neg7 a :: Base1007.Theta.kept sa a rest).toFinset = insert (neg7 a) U := by
      ext x
      cases hsa : sa
      · have haU : a ∉ U := by simpa [sa] using hsa
        simp only [Base1007.Theta.kept, Bool.false_eq_true, ite_false, List.toFinset_cons,
          Finset.mem_insert, List.mem_toFinset, rest, Finset.mem_toList, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨_, hxU⟩)
          · exact Or.inl rfl
          · exact Or.inr hxU
        · rintro (rfl | hxU)
          · exact Or.inl rfl
          · exact Or.inr ⟨fun e => haU (e ▸ hxU), hxU⟩
      · have haU : a ∈ U := by simpa [sa] using hsa
        simp only [Base1007.Theta.kept, ite_true, List.toFinset_cons,
          Finset.mem_insert, List.mem_toFinset, rest, Finset.mem_toList, Finset.mem_erase]
        constructor
        · rintro (rfl | rfl | ⟨_, hxU⟩)
          · exact Or.inl rfl
          · exact Or.inr haU
          · exact Or.inr hxU
        · rintro (rfl | hxU)
          · exact Or.inl rfl
          · by_cases hxa : x = a
            · exact Or.inr (Or.inl hxa)
            · exact Or.inr (Or.inr ⟨hxa, hxU⟩)
    have hdone := ih _ hkept_nd hkept_tf
    exact Base1007.Theta.Run.perm hp (Base1007.Theta.Run.one true sa hdone)
  · intro k t U a b d ha hb hab hf _ ih L hnd htf
    let sa : Bool := decide (a ∈ U)
    let sb : Bool := decide (b ∈ U)
    let rest := ((U.erase a).erase b).toList
    have hrest_nd : rest.Nodup := Finset.nodup_toList _
    have ha_rest : a ∉ rest := by simp [rest]
    have hb_rest : b ∉ rest := by simp [rest]
    have hc_rest : bin7 d a b ∉ rest := by
      intro hm
      have hmU : bin7 d a b ∈ U := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_toList.mp hm)).2).2
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmU))
    have hc_ne_a : bin7 d a b ≠ a := fun e => hf (by rw [e]; exact Finset.mem_insert_self _ _)
    have hc_ne_b : bin7 d a b ≠ b := fun e => hf (by rw [e]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hp : (a :: b :: rest).Perm L := by
      apply nodup_perm_of_toFinset_eq
        (List.nodup_cons.mpr ⟨by simp [hab, ha_rest], List.nodup_cons.mpr ⟨hb_rest, hrest_nd⟩⟩) hnd
      rw [htf]
      ext x
      simp [rest, Finset.mem_toList]
      tauto
    have hkept_nd : (bin7 d a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).Nodup := by
      cases hsa : sa <;> cases hsb : sb <;>
        simp [Base1007.Theta.kept, hc_rest, hc_ne_a, hc_ne_b, hab, ha_rest, hb_rest, hrest_nd]
    have hkept_tf :
        (bin7 d a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).toFinset =
        insert (bin7 d a b) U := by
      ext x
      cases hsa : sa <;> cases hsb : sb
      · have haU : a ∉ U := by simpa [sa] using hsa
        have hbU : b ∉ U := by simpa [sb] using hsb
        simp only [Base1007.Theta.kept, Bool.false_eq_true, ite_false, List.toFinset_cons,
          Finset.mem_insert, List.mem_toFinset, rest, Finset.mem_toList, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨_, _, hxU⟩); exact Or.inl rfl; exact Or.inr hxU
        · rintro (rfl | hxU); exact Or.inl rfl
          exact Or.inr ⟨fun e => hbU (e ▸ hxU), fun e => haU (e ▸ hxU), hxU⟩
      · have haU : a ∉ U := by simpa [sa] using hsa
        have hbU : b ∈ U := by simpa [sb] using hsb
        simp only [Base1007.Theta.kept, Bool.false_eq_true, ite_false, ite_true, List.toFinset_cons,
          Finset.mem_insert, List.mem_toFinset, rest, Finset.mem_toList, Finset.mem_erase]
        constructor
        · rintro (rfl | rfl | ⟨_, _, hxU⟩); exact Or.inl rfl; exact Or.inr hbU; exact Or.inr hxU
        · rintro (rfl | hxU); exact Or.inl rfl
          by_cases hxb : x = b
          · exact Or.inr (Or.inl hxb)
          · exact Or.inr (Or.inr ⟨hxb, fun e => haU (e ▸ hxU), hxU⟩)
      · have haU : a ∈ U := by simpa [sa] using hsa
        have hbU : b ∉ U := by simpa [sb] using hsb
        simp only [Base1007.Theta.kept, Bool.false_eq_true, ite_false, ite_true, List.toFinset_cons,
          Finset.mem_insert, List.mem_toFinset, rest, Finset.mem_toList, Finset.mem_erase]
        constructor
        · rintro (rfl | rfl | ⟨_, _, hxU⟩); exact Or.inl rfl; exact Or.inr haU; exact Or.inr hxU
        · rintro (rfl | hxU); exact Or.inl rfl
          by_cases hxa : x = a
          · exact Or.inr (Or.inl hxa)
          · exact Or.inr (Or.inr ⟨fun e => hbU (e ▸ hxU), hxa, hxU⟩)
      · have haU : a ∈ U := by simpa [sa] using hsa
        have hbU : b ∈ U := by simpa [sb] using hsb
        simp only [Base1007.Theta.kept, ite_true, List.toFinset_cons,
          Finset.mem_insert, List.mem_toFinset, rest, Finset.mem_toList, Finset.mem_erase]
        constructor
        · rintro (rfl | rfl | rfl | ⟨_, _, hxU⟩)
          · exact Or.inl rfl
          · exact Or.inr haU
          · exact Or.inr hbU
          · exact Or.inr hxU
        · rintro (rfl | hxU); exact Or.inl rfl
          by_cases hxa : x = a
          · exact Or.inr (Or.inl hxa)
          · by_cases hxb : x = b
            · exact Or.inr (Or.inr (Or.inl hxb))
            · exact Or.inr (Or.inr (Or.inr ⟨hxb, hxa, hxU⟩))
    have hdone := ih _ hkept_nd hkept_tf
    cases d
    · exact Base1007.Theta.Run.perm hp (Base1007.Theta.Run.two true sa sb hdone)
    · exact Base1007.Theta.Run.perm hp (Base1007.Theta.Run.two false sa sb hdone)

def inp7 (j : Nat) (i : Fin 7) : Bool := (Base1007.Theta.xs517.getD i.val 0).testBit j

def lift7 (emb : Fin 7 → Fin 9) (y : Fin 7 → Bool) (v : Fin 9) : Bool :=
  (List.finRange 7).any (fun i => decide (emb i = v) && y i)

lemma lift7_hit {emb : Fin 7 → Fin 9} (hinj : Function.Injective emb) (y : Fin 7 → Bool) (i : Fin 7) :
    lift7 emb y (emb i) = y i := by
  unfold lift7
  cases hy : y i
  · rw [Bool.eq_false_iff]
    intro h
    obtain ⟨j, _, hj⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    have hji : j = i := hinj hj.1
    subst hji
    rw [hy] at hj
    exact Bool.false_ne_true hj.2
  · apply List.any_eq_true.mpr
    exact ⟨i, List.mem_finRange i, by simp [hy]⟩

lemma lift7_miss {emb : Fin 7 → Fin 9} {d : Fin 9} (hmiss : ∀ i : Fin 7, emb i ≠ d) (y : Fin 7 → Bool) :
    lift7 emb y d = false := by
  unfold lift7
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨j, _, hj⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
  exact hmiss j hj.1

def proj7 (emb : Fin 7 → Fin 9) (φ : BF) : Nat :=
  packNat (fun j => φ (lift7 emb (inp7 j))) 464

lemma proj7_testBit (emb : Fin 7 → Fin 9) (φ : BF) (j : Nat) :
    (proj7 emb φ).testBit j = (decide (j < 464) && φ (lift7 emb (inp7 j))) :=
  packNat_testBit _ 464 j

lemma proj7_valid (emb : Fin 7 → Fin 9) (φ : BF) : Valid7 (proj7 emb φ) := by
  intro j hj
  rw [proj7_testBit]
  simp [show ¬ j < 464 by omega]

lemma proj7_false (emb : Fin 7 → Fin 9) : proj7 emb cFalse = 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  simp [proj7_testBit, cFalse]

lemma proj7_true (emb : Fin 7 → Fin 9) : proj7 emb cTrue = M7 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [proj7_testBit, testBit_M7]; simp [cTrue]

lemma proj7_neg (emb : Fin 7 → Fin 9) (φ : BF) : proj7 emb (neg9 φ) = neg7 (proj7 emb φ) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [neg7, Nat.testBit_xor, proj7_testBit, proj7_testBit, testBit_M7]
  by_cases hj : j < 464 <;> simp [hj, neg9]

lemma proj7_bin (emb : Fin 7 → Fin 9) (d : Bool) (φ ψ : BF) :
    proj7 emb (bin9 d φ ψ) = bin7 d (proj7 emb φ) (proj7 emb ψ) := by
  cases d <;> apply Nat.eq_of_testBit_eq <;> intro j
  · simp only [bin7, Bool.false_eq_true, ite_false, Nat.testBit_and, proj7_testBit, bin9]
    by_cases hj : j < 464 <;> simp [hj]
  · simp only [bin7, ite_true, Nat.testBit_or, proj7_testBit, bin9]
    by_cases hj : j < 464 <;> simp [hj]

lemma xs517_le_q7 : ∀ i : Fin 7, Base1007.Theta.xs517.getD i.val 0 ≤ Base1007.Theta.q7 := by
  decide +kernel

lemma xs517_valid (i : Fin 7) : Valid7 (Base1007.Theta.xs517.getD i.val 0) := by
  intro j hj
  have hle := xs517_le_q7 i
  rw [Base1007.Theta.vb] at hle
  have hlt : Base1007.Theta.xs517.getD i.val 0 < 2 ^ 464 := by
    have hq : Base1007.Theta.mask 232 = 2 ^ 464 - 1 := rfl
    rw [hq] at hle
    have hp : 0 < 2 ^ 464 := by positivity
    omega
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hj))

lemma proj7_var_hit {emb : Fin 7 → Fin 9} (hinj : Function.Injective emb) (i : Fin 7) :
    proj7 emb (wVar (emb i)) = Base1007.Theta.xs517.getD i.val 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [proj7_testBit]
  by_cases hj : j < 464
  · simp [hj, wVar, lift7_hit hinj, inp7]
  · simp only [hj, decide_false, Bool.false_and]
    exact (xs517_valid i j (by omega)).symm

lemma proj7_var_miss {emb : Fin 7 → Fin 9} {d : Fin 9} (hmiss : ∀ i : Fin 7, emb i ≠ d) :
    proj7 emb (wVar d) = 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [proj7_testBit]
  simp [wVar, lift7_miss hmiss]

def Feasible7 (emb : Fin 7 → Fin 9) (q : Nat) (S : Finset BF) : Prop :=
  ∃ m ≤ q, ∃ t T, Live7 m t T ∧ T ⊆ S.image (proj7 emb)

lemma feasible7_mono {emb : Fin 7 → Fin 9} {q1 q2 : Nat} {S : Finset BF}
    (h : Feasible7 emb q1 S) (hq : q1 ≤ q2) : Feasible7 emb q2 S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  exact ⟨m, hm.trans hq, t, T, hl, hs⟩

lemma free7_unary {emb : Fin 7 → Fin 9} {q : Nat} {U : Finset BF} {a : BF}
    (hc : ¬ proper7 (proj7 emb a))
    (h : Feasible7 emb q (insert (neg9 a) U)) : Feasible7 emb q (insert a U) := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  refine ⟨m, hm, t, T, hl, fun x hx => ?_⟩
  have hxm := hs hx
  rw [Finset.image_insert] at hxm ⊢
  rcases Finset.mem_insert.mp hxm with rfl | hxU
  · exfalso
    have hp := live7_proper hl _ hx
    have hv := proj7_valid emb a
    have hcases : proj7 emb a = 0 ∨ proj7 emb a = M7 := by
      by_cases h0 : proj7 emb a = 0; exact Or.inl h0
      by_cases h1 : proj7 emb a = M7; exact Or.inr h1
      exact (hc ⟨hv, h0, h1⟩).elim
    rw [proj7_neg] at hp
    rcases hcases with h0 | h1
    · rw [h0, neg7_laws.1] at hp; exact hp.2.2 rfl
    · rw [h1, neg7_laws.2] at hp; exact hp.2.1 rfl
  · exact Finset.mem_insert_of_mem hxU

lemma pull7_unary {emb : Fin 7 → Fin 9} {q : Nat} {U : Finset BF} {a : BF}
    (h : Feasible7 emb q (insert (neg9 a) U)) : Feasible7 emb (q + 1) (insert a U) := by
  by_cases hc : proper7 (proj7 emb a)
  · obtain ⟨m, hm, t, T, hl, hs⟩ := h
    by_cases hna : neg7 (proj7 emb a) ∈ T
    · by_cases hin : neg7 (proj7 emb a) ∈ insert (proj7 emb a) (T.erase (neg7 (proj7 emb a)))
      · rcases Finset.mem_insert.mp hin with heq | hmem
        · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
          have hxm := hs hx
          rw [Finset.image_insert, proj7_neg] at hxm
          rw [Finset.image_insert]
          rcases Finset.mem_insert.mp hxm with rfl | hxU
          · rw [heq]; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hxU
        · exact ((Finset.mem_erase.mp hmem).1 rfl).elim
      · refine ⟨m + 1, by omega, t + 1, insert (proj7 emb a) (T.erase (neg7 (proj7 emb a))),
          Live7.unary hc hin (by rwa [Finset.insert_erase hna]), ?_⟩
        intro x hx
        rw [Finset.image_insert]
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · exact Finset.mem_insert_self _ _
        · have hxne := (Finset.mem_erase.mp hxU).1
          have hxT := (Finset.mem_erase.mp hxU).2
          have hxm := hs hxT
          rw [Finset.image_insert, proj7_neg] at hxm
          rcases Finset.mem_insert.mp hxm with heq | hxI
          · exact (hxne heq).elim
          · exact Finset.mem_insert_of_mem hxI
    · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
      have hxm := hs hx
      rw [Finset.image_insert, proj7_neg] at hxm
      rw [Finset.image_insert]
      rcases Finset.mem_insert.mp hxm with rfl | hxU
      · exact (hna hx).elim
      · exact Finset.mem_insert_of_mem hxU
  · exact feasible7_mono (free7_unary hc h) (by omega)

lemma free7_binary_left {emb : Fin 7 → Fin 9} {q : Nat} {U : Finset BF} {a b : BF} {d : Bool}
    (hc : ¬ proper7 (proj7 emb a))
    (h : Feasible7 emb q (insert (bin9 d a b) U)) : Feasible7 emb q (insert a (insert b U)) := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  refine ⟨m, hm, t, T, hl, fun x hx => ?_⟩
  have hxm := hs hx
  rw [Finset.image_insert, proj7_bin] at hxm
  rw [Finset.image_insert, Finset.image_insert]
  rcases Finset.mem_insert.mp hxm with rfl | hxU
  · have hp := live7_proper hl _ hx
    have hv := proj7_valid emb a
    have hvb := proj7_valid emb b
    have hcases : proj7 emb a = 0 ∨ proj7 emb a = M7 := by
      by_cases h0 : proj7 emb a = 0; exact Or.inl h0
      by_cases h1 : proj7 emb a = M7; exact Or.inr h1
      exact (hc ⟨hv, h0, h1⟩).elim
    rcases hcases with h0 | h1 <;> cases d
    · rw [h0, bin7_comm, (bin7_laws hvb).2.2.1] at hp; exact (hp.2.1 rfl).elim
    · rw [h0, bin7_comm, (bin7_laws hvb).2.1]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h1, bin7_comm, (bin7_laws hvb).1]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h1, bin7_comm, (bin7_laws hvb).2.2.2.1] at hp; exact (hp.2.2 rfl).elim
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)

lemma free7_binary_right {emb : Fin 7 → Fin 9} {q : Nat} {U : Finset BF} {a b : BF} {d : Bool}
    (hc : ¬ proper7 (proj7 emb b))
    (h : Feasible7 emb q (insert (bin9 d a b) U)) : Feasible7 emb q (insert a (insert b U)) := by
  rw [Finset.insert_comm]
  rw [bin9_comm] at h
  exact free7_binary_left hc h

lemma pull7_binary {emb : Fin 7 → Fin 9} {q : Nat} {U : Finset BF} {a b : BF} {d : Bool}
    (h : Feasible7 emb q (insert (bin9 d a b) U)) : Feasible7 emb (q + 1) (insert a (insert b U)) := by
  by_cases ha : proper7 (proj7 emb a)
  · by_cases hb : proper7 (proj7 emb b)
    · by_cases hab : proj7 emb a = proj7 emb b
      · obtain ⟨m, hm, t, T, hl, hs⟩ := h
        refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
        have hxm := hs hx
        rw [Finset.image_insert, proj7_bin, hab] at hxm
        rw [Finset.image_insert, Finset.image_insert]
        rcases Finset.mem_insert.mp hxm with rfl | hxU
        · cases d
          · rw [(bin7_laws hb.1).2.2.2.2.1]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · rw [(bin7_laws hb.1).2.2.2.2.2]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)
      · obtain ⟨m, hm, t, T, hl, hs⟩ := h
        let c := bin7 d (proj7 emb a) (proj7 emb b)
        by_cases hcT : c ∈ T
        · by_cases hfresh : c ∈ insert (proj7 emb a) (insert (proj7 emb b) (T.erase c))
          · rcases Finset.mem_insert.mp hfresh with heq | hm1
            · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
              have hxm := hs hx
              rw [Finset.image_insert, proj7_bin] at hxm
              rw [Finset.image_insert, Finset.image_insert]
              rcases Finset.mem_insert.mp hxm with rfl | hxU
              · change c ∈ _; rw [heq]; exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)
            · rcases Finset.mem_insert.mp hm1 with heq | hmU
              · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
                have hxm := hs hx
                rw [Finset.image_insert, proj7_bin] at hxm
                rw [Finset.image_insert, Finset.image_insert]
                rcases Finset.mem_insert.mp hxm with rfl | hxU
                · change c ∈ _; rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)
              · exact ((Finset.mem_erase.mp hmU).1 rfl).elim
          · refine ⟨m + 1, by omega, t, insert (proj7 emb a) (insert (proj7 emb b) (T.erase c)),
              Live7.binary ha hb hab hfresh (by rwa [Finset.insert_erase hcT]), ?_⟩
            intro x hx
            rw [Finset.image_insert, Finset.image_insert]
            rcases Finset.mem_insert.mp hx with rfl | hx1
            · exact Finset.mem_insert_self _ _
            · rcases Finset.mem_insert.mp hx1 with rfl | hxU
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              · have hxne := (Finset.mem_erase.mp hxU).1
                have hxT := (Finset.mem_erase.mp hxU).2
                have hxm := hs hxT
                rw [Finset.image_insert, proj7_bin] at hxm
                rcases Finset.mem_insert.mp hxm with heq | hxI
                · exact (hxne heq).elim
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxI)
        · refine ⟨m, by omega, t, T, hl, fun x hx => ?_⟩
          have hxm := hs hx
          rw [Finset.image_insert, proj7_bin] at hxm
          rw [Finset.image_insert, Finset.image_insert]
          rcases Finset.mem_insert.mp hxm with rfl | hxU
          · exact (hcT hx).elim
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)
    · exact feasible7_mono (free7_binary_right hb h) (by omega)
  · exact feasible7_mono (free7_binary_left ha h) (by omega)

lemma not_proper7_bin_consts {a b : Nat} (d : Bool) (hva : Valid7 a) (hvb : Valid7 b)
    (ha : ¬ proper7 a) (hb : ¬ proper7 b) : ¬ proper7 (bin7 d a b) := by
  have h1 : a = 0 ∨ a = M7 := by
    by_cases h0 : a = 0; exact Or.inl h0
    by_cases h1 : a = M7; exact Or.inr h1
    exact (ha ⟨hva, h0, h1⟩).elim
  have h2 : b = 0 ∨ b = M7 := by
    by_cases h0 : b = 0; exact Or.inl h0
    by_cases h1 : b = M7; exact Or.inr h1
    exact (hb ⟨hvb, h0, h1⟩).elim
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> cases d
  · rw [(bin7_laws valid7_zero).2.2.1]; exact fun h => h.2.1 rfl
  · rw [(bin7_laws valid7_zero).2.1]; exact fun h => h.2.1 rfl
  · rw [bin7_comm, (bin7_laws valid7_M7).2.2.1]; exact fun h => h.2.1 rfl
  · rw [(bin7_laws valid7_zero).2.2.2.1]; exact fun h => h.2.2 rfl
  · rw [(bin7_laws valid7_M7).2.2.1]; exact fun h => h.2.1 rfl
  · rw [(bin7_laws valid7_M7).2.1]; exact fun h => h.2.2 rfl
  · rw [(bin7_laws valid7_M7).1]; exact fun h => h.2.2 rfl
  · rw [(bin7_laws valid7_M7).2.2.2.1]; exact fun h => h.2.2 rfl

lemma live9_feasible7 {emb : Fin 7 → Fin 9} (hF : proj7 emb F9 = G7)
    {k t : Nat} {S : Finset BF} (h : Live9 k t S) : Feasible7 emb k S := by
  apply Live9.elimInd (h := h)
  · refine ⟨0, le_refl _, 0, {G7}, Live7.stop, ?_⟩
    simp [hF]
  · intro _ _ _ _ _ _ _ ih; exact pull7_unary ih
  · intro _ _ _ _ _ _ _ _ _ _ _ ih; exact pull7_binary ih

lemma feasible7_const {emb : Fin 7 → Fin 9} (hF : proj7 emb F9 = G7)
    {k t : Nat} {S : Finset BF} (h : Live9 k t S) (a : BF) (ha : a ∈ S)
    (hca : ¬ proper7 (proj7 emb a)) :
    ∃ q, q + 1 ≤ k ∧ Feasible7 emb q S := by
  revert a
  apply Live9.elimInd (h := h)
  · intro a ha hca
    rw [Finset.mem_singleton.mp ha, hF] at hca
    exact (hca G7_proper).elim
  · intro k t U c _ _ tail ih a ha hca
    rcases Finset.mem_insert.mp ha with rfl | haU
    · exact ⟨k, le_refl _, free7_unary hca (live9_feasible7 hF tail)⟩
    · obtain ⟨q, hq, hf⟩ := ih a (Finset.mem_insert_of_mem haU) hca
      exact ⟨q + 1, by omega, pull7_unary hf⟩
  · intro k t U c e d _ _ _ _ tail ih a ha hca
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · exact ⟨k, le_refl _, free7_binary_left hca (live9_feasible7 hF tail)⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · exact ⟨k, le_refl _, free7_binary_right hca (live9_feasible7 hF tail)⟩
      · obtain ⟨q, hq, hf⟩ := ih a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q + 1, by omega, pull7_binary hf⟩

lemma feasible7_two_consts {emb : Fin 7 → Fin 9} (hF : proj7 emb F9 = G7)
    {k t : Nat} {S : Finset BF} (h : Live9 k t S) (a b : BF) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ proper7 (proj7 emb a)) (hcb : ¬ proper7 (proj7 emb b)) :
    ∃ q, q + 2 ≤ k ∧ Feasible7 emb q S := by
  revert a b
  apply Live9.elimInd (h := h)
  · intro a b ha hb hab _ _
    exact (hab ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)).elim
  · intro k t U c _ _ tail ih a b ha hb hab hca hcb
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      obtain ⟨q, hq, hf⟩ := feasible7_const hF tail b (Finset.mem_insert_of_mem hbU) hcb
      exact ⟨q, by omega, free7_unary hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · obtain ⟨q, hq, hf⟩ := feasible7_const hF tail a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q, by omega, free7_unary hcb hf⟩
      · obtain ⟨q, hq, hf⟩ := ih a b (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) hab hca hcb
        exact ⟨q + 1, by omega, pull7_unary hf⟩
  · intro k t U c e d _ _ _ _ tail ih a b ha hb hab hca hcb
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · have hce : ¬ proper7 (proj7 emb (bin9 d a b)) := by
            rw [proj7_bin]; exact not_proper7_bin_consts d (proj7_valid _ _) (proj7_valid _ _) hca hcb
          obtain ⟨q, hq, hf⟩ := feasible7_const hF tail (bin9 d a b) (Finset.mem_insert_self _ _) hce
          exact ⟨q, by omega, free7_binary_left hca hf⟩
        · obtain ⟨q, hq, hf⟩ := feasible7_const hF tail b (Finset.mem_insert_of_mem hbU) hcb
          exact ⟨q, by omega, free7_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · have hce : ¬ proper7 (proj7 emb (bin9 d b a)) := by
            rw [proj7_bin]; exact not_proper7_bin_consts d (proj7_valid _ _) (proj7_valid _ _) hcb hca
          obtain ⟨q, hq, hf⟩ := feasible7_const hF tail (bin9 d b a) (Finset.mem_insert_self _ _) hce
          exact ⟨q, by omega, free7_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · obtain ⟨q, hq, hf⟩ := feasible7_const hF tail b (Finset.mem_insert_of_mem hbU) hcb
            exact ⟨q, by omega, free7_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible7_const hF tail a (Finset.mem_insert_of_mem haU) hca
          exact ⟨q, by omega, free7_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · obtain ⟨q, hq, hf⟩ := feasible7_const hF tail a (Finset.mem_insert_of_mem haU) hca
            exact ⟨q, by omega, free7_binary_right hcb hf⟩
          · obtain ⟨q, hq, hf⟩ := ih a b (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) hab hca hcb
            exact ⟨q + 1, by omega, pull7_binary hf⟩

lemma feasible7_three_consts {emb : Fin 7 → Fin 9} (hF : proj7 emb F9 = G7)
    {k t : Nat} {S : Finset BF} (h : Live9 k t S) (a b c : BF)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hca : ¬ proper7 (proj7 emb a)) (hcb : ¬ proper7 (proj7 emb b)) (hcc : ¬ proper7 (proj7 emb c)) :
    ∃ q, q + 3 ≤ k ∧ Feasible7 emb q S := by
  revert a b c
  apply Live9.elimInd (h := h)
  · intro a b c ha hb _ hab _ _ _ _ _
    exact (hab ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)).elim
  · intro k t U x _ _ tail ih a b c ha hb hc hab hac hbc hca hcb hcc
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      have hcU : c ∈ U := (Finset.mem_insert.mp hc).resolve_left hac.symm
      obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail b c
        (Finset.mem_insert_of_mem hbU) (Finset.mem_insert_of_mem hcU) hbc hcb hcc
      exact ⟨q, by omega, free7_unary hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · have hcU : c ∈ U := (Finset.mem_insert.mp hc).resolve_left hbc.symm
        obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail a c
          (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hcU) hac hca hcc
        exact ⟨q, by omega, free7_unary hcb hf⟩
      · rcases Finset.mem_insert.mp hc with rfl | hcU
        · obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail a b
            (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) hab hca hcb
          exact ⟨q, by omega, free7_unary hcc hf⟩
        · obtain ⟨q, hq, hf⟩ := ih a b c
            (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) (Finset.mem_insert_of_mem hcU)
            hab hac hbc hca hcb hcc
          exact ⟨q + 1, by omega, pull7_unary hf⟩
  · intro k t U x y d _ _ hxy hfr tail ih a b c ha hb hc hab hac hbc hca hcb hcc
    have pairCase : ∀ (p1 p2 p3 : BF), p1 = x → p2 = y → p3 ∈ U →
        ¬ proper7 (proj7 emb p1) → ¬ proper7 (proj7 emb p2) → ¬ proper7 (proj7 emb p3) →
        ∃ q, q + 3 ≤ k + 1 ∧ Feasible7 emb q (insert x (insert y U)) := by
      intro p1 p2 p3 hp1 hp2 hp3 hcp1 hcp2 hcp3
      subst hp1 hp2
      have hz : ¬ proper7 (proj7 emb (bin9 d p1 p2)) := by
        rw [proj7_bin]; exact not_proper7_bin_consts d (proj7_valid _ _) (proj7_valid _ _) hcp1 hcp2
      have hne : bin9 d p1 p2 ≠ p3 := fun e => hfr (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp3))
      obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail (bin9 d p1 p2) p3
        (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hp3) hne hz hcp3
      exact ⟨q, by omega, free7_binary_left hcp1 hf⟩
    have pairCaseR : ∀ (p1 p2 p3 : BF), p1 = y → p2 = x → p3 ∈ U →
        ¬ proper7 (proj7 emb p1) → ¬ proper7 (proj7 emb p2) → ¬ proper7 (proj7 emb p3) →
        ∃ q, q + 3 ≤ k + 1 ∧ Feasible7 emb q (insert x (insert y U)) := by
      intro p1 p2 p3 hp1 hp2 hp3 hcp1 hcp2 hcp3
      exact pairCase p2 p1 p3 hp2 hp1 hp3 hcp2 hcp1 hcp3
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · have hcU : c ∈ U := ((Finset.mem_insert.mp hc).resolve_left hac.symm |> Finset.mem_insert.mp).resolve_left hbc.symm
          exact pairCase a b c rfl rfl hcU hca hcb hcc
        · rcases Finset.mem_insert.mp hc with hcEq | hc1
          · exact (hac hcEq.symm).elim
          · rcases Finset.mem_insert.mp hc1 with rfl | hcU
            · exact pairCase a c b rfl rfl hbU hca hcc hcb
            · obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail b c
                (Finset.mem_insert_of_mem hbU) (Finset.mem_insert_of_mem hcU) hbc hcb hcc
              exact ⟨q, by omega, free7_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · have hcU : c ∈ U := ((Finset.mem_insert.mp hc).resolve_left hbc.symm |> Finset.mem_insert.mp).resolve_left hac.symm
          exact pairCaseR a b c rfl rfl hcU hca hcb hcc
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · rcases Finset.mem_insert.mp hc with rfl | hc1
            · exact pairCaseR a c b rfl rfl hbU hca hcc hcb
            · rcases Finset.mem_insert.mp hc1 with hcEq | hcU
              · exact (hac hcEq.symm).elim
              · obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail b c
                  (Finset.mem_insert_of_mem hbU) (Finset.mem_insert_of_mem hcU) hbc hcb hcc
                exact ⟨q, by omega, free7_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · rcases Finset.mem_insert.mp hc with hcEq | hc1
          · exact (hbc hcEq.symm).elim
          · rcases Finset.mem_insert.mp hc1 with rfl | hcU
            · exact pairCase b c a rfl rfl haU hcb hcc hca
            · obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail a c
                (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hcU) hac hca hcc
              exact ⟨q, by omega, free7_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · rcases Finset.mem_insert.mp hc with rfl | hc1
            · exact pairCaseR b c a rfl rfl haU hcb hcc hca
            · rcases Finset.mem_insert.mp hc1 with hcEq | hcU
              · exact (hbc hcEq.symm).elim
              · obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail a c
                  (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hcU) hac hca hcc
                exact ⟨q, by omega, free7_binary_right hcb hf⟩
          · rcases Finset.mem_insert.mp hc with rfl | hc1
            · obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail a b
                (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) hab hca hcb
              exact ⟨q, by omega, free7_binary_left hcc hf⟩
            · rcases Finset.mem_insert.mp hc1 with rfl | hcU
              · obtain ⟨q, hq, hf⟩ := feasible7_two_consts hF tail a b
                  (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) hab hca hcb
                exact ⟨q, by omega, free7_binary_right hcc hf⟩
              · obtain ⟨q, hq, hf⟩ := ih a b c
                  (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU) (Finset.mem_insert_of_mem hcU)
                  hab hac hbc hca hcb hcc
                exact ⟨q + 1, by omega, pull7_binary hf⟩

lemma xs517_nd : Base1007.Theta.xs517.Nodup := by decide +kernel

lemma no_feasible7_10 {emb : Fin 7 → Fin 9} {S : Finset BF}
    (hsub : ∀ φ ∈ S, proj7 emb φ = 0 ∨ proj7 emb φ ∈ Base1007.Theta.xs517)
    (hf : Feasible7 emb 10 S) : False := by
  obtain ⟨m, hm, t, T, hl, hT⟩ := hf
  have hTxs : ∀ z ∈ T, z ∈ Base1007.Theta.xs517 := by
    intro z hz
    obtain ⟨φ, hφS, rfl⟩ := Finset.mem_image.mp (hT hz)
    rcases hsub φ hφS with h0 | hr
    · exact ((live7_proper hl _ hz).2.1 h0).elim
    · exact hr
  let L := Base1007.Theta.xs517.filter (fun z => decide (z ∈ T))
  have hLsub : L.Sublist Base1007.Theta.xs517 := List.filter_sublist
  have hLnd : L.Nodup := xs517_nd.filter _
  have hLtf : L.toFinset = T := by
    ext z
    simp only [L, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun hz => ⟨hTxs z hz, hz⟩⟩
  exact Base1007.Theta.noSub hm hLsub (live7_to_run hl L hLnd hLtf)

lemma no_feasible7_10_46 {emb : Fin 7 → Fin 9} {S : Finset BF}
    (hsub : ∀ φ ∈ S, proj7 emb φ = 0 ∨ proj7 emb φ ∈ Base1007.Theta.xs46)
    (hf : Feasible7 emb 10 S) : False := by
  obtain ⟨m, hm, t, T, hl, hT⟩ := hf
  have hTxs : ∀ z ∈ T, z ∈ Base1007.Theta.xs46 := by
    intro z hz
    obtain ⟨φ, hφS, rfl⟩ := Finset.mem_image.mp (hT hz)
    rcases hsub φ hφS with h0 | hr
    · exact ((live7_proper hl _ hz).2.1 h0).elim
    · exact hr
  let L := Base1007.Theta.xs46.filter (fun z => decide (z ∈ T))
  have hLsub : L.Sublist Base1007.Theta.xs46 := List.filter_sublist
  have hLnd : L.Nodup := Base1007.Theta.xs46_nd.filter _
  have hLtf : L.toFinset = T := by
    ext z
    simp only [L, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun hz => ⟨hTxs z hz, hz⟩⟩
  exact Base1007.Theta.noSub46 hm hLsub (live7_to_run hl L hLnd hLtf)

def emb8_4 : Fin 8 → Fin 9 := ![0, 1, 2, 3, 5, 6, 7, 8]
def emb8_6 : Fin 8 → Fin 9 := ![1, 0, 5, 8, 2, 4, 7, 3]
def emb8_7 : Fin 8 → Fin 9 := ![2, 1, 0, 5, 3, 6, 4, 8]

def emb7_04 : Fin 7 → Fin 9 := ![2, 8, 3, 1, 6, 7, 5]
def emb7_34 : Fin 7 → Fin 9 := ![1, 5, 0, 2, 7, 6, 8]
def emb7_16 : Fin 7 → Fin 9 := ![3, 5, 8, 2, 7, 4, 0]
def emb7_86 : Fin 7 → Fin 9 := ![0, 2, 1, 4, 3, 5, 7]
def emb7_27 : Fin 7 → Fin 9 := ![0, 8, 5, 1, 6, 4, 3]
def emb7_57 : Fin 7 → Fin 9 := ![1, 3, 2, 0, 4, 6, 8]

lemma emb8_4_inj : Function.Injective emb8_4 := by decide
lemma emb8_6_inj : Function.Injective emb8_6 := by decide
lemma emb8_7_inj : Function.Injective emb8_7 := by decide
lemma emb8_4_miss : ∀ i : Fin 8, emb8_4 i ≠ 4 := by decide
lemma emb8_6_miss : ∀ i : Fin 8, emb8_6 i ≠ 6 := by decide
lemma emb8_7_miss : ∀ i : Fin 8, emb8_7 i ≠ 7 := by decide

lemma emb7_04_inj : Function.Injective emb7_04 := by decide
lemma emb7_34_inj : Function.Injective emb7_34 := by decide
lemma emb7_16_inj : Function.Injective emb7_16 := by decide
lemma emb7_86_inj : Function.Injective emb7_86 := by decide
lemma emb7_27_inj : Function.Injective emb7_27 := by decide
lemma emb7_57_inj : Function.Injective emb7_57 := by decide

lemma emb7_04_m0 : ∀ i : Fin 7, emb7_04 i ≠ 0 := by decide
lemma emb7_04_m4 : ∀ i : Fin 7, emb7_04 i ≠ 4 := by decide
lemma emb7_34_m3 : ∀ i : Fin 7, emb7_34 i ≠ 3 := by decide
lemma emb7_34_m4 : ∀ i : Fin 7, emb7_34 i ≠ 4 := by decide
lemma emb7_16_m1 : ∀ i : Fin 7, emb7_16 i ≠ 1 := by decide
lemma emb7_16_m6 : ∀ i : Fin 7, emb7_16 i ≠ 6 := by decide
lemma emb7_86_m8 : ∀ i : Fin 7, emb7_86 i ≠ 8 := by decide
lemma emb7_86_m6 : ∀ i : Fin 7, emb7_86 i ≠ 6 := by decide
lemma emb7_27_m2 : ∀ i : Fin 7, emb7_27 i ≠ 2 := by decide
lemma emb7_27_m7 : ∀ i : Fin 7, emb7_27 i ≠ 7 := by decide
lemma emb7_57_m5 : ∀ i : Fin 7, emb7_57 i ≠ 5 := by decide
lemma emb7_57_m7 : ∀ i : Fin 7, emb7_57 i ≠ 7 := by decide

set_option maxHeartbeats 0 in
lemma proj8_4_F9_b : ∀ j : Fin 252, F9 (lift8 emb8_4 (pos8 j.val)) = true ∧ F9 (lift8 emb8_4 (neg8 j.val)) = false := by decide +kernel
set_option maxHeartbeats 0 in
lemma proj8_6_F9_b : ∀ j : Fin 252, F9 (lift8 emb8_6 (pos8 j.val)) = true ∧ F9 (lift8 emb8_6 (neg8 j.val)) = false := by decide +kernel
set_option maxHeartbeats 0 in
lemma proj8_7_F9_b : ∀ j : Fin 252, F9 (lift8 emb8_7 (pos8 j.val)) = true ∧ F9 (lift8 emb8_7 (neg8 j.val)) = false := by decide +kernel

lemma proj8_F9_of_b {emb : Fin 8 → Fin 9}
    (hb : ∀ j : Fin 252, F9 (lift8 emb (pos8 j.val)) = true ∧ F9 (lift8 emb (neg8 j.val)) = false) :
    proj8 emb F9 = Base1007.target := by
  apply sig8_ext <;> intro j hj
  · rw [proj8_fst_bit _ _ _ hj, (hb ⟨j, hj⟩).1, Base1007.target, top8_bit _ hj]
  · rw [proj8_snd_bit _ _ _ hj, (hb ⟨j, hj⟩).2, target8_bit2]

lemma proj8_4_F9 : proj8 emb8_4 F9 = Base1007.target := proj8_F9_of_b proj8_4_F9_b
lemma proj8_6_F9 : proj8 emb8_6 F9 = Base1007.target := proj8_F9_of_b proj8_6_F9_b
lemma proj8_7_F9 : proj8 emb8_7 F9 = Base1007.target := proj8_F9_of_b proj8_7_F9_b

set_option maxHeartbeats 0 in
lemma proj7_04_F9_b : ∀ j : Fin 464, F9 (lift7 emb7_04 (inp7 j.val)) = decide (232 ≤ j.val) := by decide +kernel
set_option maxHeartbeats 0 in
lemma proj7_34_F9_b : ∀ j : Fin 464, F9 (lift7 emb7_34 (inp7 j.val)) = decide (232 ≤ j.val) := by decide +kernel
set_option maxHeartbeats 0 in
lemma proj7_16_F9_b : ∀ j : Fin 464, F9 (lift7 emb7_16 (inp7 j.val)) = decide (232 ≤ j.val) := by decide +kernel
set_option maxHeartbeats 0 in
lemma proj7_86_F9_b : ∀ j : Fin 464, F9 (lift7 emb7_86 (inp7 j.val)) = decide (232 ≤ j.val) := by decide +kernel
set_option maxHeartbeats 0 in
lemma proj7_27_F9_b : ∀ j : Fin 464, F9 (lift7 emb7_27 (inp7 j.val)) = decide (232 ≤ j.val) := by decide +kernel
set_option maxHeartbeats 0 in
lemma proj7_57_F9_b : ∀ j : Fin 464, F9 (lift7 emb7_57 (inp7 j.val)) = decide (232 ≤ j.val) := by decide +kernel

lemma proj7_F9_of_b {emb : Fin 7 → Fin 9}
    (hb : ∀ j : Fin 464, F9 (lift7 emb (inp7 j.val)) = decide (232 ≤ j.val)) :
    proj7 emb F9 = G7 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [proj7_testBit, G7, Base1007.Theta.xo]
  by_cases hj : j < 464
  · rw [decide_eq_true hj, Bool.true_and, hb ⟨j, hj⟩]
    by_cases h2 : 232 ≤ j <;> simp [h2, show j - 232 < 232 by omega]
  · simp [hj]; omega

lemma proj7_04_F9 : proj7 emb7_04 F9 = G7 := proj7_F9_of_b proj7_04_F9_b
lemma proj7_34_F9 : proj7 emb7_34 F9 = G7 := proj7_F9_of_b proj7_34_F9_b
lemma proj7_16_F9 : proj7 emb7_16 F9 = G7 := proj7_F9_of_b proj7_16_F9_b
lemma proj7_86_F9 : proj7 emb7_86 F9 = G7 := proj7_F9_of_b proj7_86_F9_b
lemma proj7_27_F9 : proj7 emb7_27 F9 = G7 := proj7_F9_of_b proj7_27_F9_b
lemma proj7_57_F9 : proj7 emb7_57 F9 = G7 := proj7_F9_of_b proj7_57_F9_b

lemma raw8_getD_mem (i : Fin 8) : Base1007.raw.getD i.val Base1007.zero ∈ Base1007.raw := by
  have hi : i.val < Base1007.raw.length := i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

lemma xs517_getD_mem (i : Fin 7) : Base1007.Theta.xs517.getD i.val 0 ∈ Base1007.Theta.xs517 := by
  have hi : i.val < Base1007.Theta.xs517.length := i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

lemma proj8_var_in_raw {emb : Fin 8 → Fin 9} {d : Fin 9}
    (hinj : Function.Injective emb) (hmiss : ∀ i : Fin 8, emb i ≠ d)
    (hsurj : ∀ v : Fin 9, v = d ∨ ∃ i : Fin 8, emb i = v) (v : Fin 9) :
    proj8 emb (wVar v) = Base1007.zero ∨ proj8 emb (wVar v) ∈ Base1007.raw := by
  rcases hsurj v with rfl | ⟨i, rfl⟩
  · exact Or.inl (proj8_var_miss hmiss)
  · rw [proj8_var_hit hinj i]; exact Or.inr (raw8_getD_mem i)

lemma proj7_var_in_xs517 {emb : Fin 7 → Fin 9} {d1 d2 : Fin 9}
    (hinj : Function.Injective emb) (hm1 : ∀ i : Fin 7, emb i ≠ d1) (hm2 : ∀ i : Fin 7, emb i ≠ d2)
    (hsurj : ∀ v : Fin 9, v = d1 ∨ v = d2 ∨ ∃ i : Fin 7, emb i = v) (v : Fin 9) :
    proj7 emb (wVar v) = 0 ∨ proj7 emb (wVar v) ∈ Base1007.Theta.xs517 := by
  rcases hsurj v with rfl | rfl | ⟨i, rfl⟩
  · exact Or.inl (proj7_var_miss hm1)
  · exact Or.inl (proj7_var_miss hm2)
  · rw [proj7_var_hit hinj i]; exact Or.inr (xs517_getD_mem i)

lemma emb8_4_surj : ∀ v : Fin 9, v = 4 ∨ ∃ i : Fin 8, emb8_4 i = v := by decide
lemma emb8_6_surj : ∀ v : Fin 9, v = 6 ∨ ∃ i : Fin 8, emb8_6 i = v := by decide
lemma emb8_7_surj : ∀ v : Fin 9, v = 7 ∨ ∃ i : Fin 8, emb8_7 i = v := by decide
lemma emb7_04_surj : ∀ v : Fin 9, v = 0 ∨ v = 4 ∨ ∃ i : Fin 7, emb7_04 i = v := by decide
lemma emb7_34_surj : ∀ v : Fin 9, v = 3 ∨ v = 4 ∨ ∃ i : Fin 7, emb7_34 i = v := by decide
lemma emb7_16_surj : ∀ v : Fin 9, v = 1 ∨ v = 6 ∨ ∃ i : Fin 7, emb7_16 i = v := by decide
lemma emb7_86_surj : ∀ v : Fin 9, v = 8 ∨ v = 6 ∨ ∃ i : Fin 7, emb7_86 i = v := by decide
lemma emb7_27_surj : ∀ v : Fin 9, v = 2 ∨ v = 7 ∨ ∃ i : Fin 7, emb7_27 i = v := by decide
lemma emb7_57_surj : ∀ v : Fin 9, v = 5 ∨ v = 7 ∨ ∃ i : Fin 7, emb7_57 i = v := by decide

lemma proj8_4_w09 : proj8 emb8_4 w09 ∈ Base1007.raw := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  rw [heq, proj8_bin, proj8_var_miss emb8_4_miss, sig8_bin_comm, (sig8_bin_laws _).2.1]
  have h6 : (6 : Fin 9) = emb8_4 5 := rfl
  rw [h6, proj8_var_hit emb8_4_inj 5]
  exact raw8_getD_mem 5

lemma proj8_6_w09 : proj8 emb8_6 w09 ∈ Base1007.raw := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  rw [heq, proj8_bin, proj8_var_miss emb8_6_miss, (sig8_bin_laws _).2.1]
  have h4 : (4 : Fin 9) = emb8_6 5 := rfl
  rw [h4, proj8_var_hit emb8_6_inj 5]
  exact raw8_getD_mem 5

lemma proj8_7_w09 :
    proj8 emb8_7 w09 = Base1007.bin true (Base1007.raw.getD 6 Base1007.zero) (Base1007.raw.getD 5 Base1007.zero) := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  have h4 : (4 : Fin 9) = emb8_7 6 := rfl
  have h6 : (6 : Fin 9) = emb8_7 5 := rfl
  rw [heq, proj8_bin, h4, h6, proj8_var_hit emb8_7_inj 6, proj8_var_hit emb8_7_inj 5]
  rfl

lemma proj7_04_w09 : proj7 emb7_04 w09 ∈ Base1007.Theta.xs517 := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  rw [heq, proj7_bin, proj7_var_miss emb7_04_m4, bin7_comm, (bin7_laws (proj7_valid _ _)).2.1]
  have h6 : (6 : Fin 9) = emb7_04 4 := rfl
  rw [h6, proj7_var_hit emb7_04_inj 4]; exact xs517_getD_mem 4

lemma proj7_34_w09 : proj7 emb7_34 w09 ∈ Base1007.Theta.xs517 := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  rw [heq, proj7_bin, proj7_var_miss emb7_34_m4, bin7_comm, (bin7_laws (proj7_valid _ _)).2.1]
  have h6 : (6 : Fin 9) = emb7_34 5 := rfl
  rw [h6, proj7_var_hit emb7_34_inj 5]; exact xs517_getD_mem 5

lemma proj7_16_w09 : proj7 emb7_16 w09 ∈ Base1007.Theta.xs517 := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  rw [heq, proj7_bin, proj7_var_miss emb7_16_m6, (bin7_laws (proj7_valid _ _)).2.1]
  have h4 : (4 : Fin 9) = emb7_16 5 := rfl
  rw [h4, proj7_var_hit emb7_16_inj 5]; exact xs517_getD_mem 5

lemma proj7_86_w09 : proj7 emb7_86 w09 ∈ Base1007.Theta.xs517 := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  rw [heq, proj7_bin, proj7_var_miss emb7_86_m6, (bin7_laws (proj7_valid _ _)).2.1]
  have h4 : (4 : Fin 9) = emb7_86 3 := rfl
  rw [h4, proj7_var_hit emb7_86_inj 3]; exact xs517_getD_mem 3

lemma proj7_27_w09 : proj7 emb7_27 w09 = Base1007.Theta.w46 := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  have h4 : (4 : Fin 9) = emb7_27 5 := rfl
  have h6 : (6 : Fin 9) = emb7_27 4 := rfl
  rw [heq, proj7_bin, h4, h6, proj7_var_hit emb7_27_inj 5, proj7_var_hit emb7_27_inj 4,
    Base1007.Theta.w46_eq, bin7, if_pos rfl, Nat.or_comm]
  rfl

lemma proj7_57_w09 : proj7 emb7_57 w09 = Base1007.Theta.w46 := by
  have heq : w09 = bin9 true (wVar 4) (wVar 6) := rfl
  have h4 : (4 : Fin 9) = emb7_57 4 := rfl
  have h6 : (6 : Fin 9) = emb7_57 5 := rfl
  rw [heq, proj7_bin, h4, h6, proj7_var_hit emb7_57_inj 4, proj7_var_hit emb7_57_inj 5,
    Base1007.Theta.w46_eq, bin7, if_pos rfl]
  rfl

def mkIn (m : Nat) : Fin 9 → Bool := fun i => m.testBit i.val

lemma var_mem_of_wit {k t : Nat} {S : Finset BF} {φ10 : BF} (hl : Live9 k t S)
    (hsub : ∀ φ ∈ S, φ ∈ sBase ++ [φ10]) (v : Fin 9) (m : Nat)
    (hF : F9 (mkIn m) ≠ F9 (mkIn (m ||| (2 ^ v.val))))
    (h09 : w09 (mkIn m) = w09 (mkIn (m ||| (2 ^ v.val))))
    (h10 : φ10 (mkIn m) = φ10 (mkIn (m ||| (2 ^ v.val)))) :
    wVar v ∈ S := by
  obtain ⟨φ, hφS, hneq⟩ := live9_sep hl (mkIn m) (mkIn (m ||| (2 ^ v.val))) hF
  rcases List.mem_append.mp (hsub φ hφS) with hB | h1
  · rcases List.mem_append.mp hB with hv | h9
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      by_cases hj : j = v
      · exact hj ▸ hφS
      · exfalso
        apply hneq
        simp only [wVar, mkIn, Nat.testBit_or, Nat.testBit_two_pow]
        have hne : v.val ≠ j.val := fun e => hj (Fin.ext e.symm)
        simp [hne]
    · simp only [List.mem_singleton] at h9
      subst φ
      exact (hneq h09).elim
  · simp only [List.mem_singleton] at h1
    subst φ
    exact (hneq h10).elim

lemma var_mem_base {k t : Nat} {S : Finset BF} (hl : Live9 k t S)
    (hsub : ∀ φ ∈ S, φ ∈ sBase) : wVar 4 ∈ S := by
  obtain ⟨φ, hφS, hneq⟩ := live9_sep hl (mkIn 72) (mkIn 88) (by decide)
  rcases List.mem_append.mp (hsub φ hφS) with hv | h9
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    fin_cases j <;> first | exact hφS | (exfalso; apply hneq; decide)
  · simp only [List.mem_singleton] at h9
    subst φ
    exact (hneq (by decide)).elim

lemma kill_base {k t : Nat} {S : Finset BF} (hk : k ≤ 13) (hl : Live9 k t S)
    (hsub : ∀ φ ∈ S, φ ∈ sBase) : False := by
  have h4 : wVar 4 ∈ S := var_mem_base hl hsub
  have hc4 : ¬ Base1007.proper (proj8 emb8_4 (wVar 4)) := by
    rw [proj8_var_miss emb8_4_miss]; exact fun h => h.1 rfl
  obtain ⟨q, hq, hf⟩ := feasible8_const proj8_4_F9 hl (wVar 4) h4 hc4
  apply no_feasible8_12 _ (feasible8_mono hf (by omega : q ≤ 12))
  intro φ hφS
  rcases List.mem_append.mp (hsub φ hφS) with hv | h9
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact proj8_var_in_raw emb8_4_inj emb8_4_miss emb8_4_surj j
  · simp only [List.mem_singleton] at h9
    subst φ
    exact Or.inr proj8_4_w09

lemma raw8_6_proper : Base1007.proper (Base1007.raw.getD 6 Base1007.zero) := ⟨by decide, by decide⟩
lemma raw8_5_proper : Base1007.proper (Base1007.raw.getD 5 Base1007.zero) := ⟨by decide, by decide⟩
lemma raw8_6_ne_5 : Base1007.raw.getD 6 Base1007.zero ≠ Base1007.raw.getD 5 Base1007.zero := by decide
lemma raw8_or65_not_mem :
    Base1007.bin true (Base1007.raw.getD 6 Base1007.zero) (Base1007.raw.getD 5 Base1007.zero) ∉ Base1007.raw := by
  decide

lemma wireBase_fin (v : Fin 9) : wireBase v.val = wVar v := by
  unfold wireBase
  rw [dif_pos v.isLt]

lemma wireBase_and_ne_var (v : Fin 9) (a b : Nat) (hb : b < 10) (hab : a < b)
    (ha4 : a ≠ 4) (hb4 : b ≠ 4) (ha6 : a ≠ 6) (hb6 : b ≠ 6) :
    wVar v ≠ bin9 false (wireBase a) (wireBase b) := by
  intro heq
  have h := congrFun heq (fun i => decide (i = v))
  simp only [wVar, decide_true, bin9, Bool.false_eq_true, ite_false] at h
  by_cases hav : a = v.val
  · have hbv : b ≠ v.val := by omega
    have hv4 : v ≠ 4 := fun e => ha4 (hav.trans (congrArg Fin.val e))
    have hv6 : v ≠ 6 := fun e => ha6 (hav.trans (congrArg Fin.val e))
    have hb0 : wireBase b (fun i => decide (i = v)) = false := by
      unfold wireBase
      by_cases hb9 : b < 9
      · simp only [hb9, dite_true, wVar, decide_eq_false_iff_not]
        intro e; exact hbv (congrArg Fin.val e)
      · have hbe : b = 9 := by omega
        subst hbe
        simp [w09, hv4.symm, hv6.symm]
    rw [hb0, Bool.and_false] at h
    exact Bool.false_ne_true h.symm
  · have ha9 : a < 9 := by omega
    have ha0 : wireBase a (fun i => decide (i = v)) = false := by
      unfold wireBase
      simp only [ha9, dite_true, wVar, decide_eq_false_iff_not]
      intro e; exact hav (congrArg Fin.val e)
    rw [ha0, Bool.false_and] at h
    exact Bool.false_ne_true h.symm

lemma wireBase_mkIn_zero (c : Nat) (hc : c < 10) (m : Nat)
    (h1 : c < 9 → m.testBit c = false)
    (h2 : c = 9 → m.testBit 4 = false ∧ m.testBit 6 = false) :
    wireBase c (mkIn m) = false := by
  unfold wireBase
  by_cases hc9 : c < 9
  · simp only [hc9, dite_true, wVar, mkIn]
    exact h1 hc9
  · have hce : c = 9 := by omega
    subst hce
    simp only [Nat.lt_irrefl, dite_false, ite_true, w09, mkIn]
    obtain ⟨h4, h6⟩ := h2 rfl
    simp [h4, h6]

lemma and_mkIn_zero_eq (a b : Nat) (v : Fin 9) (m : Nat)
    (h : (wireBase a (mkIn m) = false ∧ wireBase a (mkIn (m ||| 2 ^ v.val)) = false) ∨
         (wireBase b (mkIn m) = false ∧ wireBase b (mkIn (m ||| 2 ^ v.val)) = false)) :
    bin9 false (wireBase a) (wireBase b) (mkIn m) =
    bin9 false (wireBase a) (wireBase b) (mkIn (m ||| 2 ^ v.val)) := by
  simp only [bin9, Bool.false_eq_true, ite_false]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, Bool.false_and, Bool.false_and]
  · rw [h1, h2, Bool.and_false, Bool.and_false]

lemma var_mem_of_pair_other {k t : Nat} {S : Finset BF} (hl : Live9 k t S)
    (a b : Nat) (ha : a < 10) (hb : b < 10) (hab : a < b)
    (hsub : ∀ φ ∈ S, φ ∈ sBase ++ [bin9 false (wireBase a) (wireBase b)])
    (u : Fin 9) (hu : a = u.val ∨ b = u.val) (m : Nat)
    (hF : F9 (mkIn m) ≠ F9 (mkIn (m ||| 2 ^ u.val)))
    (h09 : w09 (mkIn m) = w09 (mkIn (m ||| 2 ^ u.val)))
    (h46 : m.testBit 4 = false ∧ m.testBit 6 = false)
    (hu4 : u.val ≠ 4) (hu6 : u.val ≠ 6)
    (hm : ∀ c : Nat, c < 9 → c ≠ u.val → (c = a ∨ c = b) → m.testBit c = false) :
    wVar u ∈ S := by
  apply var_mem_of_wit hl hsub u m hF h09
  apply and_mkIn_zero_eq a b u m
  rcases hu with rfl | rfl
  · right
    constructor
    · apply wireBase_mkIn_zero b hb m (fun hb9 => hm b hb9 (by omega) (Or.inr rfl)) (fun _ => h46)
    · apply wireBase_mkIn_zero b hb (m ||| 2 ^ u.val)
      · intro hb9
        rw [Nat.testBit_or, Nat.testBit_two_pow, hm b hb9 (by omega) (Or.inr rfl)]
        simp [show u.val ≠ b by omega]
      · intro _
        rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow, h46.1, h46.2]
        simp [hu4, hu6]
  · left
    constructor
    · apply wireBase_mkIn_zero a ha m (fun ha9 => hm a ha9 (by omega) (Or.inl rfl)) (fun _ => h46)
    · apply wireBase_mkIn_zero a ha (m ||| 2 ^ u.val)
      · intro ha9
        rw [Nat.testBit_or, Nat.testBit_two_pow, hm a ha9 (by omega) (Or.inl rfl)]
        simp [show u.val ≠ a by omega]
      · intro _
        rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow, h46.1, h46.2]
        simp [hu4, hu6]

lemma var_mem_of_pair_zero {k t : Nat} {S : Finset BF} (hl : Live9 k t S)
    (a b : Nat) (hsub : ∀ φ ∈ S, φ ∈ sBase ++ [bin9 false (wireBase a) (wireBase b)])
    (u d : Fin 9) (hu : a = u.val ∨ b = u.val) (hud : u ≠ d) (m : Nat)
    (hF : F9 (mkIn m) ≠ F9 (mkIn (m ||| 2 ^ d.val)))
    (h09 : w09 (mkIn m) = w09 (mkIn (m ||| 2 ^ d.val)))
    (hmu : m.testBit u.val = false) :
    wVar d ∈ S := by
  apply var_mem_of_wit hl hsub d m hF h09
  apply and_mkIn_zero_eq a b d m
  have hzu : wireBase u.val (mkIn m) = false ∧ wireBase u.val (mkIn (m ||| 2 ^ d.val)) = false := by
    rw [wireBase_fin]
    refine ⟨hmu, ?_⟩
    simp only [wVar, mkIn, Nat.testBit_or, Nat.testBit_two_pow, hmu]
    have hne : d.val ≠ u.val := fun e => hud (Fin.ext e.symm)
    simp [hne]
  rcases hu with rfl | rfl
  · exact Or.inl hzu
  · exact Or.inr hzu

lemma kill_and_pair {k t : Nat} {S : Finset BF} (hk : k ≤ 13) (hl : Live9 k t S)
    (a b : Nat) (ha : a < 10) (hb : b < 10) (hab : a < b)
    (hsub : ∀ φ ∈ S, φ ∈ sBase ++ [bin9 false (wireBase a) (wireBase b)]) : False := by
  let φ10 := bin9 false (wireBase a) (wireBase b)
  by_cases h10S : φ10 ∈ S
  · have kill_4 : (a = 4 ∨ b = 4) → False := by
      intro h4
      have hc10 : proj8 emb8_4 φ10 = Base1007.zero := by
        rcases h4 with rfl | rfl
        · change proj8 emb8_4 (bin9 false (wireBase (4 : Fin 9).val) (wireBase b)) = Base1007.zero
          rw [wireBase_fin, proj8_bin, proj8_var_miss emb8_4_miss, sig8_bin_comm, (sig8_bin_laws _).2.2.1]
        · change proj8 emb8_4 (bin9 false (wireBase a) (wireBase (4 : Fin 9).val)) = Base1007.zero
          rw [wireBase_fin, proj8_bin, proj8_var_miss emb8_4_miss, (sig8_bin_laws _).2.2.1]
      obtain ⟨q, hq, hf⟩ := feasible8_const proj8_4_F9 hl φ10 h10S (by rw [hc10]; exact fun h => h.1 rfl)
      apply no_feasible8_12 _ (feasible8_mono hf (by omega : q ≤ 12))
      intro φ hφS
      rcases List.mem_append.mp (hsub φ hφS) with hB | h1
      · rcases List.mem_append.mp hB with hv | h9
        · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
          exact proj8_var_in_raw emb8_4_inj emb8_4_miss emb8_4_surj j
        · simp only [List.mem_singleton] at h9; subst φ; exact Or.inr proj8_4_w09
      · simp only [List.mem_singleton] at h1; subst φ; exact Or.inl hc10
    have kill_6 : (a = 6 ∨ b = 6) → False := by
      intro h6
      have hc10 : proj8 emb8_6 φ10 = Base1007.zero := by
        rcases h6 with rfl | rfl
        · change proj8 emb8_6 (bin9 false (wireBase (6 : Fin 9).val) (wireBase b)) = Base1007.zero
          rw [wireBase_fin, proj8_bin, proj8_var_miss emb8_6_miss, sig8_bin_comm, (sig8_bin_laws _).2.2.1]
        · change proj8 emb8_6 (bin9 false (wireBase a) (wireBase (6 : Fin 9).val)) = Base1007.zero
          rw [wireBase_fin, proj8_bin, proj8_var_miss emb8_6_miss, (sig8_bin_laws _).2.2.1]
      obtain ⟨q, hq, hf⟩ := feasible8_const proj8_6_F9 hl φ10 h10S (by rw [hc10]; exact fun h => h.1 rfl)
      apply no_feasible8_12 _ (feasible8_mono hf (by omega : q ≤ 12))
      intro φ hφS
      rcases List.mem_append.mp (hsub φ hφS) with hB | h1
      · rcases List.mem_append.mp hB with hv | h9
        · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
          exact proj8_var_in_raw emb8_6_inj emb8_6_miss emb8_6_surj j
        · simp only [List.mem_singleton] at h9; subst φ; exact Or.inr proj8_6_w09
      · simp only [List.mem_singleton] at h1; subst φ; exact Or.inl hc10
    by_cases h4 : a = 4 ∨ b = 4
    · exact kill_4 h4
    by_cases h6 : a = 6 ∨ b = 6
    · exact kill_6 h6
    have ha4 : a ≠ 4 := fun e => h4 (Or.inl e)
    have hb4 : b ≠ 4 := fun e => h4 (Or.inr e)
    have ha6 : a ≠ 6 := fun e => h6 (Or.inl e)
    have hb6 : b ≠ 6 := fun e => h6 (Or.inr e)
    have hne_all : ∀ v : Fin 9, wVar v ≠ φ10 :=
      fun v => wireBase_and_ne_var v a b hb hab ha4 hb4 ha6 hb6
    have kill_7 : (a = 7 ∨ b = 7) → False := by
      intro h7
      have h7S : wVar 7 ∈ S := by
        by_cases h2 : a = 2 ∨ b = 2
        · apply var_mem_of_pair_other hl a b ha hb hab hsub 7 h7 32 (by decide) (by decide) (by decide) (by decide) (by decide)
          intro c hc9 hc7 hcab
          have hc2 : c = 2 := by omega
          subst hc2; decide
        · apply var_mem_of_pair_other hl a b ha hb hab hsub 7 h7 4 (by decide) (by decide) (by decide) (by decide) (by decide)
          intro c hc9 hc7 hcab
          have hc2 : c ≠ 2 := by omega
          interval_cases c <;> first | contradiction | decide
      have hc7 : proj8 emb8_7 (wVar 7) = Base1007.zero := proj8_var_miss emb8_7_miss
      have hc10 : proj8 emb8_7 φ10 = Base1007.zero := by
        rcases h7 with rfl | rfl
        · change proj8 emb8_7 (bin9 false (wireBase (7 : Fin 9).val) (wireBase b)) = Base1007.zero
          rw [wireBase_fin, proj8_bin, proj8_var_miss emb8_7_miss, sig8_bin_comm, (sig8_bin_laws _).2.2.1]
        · change proj8 emb8_7 (bin9 false (wireBase a) (wireBase (7 : Fin 9).val)) = Base1007.zero
          rw [wireBase_fin, proj8_bin, proj8_var_miss emb8_7_miss, (sig8_bin_laws _).2.2.1]
      obtain ⟨q, hq, hf⟩ := feasible8_two_consts proj8_7_F9 hl (wVar 7) φ10 h7S h10S (hne_all 7)
        (by rw [hc7]; exact fun h => h.1 rfl) (by rw [hc10]; exact fun h => h.1 rfl)
      apply no_feasible8_11_or (raw8_getD_mem 6) (raw8_getD_mem 5) raw8_6_proper raw8_5_proper
        raw8_6_ne_5 raw8_or65_not_mem _ (feasible8_mono hf (by omega : q ≤ 11))
      intro φ hφS
      rcases List.mem_append.mp (hsub φ hφS) with hB | h1
      · rcases List.mem_append.mp hB with hv | h9
        · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
          rcases proj8_var_in_raw emb8_7_inj emb8_7_miss emb8_7_surj j with h0 | hr
          · exact Or.inl h0
          · exact Or.inr (Or.inl hr)
        · simp only [List.mem_singleton] at h9; subst φ; exact Or.inr (Or.inr proj8_7_w09)
      · simp only [List.mem_singleton] at h1; subst φ; exact Or.inl hc10
    have kill_3a : ∀ (u d : Fin 9) (emb : Fin 7 → Fin 9),
        Function.Injective emb → (∀ i : Fin 7, emb i ≠ u) → (∀ i : Fin 7, emb i ≠ d) →
        (∀ v : Fin 9, v = u ∨ v = d ∨ ∃ i : Fin 7, emb i = v) →
        proj7 emb F9 = G7 → proj7 emb w09 ∈ Base1007.Theta.xs517 →
        (a = u.val ∨ b = u.val) → u ≠ d →
        wVar u ∈ S → wVar d ∈ S → False := by
      intro u d emb hinj hmu hmd hsurj hF hw09 hu hud huS hdS
      have hcu : proj7 emb (wVar u) = 0 := proj7_var_miss hmu
      have hcd : proj7 emb (wVar d) = 0 := proj7_var_miss hmd
      have hc10 : proj7 emb φ10 = 0 := by
        rcases hu with h1 | h1
        · change proj7 emb (bin9 false (wireBase a) (wireBase b)) = 0
          rw [h1, wireBase_fin, proj7_bin, proj7_var_miss hmu, bin7_comm, (bin7_laws (proj7_valid _ _)).2.2.1]
        · change proj7 emb (bin9 false (wireBase a) (wireBase b)) = 0
          rw [h1, wireBase_fin, proj7_bin, proj7_var_miss hmu, (bin7_laws (proj7_valid _ _)).2.2.1]
      have hneud : wVar u ≠ wVar d := by
        intro heq
        have h1 := congrFun heq (fun i => decide (i = u))
        simp [wVar, hud.symm] at h1
      obtain ⟨q, hq, hf⟩ := feasible7_three_consts hF hl (wVar u) (wVar d) φ10
        huS hdS h10S hneud (hne_all u) (hne_all d)
        (by rw [hcu]; exact fun h => h.2.1 rfl)
        (by rw [hcd]; exact fun h => h.2.1 rfl)
        (by rw [hc10]; exact fun h => h.2.1 rfl)
      apply no_feasible7_10 _ (feasible7_mono hf (by omega : q ≤ 10))
      intro φ hφS
      rcases List.mem_append.mp (hsub φ hφS) with hB | h1
      · rcases List.mem_append.mp hB with hv | h9
        · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
          exact proj7_var_in_xs517 hinj hmu hmd hsurj j
        · simp only [List.mem_singleton] at h9; subst φ; exact Or.inr hw09
      · simp only [List.mem_singleton] at h1; subst φ; exact Or.inl hc10
    have kill_3b : ∀ (u : Fin 9) (emb : Fin 7 → Fin 9),
        Function.Injective emb → (∀ i : Fin 7, emb i ≠ u) → (∀ i : Fin 7, emb i ≠ 7) →
        (∀ v : Fin 9, v = u ∨ v = 7 ∨ ∃ i : Fin 7, emb i = v) →
        proj7 emb F9 = G7 → proj7 emb w09 = Base1007.Theta.w46 →
        (a = u.val ∨ b = u.val) → u ≠ 7 →
        wVar u ∈ S → wVar 7 ∈ S → False := by
      intro u emb hinj hmu hm7 hsurj hF hw09 hu hu7 huS h7S
      have hcu : proj7 emb (wVar u) = 0 := proj7_var_miss hmu
      have hc7 : proj7 emb (wVar 7) = 0 := proj7_var_miss hm7
      have hc10 : proj7 emb φ10 = 0 := by
        rcases hu with h1 | h1
        · change proj7 emb (bin9 false (wireBase a) (wireBase b)) = 0
          rw [h1, wireBase_fin, proj7_bin, proj7_var_miss hmu, bin7_comm, (bin7_laws (proj7_valid _ _)).2.2.1]
        · change proj7 emb (bin9 false (wireBase a) (wireBase b)) = 0
          rw [h1, wireBase_fin, proj7_bin, proj7_var_miss hmu, (bin7_laws (proj7_valid _ _)).2.2.1]
      have hneu7 : wVar u ≠ wVar 7 := by
        intro heq
        have h1 := congrFun heq (fun i => decide (i = u))
        simp [wVar, hu7.symm] at h1
      obtain ⟨q, hq, hf⟩ := feasible7_three_consts hF hl (wVar u) (wVar 7) φ10
        huS h7S h10S hneu7 (hne_all u) (hne_all 7)
        (by rw [hcu]; exact fun h => h.2.1 rfl)
        (by rw [hc7]; exact fun h => h.2.1 rfl)
        (by rw [hc10]; exact fun h => h.2.1 rfl)
      apply no_feasible7_10_46 _ (feasible7_mono hf (by omega : q ≤ 10))
      intro φ hφS
      rcases List.mem_append.mp (hsub φ hφS) with hB | h1
      · rcases List.mem_append.mp hB with hv | h9
        · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
          rcases proj7_var_in_xs517 hinj hmu hm7 hsurj j with h0 | hr
          · exact Or.inl h0
          · exact Or.inr (List.mem_append_left _ hr)
        · simp only [List.mem_singleton] at h9; subst φ
          rw [hw09]; exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
      · simp only [List.mem_singleton] at h1; subst φ; exact Or.inl hc10
    by_cases h7 : a = 7 ∨ b = 7
    · exact kill_7 h7
    by_cases h0 : a = 0 ∨ b = 0
    · have h0S : wVar 0 ∈ S := by
        by_cases h1 : a = 1 ∨ b = 1
        · apply var_mem_of_pair_other hl a b ha hb hab hsub 0 h0 32 (by decide) (by decide) (by decide) (by decide) (by decide)
          intro c hc9 hc0 hcab
          have hc1 : c = 1 := by omega
          subst hc1; decide
        · apply var_mem_of_pair_other hl a b ha hb hab hsub 0 h0 2 (by decide) (by decide) (by decide) (by decide) (by decide)
          intro c hc9 hc0 hcab
          have hc1 : c ≠ 1 := by omega
          interval_cases c <;> first | contradiction | decide
      have h4S : wVar 4 ∈ S := var_mem_of_pair_zero hl a b hsub 0 4 h0 (by decide) 72 (by decide) (by decide) (by decide)
      exact kill_3a 0 4 emb7_04 emb7_04_inj emb7_04_m0 emb7_04_m4 emb7_04_surj proj7_04_F9 proj7_04_w09 h0 (by decide) h0S h4S
    by_cases h3 : a = 3 ∨ b = 3
    · have h3S : wVar 3 ∈ S := by
        by_cases h2 : a = 2 ∨ b = 2
        · apply var_mem_of_pair_other hl a b ha hb hab hsub 3 h3 256 (by decide) (by decide) (by decide) (by decide) (by decide)
          intro c hc9 hc3 hcab
          have hc2 : c = 2 := by omega
          subst hc2; decide
        · apply var_mem_of_pair_other hl a b ha hb hab hsub 3 h3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
          intro c hc9 hc3 hcab
          have hc2 : c ≠ 2 := by omega
          interval_cases c <;> first | contradiction | decide
      have h4S : wVar 4 ∈ S := var_mem_of_pair_zero hl a b hsub 3 4 h3 (by decide) 65 (by decide) (by decide) (by decide)
      exact kill_3a 3 4 emb7_34 emb7_34_inj emb7_34_m3 emb7_34_m4 emb7_34_surj proj7_34_F9 proj7_34_w09 h3 (by decide) h3S h4S
    by_cases h1 : a = 1 ∨ b = 1
    · have h1S : wVar 1 ∈ S := by
        apply var_mem_of_pair_other hl a b ha hb hab hsub 1 h1 1 (by decide) (by decide) (by decide) (by decide) (by decide)
        intro c hc9 hc1 hcab
        have hc0 : c ≠ 0 := by omega
        interval_cases c <;> first | contradiction | decide
      have h6S : wVar 6 ∈ S := var_mem_of_pair_zero hl a b hsub 1 6 h1 (by decide) 272 (by decide) (by decide) (by decide)
      exact kill_3a 1 6 emb7_16 emb7_16_inj emb7_16_m1 emb7_16_m6 emb7_16_surj proj7_16_F9 proj7_16_w09 h1 (by decide) h1S h6S
    by_cases h8 : a = 8 ∨ b = 8
    · have h8S : wVar 8 ∈ S := by
        apply var_mem_of_pair_other hl a b ha hb hab hsub 8 h8 8 (by decide) (by decide) (by decide) (by decide) (by decide)
        intro c hc9 hc8 hcab
        have hc3 : c ≠ 3 := by omega
        interval_cases c <;> first | contradiction | decide
      have h6S : wVar 6 ∈ S := var_mem_of_pair_zero hl a b hsub 8 6 h8 (by decide) 18 (by decide) (by decide) (by decide)
      exact kill_3a 8 6 emb7_86 emb7_86_inj emb7_86_m8 emb7_86_m6 emb7_86_surj proj7_86_F9 proj7_86_w09 h8 (by decide) h8S h6S
    by_cases h2 : a = 2 ∨ b = 2
    · have h2S : wVar 2 ∈ S := by
        apply var_mem_of_pair_other hl a b ha hb hab hsub 2 h2 2 (by decide) (by decide) (by decide) (by decide) (by decide)
        intro c hc9 hc2 hcab
        have hc1 : c ≠ 1 := by omega
        interval_cases c <;> first | contradiction | decide
      have h7S : wVar 7 ∈ S := by
        apply var_mem_of_wit hl hsub 7 4 (by decide) (by decide)
        apply and_mkIn_zero_eq a b 7 4
        have ha2 : a = 2 := by omega
        have hb59 : b = 5 ∨ b = 9 := by omega
        right
        rcases hb59 with rfl | rfl <;> constructor <;> decide
      exact kill_3b 2 emb7_27 emb7_27_inj emb7_27_m2 emb7_27_m7 emb7_27_surj proj7_27_F9 proj7_27_w09 h2 (by decide) h2S h7S
    by_cases h5 : a = 5 ∨ b = 5
    · have ha5 : a = 5 := by omega
      have hb9 : b = 9 := by omega
      have h5S : wVar 5 ∈ S := by
        apply var_mem_of_wit hl hsub 5 1 (by decide) (by decide)
        apply and_mkIn_zero_eq a b 5 1
        right; rw [hb9]; constructor <;> decide
      have h7S : wVar 7 ∈ S := var_mem_of_pair_zero hl a b hsub 5 7 h5 (by decide) 4 (by decide) (by decide) (by decide)
      exact kill_3b 5 emb7_57 emb7_57_inj emb7_57_m5 emb7_57_m7 emb7_57_surj proj7_57_F9 proj7_57_w09 h5 (by decide) h5S h7S
    omega
  · apply kill_base hk hl
    intro φ hφS
    rcases List.mem_append.mp (hsub φ hφS) with hB | h1
    · exact hB
    · simp only [List.mem_singleton] at h1; subst φ; exact (h10S hφS).elim

lemma foldl_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨_ :: t, by simpa [List.foldl_cons] using ht⟩

theorem finalBound :
    ∀ (x1 : Circuit),
      FanInTwo x1 →
      (∀ (x3 : Fin 9 → Bool), (x1.wires (List.ofFn x3)).getD 9 false = (x3 4 || x3 6)) →
      circuitFun 9 x1 = F9 →
      Option.map (fun x5 : Gate => x5.op) x1.gates[1]? = some GateOp.and →
      16 ≤ x1.size := by
  intro C hfan h9 hfun hg1
  by_contra hlt
  have hle : C.gates.length ≤ 15 := by change ¬ 16 ≤ C.gates.length at hlt; omega
  rcases C with ⟨gs, out⟩
  rcases gs with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp at hg1
  · simp at hg1
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hg1
  have hrest_len : rest.length ≤ 13 := by simp at hle; omega
  have hw0 : ∀ x : Fin 9 → Bool,
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
    intro x
    have h9x := h9 x
    change ((g0 :: g1 :: rest).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD 9 false = (x 4 || x 6) at h9x
    rw [List.foldl_cons] at h9x
    obtain ⟨t, ht⟩ := foldl_prefix (g1 :: rest) (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)])
    rw [ht, List.getD_append _ _ _ _ (by simp)] at h9x
    simpa [List.getD_eq_getElem?_getD] using h9x
  let φ10 : BF := gateBF sBase g1
  have hmap_s0 : ∀ x : Fin 9 → Bool,
      (sBase ++ [φ10]).map (fun f => f x) =
      (List.ofFn x ++ [x 4 || x 6]) ++ [g1.op.eval (g1.inputs.map fun i => (List.ofFn x ++ [x 4 || x 6]).getD i false)] := by
    intro x
    have hsB : sBase.map (fun f => f x) = List.ofFn x ++ [x 4 || x 6] := by
      simp [sBase, wVar, w09]
    rw [List.map_append, List.map_cons, List.map_nil, hsB]
    congr 2
    dsimp only [φ10]
    rw [gateBF_eval, hsB]
  have heval : ∀ x : Fin 9 → Bool,
      ((wiresBF rest (sBase ++ [φ10])).getD out cFalse) x = F9 x := by
    intro x
    have hfx := congrFun hfun x
    change ((g0 :: g1 :: rest).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD out false = F9 x at hfx
    rw [List.foldl_cons, hw0 x, List.foldl_cons, ← hmap_s0 x, ← wiresBF_map] at hfx
    have hget : ((wiresBF rest (sBase ++ [φ10])).map (fun f => f x)).getD out false =
        ((wiresBF rest (sBase ++ [φ10])).getD out cFalse) x := by
      by_cases ho : out < (wiresBF rest (sBase ++ [φ10])).length
      · simp [List.getD_eq_getElem?_getD, ho]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]; rfl
    exact hget.symm.trans hfx
  have hF9eq : (wiresBF rest (sBase ++ [φ10])).getD out cFalse = F9 := funext heval
  have hF9mem : F9 ∈ wiresBF rest (sBase ++ [φ10]) := by
    by_cases ho : out < (wiresBF rest (sBase ++ [φ10])).length
    · rw [← hF9eq, List.getD_eq_getElem _ _ ho]
      exact List.getElem_mem ho
    · exfalso
      rw [List.getD_eq_default _ _ (by omega)] at hF9eq
      exact F9_ne_cFalse hF9eq.symm
  have hrest_ok : ∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hfan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
  obtain ⟨k, u, S, hk, hl, hsub⟩ := extract9 rest (sBase ++ [φ10]) hrest_ok hF9mem
  have hk13 : k ≤ 13 := hk.trans hrest_len
  have hg1_len : g1.inputs.length ≤ 2 := (hfan g1 (List.mem_cons_of_mem _ List.mem_cons_self)).2
  have hkill_not_proper : ¬ proper9 φ10 → False := by
    intro hnp
    apply kill_base hk13 hl
    intro φ hφS
    rcases List.mem_append.mp (hsub φ hφS) with hB | h1
    · exact hB
    · simp only [List.mem_singleton] at h1
      subst φ
      exact (hnp (live9_proper hl _ hφS)).elim
  have hkill_in_base : φ10 ∈ sBase → False := by
    intro hmem
    apply kill_base hk13 hl
    intro φ hφS
    rcases List.mem_append.mp (hsub φ hφS) with hB | h1
    · exact hB
    · simp only [List.mem_singleton] at h1
      exact h1 ▸ hmem
  rcases hin : g1.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · apply hkill_not_proper
    have : φ10 = cTrue := by funext x; simp [φ10, gateBF, hg1, hin, GateOp.eval, cTrue]
    rw [this]; exact fun h => h.2 rfl
  · have hφ : φ10 = wireBase a := by
      funext x
      simp only [φ10, gateBF, hg1, hin, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true]
      rw [getD_sBase]; rfl
    by_cases ha9 : a < 9
    · apply hkill_in_base
      rw [hφ, wireBase, dif_pos ha9]; exact mem_sBase_var ⟨a, ha9⟩
    · by_cases hae : a = 9
      · apply hkill_in_base
        rw [hφ, wireBase, dif_neg ha9, if_pos hae]; exact mem_sBase_w09
      · apply hkill_not_proper
        rw [hφ, wireBase, dif_neg ha9, if_neg hae]; exact fun h => h.1 rfl
  · have hφ : φ10 = bin9 false (wireBase a) (wireBase b) := by
      funext x
      simp only [φ10, gateBF, hg1, hin, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, bin9, Bool.false_eq_true, ite_false]
      rw [getD_sBase, getD_sBase]; rfl
    by_cases ha10 : a < 10
    · by_cases hb10 : b < 10
      · rcases Nat.lt_trichotomy a b with hab | hab | hab
        · exact kill_and_pair hk13 hl a b ha10 hb10 hab (by rwa [← hφ])
        · subst hab
          have heq : φ10 = wireBase a := by rw [hφ, (bin9_laws _).2.2.2.2.1]
          by_cases ha9 : a < 9
          · apply hkill_in_base; rw [heq, wireBase, dif_pos ha9]; exact mem_sBase_var ⟨a, ha9⟩
          · apply hkill_in_base; rw [heq, wireBase, dif_neg ha9, if_pos (by omega)]; exact mem_sBase_w09
        · have hφ' : φ10 = bin9 false (wireBase b) (wireBase a) := by rw [hφ, bin9_comm]
          exact kill_and_pair hk13 hl b a hb10 ha10 hab (by rwa [← hφ'])
      · apply hkill_not_proper
        have hb0 : wireBase b = cFalse := by
          unfold wireBase; rw [dif_neg (by omega), if_neg (by omega)]
        rw [hφ, hb0, (bin9_laws _).2.2.1]; exact fun h => h.1 rfl
    · apply hkill_not_proper
      have ha0 : wireBase a = cFalse := by
        unfold wireBase; rw [dif_neg (by omega), if_neg (by omega)]
      rw [hφ, ha0, bin9_comm, (bin9_laws _).2.2.1]; exact fun h => h.1 rfl
  · rw [hin] at hg1_len; simp at hg1_len

end Main3346
namespace Glue4471
open PEqualNP.CircuitLowerBounds

theorem parent : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → (16 : ℕ) ≤ x1.size :=
  Main3346.finalBound

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, by
      rw [List.foldl_cons, ht]; simp⟩

def ext (C : Circuit) (p q : ℕ) : Circuit :=
  ⟨⟨GateOp.or, [4, 6]⟩ :: ⟨GateOp.and, [p, q]⟩ :: C.gates, C.output⟩

def inp (x : Fin 9 → Bool) (p q : ℕ) : List Bool :=
  (List.ofFn x ++ [x 4 || x 6]) ++
    [(List.ofFn x ++ [x 4 || x 6]).getD p false && (List.ofFn x ++ [x 4 || x 6]).getD q false]

theorem ext_wires (C : Circuit) (p q : ℕ) (x : Fin 9 → Bool) :
    (ext C p q).wires (List.ofFn x) = C.wires (inp x p q) := by
  have h4 : (List.ofFn x).getD 4 false = x 4 := by simp [List.getD_eq_getElem?_getD]
  have h6 : (List.ofFn x).getD 6 false = x 6 := by simp [List.getD_eq_getElem?_getD]
  unfold ext Circuit.wires inp
  simp only [List.foldl_cons, List.map_cons, List.map_nil, GateOp.eval, h4, h6, List.all_cons,
    List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]

theorem ext_nine (C : Circuit) (p q : ℕ) (x : Fin 9 → Bool) :
    ((ext C p q).wires (List.ofFn x)).getD 9 false = (x 4 || x 6) := by
  rw [ext_wires]
  obtain ⟨t, ht⟩ := fold_prefix C.gates (inp x p q)
  unfold Circuit.wires
  rw [ht]
  unfold inp
  simp [List.getD_eq_getElem?_getD, List.getElem?_append]

theorem ext_fan (C : Circuit) (p q : ℕ) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (ext C p q) := by
  intro g hg
  unfold ext at hg
  simp only [List.mem_cons] at hg
  rcases hg with rfl | rfl | hg
  · simp
  · simp
  · exact h g hg

end Glue4471
end PEqualNP.Outside.L_meta_4471

theorem PEqualNP.Outside.L_meta_4471 : ∀ (x1 x2 : Fin (11 : ℕ)),   (11 : ℕ) * ↑x1 + ↑x2 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (9 : ℕ), (10 : ℕ), (24 : ℕ), (26 : ℕ), (27 : ℕ), (29 : ℕ), (31 : ℕ), (32 : ℕ), (48 : ℕ), (50 : ℕ), (51 : ℕ), (53 : ℕ), (54 : ℕ), (84 : ℕ), (86 : ℕ), (87 : ℕ), (108 : ℕ), (109 : ℕ), (120 : ℕ)] →     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))];             x4.eval (x8 ++ [x8.getD (↑x1) Bool.false && x8.getD (↑x2) Bool.false]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro p q _ C hfan hsize
  by_contra hne
  have hall : ∀ x : Fin 9 → Bool,
      C.eval (PEqualNP.Outside.L_meta_4471.Glue4471.inp x p q) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  have hbound := PEqualNP.Outside.L_meta_4471.Glue4471.parent
    (PEqualNP.Outside.L_meta_4471.Glue4471.ext C p q)
    (PEqualNP.Outside.L_meta_4471.Glue4471.ext_fan C p q hfan)
    (PEqualNP.Outside.L_meta_4471.Glue4471.ext_nine C p q)
    (by
      funext x
      have hw := PEqualNP.Outside.L_meta_4471.Glue4471.ext_wires C p q x
      have he : PEqualNP.MetaComplexity.circuitFun 9
          (PEqualNP.Outside.L_meta_4471.Glue4471.ext C p q) x =
          C.eval (PEqualNP.Outside.L_meta_4471.Glue4471.inp x p q) := by
        unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
        rw [hw]
        rfl
      rw [he]
      exact hall x)
    rfl
  have hsz : (PEqualNP.Outside.L_meta_4471.Glue4471.ext C p q).size = C.size + 2 := by
    unfold PEqualNP.Outside.L_meta_4471.Glue4471.ext PEqualNP.CircuitLowerBounds.Circuit.size
    simp
  omega
