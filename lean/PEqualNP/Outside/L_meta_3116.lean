import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3116
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
def raw0 : Sig:=(0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def raw1 : Sig:=(0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def raw2 : Sig:=(0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230)
def raw3 : Sig:=(0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def raw4 : Sig:=(0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def raw5 : Sig:=(0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000,0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def raw6 : Sig:=(0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def raw7 : Sig:=(0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)
def raw : List Sig:=[raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]
inductive Live : Nat->Nat->Finset Sig->Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))
namespace Theta
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
inductive Run {α : Type} (inv : α->α) (meet join : α->α->α) (y : α) : ℕ->List α->Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs->Run inv meet join y s xs->Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)
theorem kept_map {α β : Type} (e : α->β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e=kept b (e x) (xs.map e):= by cases b <;> simp [kept]
lemma Run.map {α β : Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
    {inv' : β->β} {meet' join' : β->β->β}
    (hi : ∀ a,e (inv a)=inv' (e a)) (hm : ∀ a b,e (meet a b)=meet' (e a) (e b))
    (hj : ∀ a b,e (join a b)=join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e):= by
  induction h with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e):= by
      cases neg <;> simp [kept_map,hi]
    rw [e1] at ih; exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)):= by
      cases conj <;> simp [kept_map,hm,hj]
    rw [e1] at ih; exact Run.two conj ka kb ih
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) : xs.length ≤ s+1:= by
  induction h with
  | done=>simp
  | perm hp _ ih=>rwa [←hp.length_eq]
  | one _ save _ ih=>cases save <;> simp_all [kept] <;> omega
  | two _ ka kb _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
abbrev NatRun (m : Nat):=Run (·^^^m) (·&&&·) (·|||·)
lemma q29 {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i=m.testBit j) (hw : ∀ w ∈ xs,w.testBit i=w.testBit j) :
    y.testBit i=y.testBit j:= by
  induction h with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | one neg save _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)
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
  rw [vb,vc] at h; rw [yx]
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hm : (mask 232).testBit i=(mask 232).testBit (232+i):= by
      simp [zn,show i<464 by omega,show 232+i<464 by omega]
    have hy : (goal 232).testBit i ≠ (goal 232).testBit (232+i):= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (s9 ws).testBit i=true:= by
      apply (q11 i ws).2; by_contra! hh; exact hy (q29 h i (232+i) hm hh)
    simp [hc]
  · simp [u4,hi]
lemma q34 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1) (i j : Nat)
    (hw : ∀ a ∈ ws,a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j:= by
  induction h with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (hp.length_eq.trans hl) (fun a ha=>hw a (hp.mem_iff.1 ha))
  | one _ save h _=>have hh:=run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had; simp only [kept,Bool.false_eq_true,ite_false,List.mem_cons] at had
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
  rw [vb,vc] at h; rw [yx]
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hy : ¬ (goal 232).testBit (232+i) ≤ (goal 232).testBit i:= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (rd ws).testBit i=true:= by
      apply (zu i hi ws).2; by_contra! hh; apply hy
      apply q34 h hl; intro a ha; specialize hh a ha
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
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length:= by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩; rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have hrun:=Run.perm ((y1 pr save a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases save with
  | false =>
    simp only [kept,Bool.false_eq_true,ite_false] at ht hrun hcov
    have hlen : ((if neg then a^^^q7 else a) :: ws.erase a).length=ws.length:= by
      simp [List.length_erase_of_mem ha]; omega
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
      simp [List.length_erase_of_mem ha]; omega
    have hlen_eq : decide (((if neg then a^^^q7 else a) :: a :: ws.erase a).length=s+1)=decide (ws.length=s):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
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
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hlenr : ((ws.erase a).erase b).length=ws.length - 2:= by
    have:=pr.length_eq; omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩; rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have hrun:=Run.perm ((y1 (y1 pr kb b) ka a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases ka <;> cases kb
  · simp only [kept,Bool.false_eq_true,ite_false] at ht hh hrun hcov
    have hlen : ((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=ws.length - 1:= by
      simp [hlenr]; omega
    have hle : decide (((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s+2):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
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
      simp [hlenr]; omega
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
      simp [hlenr]; omega
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
      simp [hlenr]; omega
    have hle : decide (((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
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
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
lemma q1f {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t=0->ws=[y]:= by
  induction h with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one=>simp
  | two=>simp
lemma y0 {t ws} (h : NatRun q7 qe t ws) :
    ∀ s,t=s+1->∀ zs,ws.Perm zs->∀ f : Bool->List Nat->Bool,
      (∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true)->vy s zs f=true:= by
  induction h with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | one _ _ h _=>intro s he zs p f hf; cases he; exact q08 p h f hf
  | two _ _ _ h _=>intro s he zs p f hf; cases he; exact q07 p h f hf
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
  let x:=b.toNat+c.toNat; let y:=(!e).toNat+(!f).toNat
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
  | swap=>simp; omega
  | trans _ _ ih1 ih2=>exact ih1.trans ih2
lemma q01 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (v : Nat->Nat) (hand : ∀ a b,v (a&&&b) ≤ v a+v b)
    (hor : ∀ a b,v (a|||b) ≤ v a+v b) : v y ≤ (ws.map v).sum:= by
  induction h with
  | done=>simp
  | perm p _ ih=>rw [← q05 (p.map v)]; exact ih (p.length_eq.trans hl)
  | one _ save h _=>have hh:=run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc,← hand]; exact ih' | grw [← Nat.add_assoc,← hor]; exact ih'
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
  · intro v w; simp only [q0e,Nat.testBit_and]; exact q0q _ _ _ _ _ _ _ _ _ _ _ _
  · intro v w; simp only [q0e,Nat.testBit_or]; exact q1g _ _ _ _ _ _ _ _ _ _ _ _
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
  rw [Bool.eq_false_iff]; intro hk
  obtain ⟨t,ht,hlt⟩:=List.any_eq_true.mp hk
  have hg:=beq_iff_eq.mp (List.all_eq_true.mp zy t ht)
  have hb:=q0f h hl t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2
  have hs:=zo t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 ws 0 hlt
  rw [hg] at hb; omega
def span (f : Nat->Bool) : Nat->Nat->Bool
  | 0,_=>true
  | n+1,i=>f i&&span f n (i+1)
theorem span_ok {f n o} (h : span f n o=true) : ∀ i,o ≤ i->i<o+n->f i=true:= by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem span_join {f a o b} (ha : span f a o=true) (hb : span f b (o+a)=true) :
    span f (a+b) o=true:= by
  induction a generalizing o with
  | zero=>simpa using hb
  | succ a ih =>
    simp only [span,Bool.and_eq_true] at ha; rw [Nat.succ_add,span,Bool.and_eq_true]
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
      else let b:=c>>>11; if op=1 then zf fuel a&&&zf fuel b else zf fuel a|||zf fuel b
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
  | w :: t=>let x:=(w % 1048573+317+salt) % 1048573; (x*x*x) % 1048573+sg salt t
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
  unfold yd; split
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
      (let v:=q16 s zs; !(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4)))))
lemma zc {s i} (hb : qh s i=true)
    (h : NatRun q7 qe s (vj s i)) :
    ∃ q<s,∃ j<q25 q,NatRun q7 qe q (vj q j):= by
  cases s with
  | zero=>simp [qh,q1f h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tight : Bool) (zs : List Nat):=!(tight&&q0x zs) &&
      (let v:=q16 s zs; !(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4))))
    have hF (zs) (hz : NatRun q7 qe s zs) : F (decide (zs.length=s+1)) zs=true:= by
      simp only [F,Bool.and_eq_true,Bool.not_eq_true']
      constructor
      · by_cases hl : zs.length=s+1
        · simp [hl,q1n hz hl]
        · simp [hl]
      · simp only [Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj; by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (q0v _ hz))
    have hN:=y0 h s rfl _ (List.Perm.refl _) F hF
    change !(vy _ _ F)=true at hb; rw [hN] at hb; contradiction
lemma q0k {cap : Nat}
    (hc : ∀ s ≤ cap,∀ i<q25 s,qh s i=true) :
    ∀ s ≤ cap,∀ i<q25 s,¬ NatRun q7 qe s (vj s i):= by
  intro s; induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩:=zc (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h
set_option maxHeartbeats 0 in lemma q3h :
    qh 0 0=true/\qh 1 0=true/\qh 2 0=true ∧
    qh 3 0=true/\qh 4 0=true/\qh 5 0=true:= by decide +kernel
set_option maxHeartbeats 0 in lemma z6 : span (qh 6) 19 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3s : span (qh 7) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3r : span (qh 7) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3q : span (qh 7) 92 200=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3p : span (qh 8) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3o : span (qh 8) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3n : span (qh 8) 100 200=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3m : span (qh 8) 65 300=true:= by decide +kernel
set_option maxHeartbeats 0 in lemma z9 : span (qh 9) 26 0=true:= by decide +kernel
set_option maxHeartbeats 0 in lemma q3z : span (qh 10) 1 0=true:= by decide +kernel
lemma z7 : span (qh 7) 292 0=true:=(@span_join (qh 7) 100 0 192 q3s (@span_join (qh 7) 100 100 92 q3r q3q))
lemma z8 : span (qh 8) 365 0=true:=(@span_join (qh 8) 200 0 165 (@span_join (qh 8) 100 0 100 q3p q3o) (@span_join (qh 8) 100 200 65 q3n q3m))
lemma q2x (s : Nat) (hs : s ≤ 10) : ∀ i<q25 s,qh s i=true:= by
  interval_cases s
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.2.2
  · exact fun i hi=>span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok q3z i (Nat.zero_le i) hi
theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs517) : False:= by
  rw [← vb,← vc] at h
  have h10 : NatRun q7 qe 10 xs517:=q10 h hs
  have p : xs517.Perm (vj 10 0):= by decide +kernel
  exact q0k q2x 10 (by decide) 0 (by decide) (Run.perm p h10)
theorem noSub {s : Nat} {ws : List Nat} (hs : s ≤ 10) (hsub : ws.Sublist xs517)
    (h : NatRun (mask 232) (goal 232) s ws) : False:= by
  by_cases eq : ws=xs517
  · subst ws; exact noRunFull _ hs h
  · rw [← vb,← vc] at h
    exact yn _ (List.mem_sublists.2 hsub) eq (vl h)
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
  rw [y6]; exact Nat.testBit_two_pow_sub_one 252 j
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
  rw [qg]; simp [show ¬ j<252 by omega]
lemma xm {x : Nat} (hx : qr x) : qr (rm x):=fun j hj=>by
  rw [uw hx]; simp [show ¬ j<252 by omega]
lemma s4 {x y : Nat} (hx : qr x) : qr (x&&&y):=fun j hj=>by
  rw [Nat.testBit_and,hx j hj]; rfl
lemma uz {x y : Nat} (hx : qr x) (hy : qr y) : qr (x|||y):=fun j hj=>by
  rw [Nat.testBit_or,hx j hj,hy j hj]; rfl
lemma q0s {x y : Nat} (hx : qr x) (hy : qr y) : qr (x^^^y):=fun j hj=>by
  rw [Nat.testBit_xor,hx j hj,hy j hj]; rfl
lemma uj {x : Nat} (h : x ≤ rx) : qr x:=fun j hj=>by
  have hlt : x<2 ^ 252:= by
    have hp : 0<2 ^ 252:=Nat.pow_pos (by omega)
    rw [y6] at h; omega
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
    rw [Nat.testBit_and,qg]; by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.1 j (by omega)]
  have hn1 : n&&&rx=n:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_and,qg]; by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.2 j (by omega)]
  have hp2 : p|||rx=rx:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_or,qg]; by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.1 j (by omega)]
  have hn2 : n|||rx=rx:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_or,qg]; by_cases hj : j<252
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
    apply Nat.eq_of_testBit_eq; intro j
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
inductive qy : Nat->Nat->Finset q0->Prop
  | stop : qy 0 0 {qc}
  | unary {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)) :
      qy (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)) :
      qy (k+1) t (insert a (insert b U))
lemma z5 {k t : Nat} {S : Finset Sig} (h : Live k t S) :
    qy k t (S.image y7):= by
  induction h with
  | stop=>simpa [q0t] using qy.stop
  | @unary k t U a ha hf _ ih =>
    simp only [Finset.image_insert,q13] at ih ⊢
    have hf' : qx (y7 a) ∉ insert (y7 a) (U.image y7):= by
      rw [← Finset.image_insert,← q13]
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hf (xn he ▸ hy)
    exact qy.unary (xc ha) hf' ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    simp only [Finset.image_insert,q14] at ih ⊢
    have hf' : qn d (y7 a) (y7 b) ∉ insert (y7 a) (insert (y7 b) (U.image y7)):= by
      rw [← Finset.image_insert,← Finset.image_insert,← q14]
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hf (xn he ▸ hy)
    exact qy.binary (xc ha) (xc hb) (fun e=>hab (xn e)) hf' ih
lemma q00 {a : Sig} (ha : a ∈ raw) : y7 a ∈ rj:= by
  have h : raw.map y7=rj:= by decide +kernel
  rw [← h]; exact List.mem_map_of_mem ha
def r9 (d : Bool) (a : q0) : Nat :=
  if d then a.1^^^a.2 else a.1&&&rm a.2
def q9 (d : Bool) : List q0->Nat
  | []=>0
  | a :: l=>r9 d a|||q9 d l
def rg (a b : q0) : Bool:=Nat.beq a.1 b.1&&Nat.beq a.2 b.2
lemma rf (a b : q0) : rg a b=true ↔ a=b:= by
  cases a; cases b; simp only [rg,Bool.and_eq_true,Nat.beq_eq,Prod.mk.injEq]
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
    exact List.nodup_cons.mpr ⟨fun hm=>by rw [(y5 x xs).mpr hm] at h; exact Bool.false_ne_true h.1.symm,ih h.2⟩
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
      | none=>rw [hr] at h; contradiction
      | some r' =>
        rw [hr] at h; injection h with h; subst h
        exact ((ih hr).cons y).trans (List.Perm.swap _ _ _)
    · rw [he] at h; injection h with h; subst h
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
    | none=>rw [he] at h; contradiction
    | some ys'=>rw [he] at h; exact ((ih h).cons x).trans (yq he).symm
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
    · subst h; rw [(rf a a).mpr rfl]; simp [ih]
    · have hf : rg a x=false:= by cases he : rg a x; rfl; exact (h ((rf a x).mp he)).elim
      have hne : decide (x=a)=false:=decide_eq_false (Ne.symm h)
      rw [hf,hne]; simp [ih]
lemma q0g (a b : q0) (v : List q0) : ug a b v=qw [a,b] v:= by
  induction v with
  | nil=>rfl
  | cons x xs ih =>
    simp only [ug,qw,List.filter_cons,List.contains_eq_mem,List.mem_cons,List.not_mem_nil,or_false] at ih ⊢
    by_cases h : a=x\/b=x
    · have ht : (rg a x||rg b x)=true:= by
        rcases h with rfl | rfl <;> simp [(rf _ _).mpr rfl]
      have hm : decide (x=a\/x=b)=true:=decide_eq_true (by rcases h with rfl | rfl <;> simp)
      rw [ht,hm]; simp [ih]
    · have ha : a ≠ x:=fun e=>h (Or.inl e)
      have hb : b ≠ x:=fun e=>h (Or.inr e)
      have hfa : rg a x=false:= by cases he : rg a x; rfl; exact (ha ((rf a x).mp he)).elim
      have hfb : rg b x=false:= by cases he : rg b x; rfl; exact (hb ((rf b x).mp he)).elim
      have hm : decide (x=a\/x=b)=false:=decide_eq_false (by rintro (rfl | rfl); exact ha rfl; exact hb rfl)
      rw [hfa,hfb,hm]; simp [ih]
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
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i<252
  · simp only [vr,r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
    cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
  · have hge : 252 ≤ i:= by omega
    simp [vr,r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hc.1 i hge]
lemma q32 {c : y3} {a b : Nat} (hc : sv c) (ha : qr a) (hb : qr b) :
    uc (r0 a (r0 b c)) a b=c.1:= by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i<252
  · simp only [uc,r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
    cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
  · have hge : 252 ≤ i:= by omega
    simp [uc,r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.1 i hge]
lemma zq {c : y3} {a b : Nat} (hc : sv c) (ha : qr a) (hb : qr b) :
    r0 a (r0 b c)=r0 b (r0 a c):= by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [r0,Nat.testBit_or]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> (apply Nat.eq_of_testBit_eq; intro i; by_cases hi : i<252)
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
  | cons a v ih=>change r9 d a|||(qz d v).1=r9 d a|||q9 d v; rw [ih]
lemma vq : qd qc:=⟨z3,by decide,by decide⟩
lemma qv {k t S} (h : qy k t S) : ∀ a ∈ S,qd a:= by
  induction h with
  | stop=>simpa using vq
  | unary ha _ _ ih=>simpa using And.intro ha (fun a h=>ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩
lemma xg {k t S} (h : qy k t S) : t ≤ k/\S.card+t ≤ k+1:= by
  induction h with
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
  induction h with
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
  apply Nat.eq_of_testBit_eq; intro i
  rw [qg]
  by_cases hi : i<252
  · obtain ⟨a,hm,ha⟩:=zh h i hi
    have hmem : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ hm)
    simp only [hi,decide_true]
    exact (ss _ _ _).2 ⟨a,hmem,ha⟩
  · simp only [hi,decide_false]
    rw [Bool.eq_false_iff]; intro ht
    obtain ⟨a,ha,hbit⟩:=(ss _ _ _).1 ht
    have hv : qb a:=(qv h a (he ▸ List.mem_toFinset.mpr ha)).1
    have hf:=rq (decide (0<t)) hv i (by omega)
    rw [hf] at hbit; contradiction
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
    rw [← List.mem_toFinset,he]; simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq; subst b
    simp [s8] at ha; simp [qw] at hb
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
    intro a ha b hb e; subst b
    simp [qw] at hb; exact hb.2 ha
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
  · have l:=p.length_eq; simp at l; omega
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
  · have l:=p.length_eq; simp at l; omega
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
    apply Nat.eq_of_testBit_eq; intro i; rw [qg]
    by_cases hi : i<252
    · obtain ⟨b,hb,h⟩:=zh l i hi
      have ba : b ≠ a:=fun he=>hn (he ▸ hb)
      have hm:=(List.mem_erase_of_ne ba).mpr (hs _ hb)
      simp only [hi,decide_true]
      exact (ss true _ _).mpr ⟨b,hm,yj _ _ _ hi h⟩
    · simp only [hi,decide_false]
      rw [Bool.eq_false_iff]; intro ht
      obtain ⟨b,hb,hbit⟩:=(ss true _ _).mp ht
      have hbv:=rh b (List.mem_of_mem_erase hb)
      have hf:=rq true hbv i (by omega)
      rw [hf] at hbit; contradiction
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
  · subst hx; simp [qu]
  · rw [qu,ite_eq_right hx,u3]; simp
lemma r7 (f : Nat->Nat) (x : Nat) : qr (qu f x):=fun j hj=>by
  rw [ql]; simp [show ¬ j<252 by omega]
lemma sd (f : Nat->Nat) (a b : Nat) :
    qu f (a&&&b)=qu f a&&&qu f b:= by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and,ql]; split_ifs <;> simp
lemma sm (f : Nat->Nat) (a b : Nat) :
    qu f (a|||b)=qu f a|||qu f b:= by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_or,ql]; split_ifs <;> simp
lemma ry (f : Nat->Nat) (hf : ∀ j<252,f j<252) (a : Nat) :
    qu f (rm a)=rm (qu f a):= by
  apply Nat.eq_of_testBit_eq; intro j
  rw [ql,uw (r7 f a),ql]
  by_cases hj : j<252
  · simp [hj,q5 a (hf j hj)]
  · simp [hj]
lemma rr (f : Nat->Nat) : qu f 0=0:= by
  apply Nat.eq_of_testBit_eq; intro j; rw [ql]; split_ifs <;> simp
lemma sh (f : Nat->Nat) (hf : ∀ j<252,f j<252) : qu f rx=rx:= by
  apply Nat.eq_of_testBit_eq; intro j; rw [ql]
  by_cases hj : j<252
  · simp [hj,qg,hf j hj]
  · simp [hj,qg]
lemma ul (f : Nat->Nat) (hf : ∀ j<252,f j<252/\f (f j)=j)
    {a : Nat} (ha : qr a) : qu f (qu f a)=a:= by
  apply Nat.eq_of_testBit_eq; intro j
  rw [ql]
  by_cases hj : j<252
  · have hfj:=hf j hj
    rw [ite_eq_left hj,ql,ite_eq_left hfj.1,hfj.2]
  · rw [ite_eq_right hj]; exact (ha j (by omega)).symm
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
  · intro h0; exact h.2.1 (sf w h.1 vg (h0.trans (xw w).symm))
  · intro h1; exact h.2.2 (sf w h.1 q0r (h1.trans (q0l w).symm))
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
  | nil=>intro j _; rfl
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
  rh a (by simp only [qf,rj,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; tauto)
lemma sy (b : Bool) (l : List Nat) (hl : ∀ j ∈ l,j<8)
    (hp : (l.map (u8 b)).Perm l) :
    ((l.map si).map (qj b)).Perm (l.map si):= by
  have heq : (l.map si).map (qj b)=(l.map (u8 b)).map si:= by
    rw [List.map_map,List.map_map]
    exact List.map_congr_left fun j hj=>x8 b ⟨j,hl j hj⟩
  rw [heq]; exact hp.map si
lemma yb (b : Bool) : (qf.map (qj b)).Perm qf:= by
  change (([0,3,5,6].map si).map (qj b)).Perm ([0,3,5,6].map si)
  exact sy b [0,3,5,6] (by decide) (by cases b <;> decide)
lemma x0 (b : Bool) {a : q0} (ha : qb a) :
    qj b a ∈ qf ↔ a ∈ qf:= by
  have hp:=yb b
  rw [← hp.mem_iff]
  constructor
  · intro hm; obtain ⟨x,hx,he⟩:=List.mem_map.mp hm
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
      rw [List.map_map]; rfl
    rw [hm]; exact (hs.map (q1 t)).trans ih
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
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor,hmask,uv,uv]
  by_cases hl : j<232
  · simp [hl,qx,q5 _ (show j<252 by omega),show j<464 by omega]
  · by_cases hh : j<464
    · simp [hl,hh,qx,q5 _ (show j - 232<252 by omega)]
    · simp [hl,hh]
lemma x2 (d : Bool) (a b : q0) :
    r4 (qn d a b)=if d then r4 a|||r4 b else r4 a&&&r4 b:= by
  apply Nat.eq_of_testBit_eq; intro j
  cases d <;> simp only [qn,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_or,
    Nat.testBit_and,uv] <;> split_ifs <;> rfl
lemma q1m {k t S} (h : qy k t S) (v : List q0) (hv : v.Nodup)
    (he : v.toFinset=S) :
    Theta.Run qx (qn false) (qn true) qc k v:= by
  induction h generalizing v with
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
    let sa:=decide (a ∈ U); let sb:=decide (b ∈ U)
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
  have h:=xx; rw [← uk] at h; exact List.Nodup.of_map _ h
lemma q04 (i : Fin 4) :
    rj.toFinset.image (q3 i)=insert rv rc.toFinset:= by
  have hact : rj.toFinset.image (r1 (sp i))=rj.toFinset:= by
    ext x; simp only [Finset.mem_image,List.mem_toFinset]
    have hp:=y2 (uu (sp i))
    rw [← hp.mem_iff,List.mem_map]; rfl
  have hcomp : rj.toFinset.image (q3 i)=rj.toFinset.image xt:= by
    calc rj.toFinset.image (q3 i)
        = (rj.toFinset.image (r1 (sp i))).image xt:= by
          rw [Finset.image_image]; rfl
      _=rj.toFinset.image xt:= by rw [hact]
  have hm : rc.toFinset=vi.toFinset.image xt:= by
    ext a; simp [rc,Finset.mem_image,List.mem_map]
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
  · rw [s0]; cases d <;> simp_all
  · rw [s0]; cases d <;> simp_all
  rcases s2 hbV hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
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
          intro v hv; obtain ⟨hne,hmv⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hmv
        have hf : qx a ∉ insert a U:= by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qy.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (qn d a b)
        have ht : qy k t (insert (qn d a b) U):= by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:= by
          intro v hv; obtain ⟨hne,hmv⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hmv
        have hf : qn d a b ∉ insert a (insert b U):= by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qy.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha; have hn : a ≠ z:=fun hh=>hm (hh ▸ ha); simpa [hn] using sub a ha
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
    ext a; simp only [v,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
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
  obtain ⟨m,hm,t,T,hl,hs⟩:=h; exact ⟨m,hm.trans hk,t,T,hl,hs⟩
lemma x5 {i : Fin 4} {q : Nat} {S S' : Finset q0} {g : q0}
    (hs : S' ⊆ insert g S)
    (hr : qm (S.image (q3 i)).toList (q3 i g) ∨
      yc (S.image (q3 i)).toList (q3 i g))
    (h : qp i q S') : qp i (q+1) S:= by
  obtain ⟨m,hm,t,T,hl,ht⟩:=h
  have sub : ∀ a ∈ T,a ∈ (S.image (q3 i)).toList++[q3 i g]:= by
    intro a ha; obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (ht ha)
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
  intro a ha; obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp=>hp (qv hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb
lemma va {i : Fin 4} {q : Nat} {a : q0} {U : Finset q0}
    (h : qp i q (insert (qx a) U)) : qp i (q+1) (insert a U):= by
  apply x5 (g:=qx a) (by simp [Finset.insert_subset_iff]; exact fun _ h=>by simp [h]) _ h
  rw [uo]
  exact q30 _ _ (re i a) (by simp)
lemma un {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : qp i q (insert (qn d a b) U)) : qp i (q+1) (insert a (insert b U)):= by
  apply x5 (g:=qn d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h=>by simp [h]) _ h
  rw [vn]
  exact q35 _ (re i a) (re i b) (Or.inl (by simp)) (Or.inl (by simp))
lemma xj {i : Fin 4} {q : Nat} {a : q0} {U : Finset q0}
    (ha : ¬ qd (q3 i a)) (h : qp i q (insert (qx a) U)) :
    qp i q (insert a U):= by
  apply x6 (g:=qx a) (by simp [Finset.insert_subset_iff]; exact fun _ h=>by simp [h]) _ h
  rcases s2 (re i a) (Or.inr ha : qm [] (q3 i a)) with hz | ho | hm
  · exact Or.inr (fun hp=>hp.2.2 (by rw [uo,hz,v6.1]))
  · exact Or.inr (fun hp=>hp.2.1 (by rw [uo,ho,v6.2]))
  · simp at hm
lemma rn {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (ha : ¬ qd (q3 i a)) (h : qp i q (insert (qn d a b) U)) :
    qp i q (insert a (insert b U)):= by
  apply x6 (g:=qn d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h=>by simp [h]) _ h
  rw [vn,s0]
  have hbv:=re i b
  rcases s2 (re i a) (Or.inr ha : qm [] (q3 i a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp=>hp.2.1 (so hbv).2.2.1)
    · rw [(so hbv).2.1]; exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(so hbv).1]; exact Or.inl (by simp)
    · exact Or.inr (fun hp=>hp.2.2 (so hbv).2.2.2.1)
  · simp at hm
lemma uq {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (hb : ¬ qd (q3 i b)) (h : qp i q (insert (qn d a b) U)) :
    qp i q (insert a (insert b U)):= by
  rw [s0] at h; rw [Finset.insert_comm]; exact rn hb h
lemma ud {k t : Nat} {S : Finset q0} (h : qy k t S) (i : Fin 4) :
    qp i k S:= by
  induction h with
  | stop=>refine ⟨0,Nat.le_refl _,0,{qc},qy.stop,?_⟩; simp [vm]
  | unary _ _ _ ih=>exact va ih
  | binary _ _ _ _ _ ih=>exact un ih
lemma ue {k t : Nat} {S : Finset q0} (h : qy k t S)
    (i : Fin 4) (a : q0) (ha : a ∈ S) (hc : ¬ qd (q3 i a)) :
    ∃ q<k,qp i q S:= by
  induction h with
  | stop =>
    have ht : a=qc:=Finset.mem_singleton.mp ha
    exact (hc (by rw [ht,vm]; exact vq)).elim
  | @unary k t U b _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k,by omega,xj hc (ud tail i)⟩
    · obtain ⟨q,hq,h⟩:=ih (Finset.mem_insert_of_mem ha); exact ⟨q+1,by omega,va h⟩
  | @binary k t U b c d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k,by omega,rn hc (ud tail i)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k,by omega,uq hc (ud tail i)⟩
      · obtain ⟨q,hq,h⟩:=ih (Finset.mem_insert_of_mem hU); exact ⟨q+1,by omega,un h⟩
def r3 (k : Nat) (S : Finset q0) : Prop :=
  ∀ i q,q+(if s5 i ∈ S then 1 else 0)<k->¬ qp i q S
lemma xf {k : Nat} (hk : k ≤ 12) : r3 k rj.toFinset:= by
  intro i q hq h; rw [ite_eq_left (x4 i)] at hq
  exact v2 i (za h (by omega))
lemma xu (a : q0) : a ∈ qf ↔ ∃ i,s5 i=a:= by
  rw [← List.mem_ofFn]; rfl
lemma q0j {k : Nat} {a : q0} {U : Finset q0}
    (h : r3 (k+1) (insert a U)) : r3 k (insert (qx a) U):= by
  intro i q hq hf
  by_cases hp : s5 i ∈ insert a U
  · by_cases ht : s5 i ∈ insert (qx a) U
    · rw [ite_eq_left ht] at hq; exact h i (q+1) (by simp [hp]; omega) (va hf)
    · rw [ite_eq_right ht] at hq
      have he : s5 i=a :=
        (Finset.mem_insert.mp hp).resolve_right (fun hm=>ht (Finset.mem_insert_of_mem hm))
      have hz : ¬ qd (q3 i a):= by rw [← he,r8]; exact fun hz=>hz.2.1 rfl
      exact h i q (by simp [hp]; omega) (xj hz hf)
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (va hf)
lemma zv {k : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : r3 (k+1) (insert a (insert b U))) : r3 k (insert (qn d a b) U):= by
  intro i q hq hf
  by_cases hp : s5 i ∈ insert a (insert b U)
  · by_cases ht : s5 i ∈ insert (qn d a b) U
    · rw [ite_eq_left ht] at hq; exact h i (q+1) (by simp [hp]; omega) (un hf)
    · rw [ite_eq_right ht] at hq
      rcases Finset.mem_insert.mp hp with ha | hb
      · have hz : ¬ qd (q3 i a):= by rw [← ha,r8]; exact fun hz=>hz.2.1 rfl
        exact h i q (by simp [hp]; omega) (rn hz hf)
      · rcases Finset.mem_insert.mp hb with hb | hU
        · have hz : ¬ qd (q3 i b):= by rw [← hb,r8]; exact fun hz=>hz.2.1 rfl
          exact h i q (by simp [hp]; omega) (uq hz hf)
        · exact (ht (Finset.mem_insert_of_mem hU)).elim
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (un hf)
lemma xz {k t : Nat} {a : q0} {U : Finset q0}
    (h : r3 (k+1) (insert a U)) (tail : qy k t (insert (qx a) U)) :
    a ∉ qf:= by
  intro hm; obtain ⟨i,rfl⟩:=(xu _).mp hm
  have hz : ¬ qd (q3 i (s5 i)):= by rw [r8]; exact fun hz=>hz.2.1 rfl
  have ho : ¬ qd (q3 i (qx (s5 i))):= by
    rw [uo,r8,v6.1]; exact fun hp=>hp.2.2 rfl
  obtain ⟨q,hq,hf⟩:=ue tail i (qx (s5 i)) (Finset.mem_insert_self _ _) ho
  exact h i q (by simp; omega) (xj hz hf)
lemma xp {k t : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : r3 (k+1) (insert a (insert b U))) (tail : qy k t (insert (qn d a b) U)) :
    (a ∈ qf->d=true/\a ∉ U)/\(b ∈ qf->d=true/\b ∉ U):= by
  have leftSide {a b : q0} (h : r3 (k+1) (insert a (insert b U)))
      (tail : qy k t (insert (qn d a b) U)) (hm : a ∈ qf) : d=true/\a ∉ U:= by
    obtain ⟨i,rfl⟩:=(xu _).mp hm
    have hz : ¬ qd (q3 i (s5 i)):= by rw [r8]; exact fun hz=>hz.2.1 rfl
    constructor
    · cases d
      · exfalso
        have ho : ¬ qd (q3 i (qn false (s5 i) b)):= by
          rw [vn,r8,s0,(so (re i b)).2.2.1]
          exact fun hp=>hp.2.1 rfl
        obtain ⟨q,hq,hf⟩:=ue tail i _ (Finset.mem_insert_self _ _) ho
        exact h i q (by simp; omega) (rn hz hf)
      · rfl
    · intro hU
      obtain ⟨q,hq,hf⟩:=ue tail i _ (Finset.mem_insert_of_mem hU) hz
      exact h i q (by simp; omega) (rn hz hf)
  refine ⟨leftSide h tail,?_⟩
  apply leftSide (a:=b) (b:=a)
  · rwa [Finset.insert_comm]
  · rwa [s0]
inductive q2 : Nat->Nat->Finset q0->Prop
  | stop : q2 0 0 {qc}
  | unary {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf)
      (tail : q2 k t (insert (qx a) U)) :
      q2 (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf->d=true/\a ∉ U)
      (hrb : b ∈ qf->d=true/\b ∉ U)
      (tail : q2 k t (insert (qn d a b) U)) :
      q2 (k+1) t (insert a (insert b U))
lemma q2.nlive {k t S} (h : q2 k t S) : qy k t S:= by
  induction h with
  | stop=>exact qy.stop
  | unary ha hf _ _ ih=>exact qy.unary ha hf ih
  | binary ha hb hab hf _ _ _ ih=>exact qy.binary ha hb hab hf ih
lemma yl {k t S} (h : qy k t S) (hb : r3 k S) : q2 k t S:= by
  induction h with
  | stop=>exact q2.stop
  | unary ha hf tail ih =>
    exact q2.unary ha hf (xz hb tail) (ih (q0j hb))
  | binary ha hg hab hf tail ih =>
    obtain ⟨h1,h2⟩:=xp hb tail
    exact q2.binary ha hg hab hf h1 h2 (ih (zv hb))
lemma xe (w : List Bool) {k t : Nat} {S : Finset q0}
    (h : q2 k t S) : q2 k t (S.image (q1 w)):= by
  induction h with
  | stop=>simpa [vu] using q2.stop
  | @unary k t U a ha hf hr tail ih =>
    have hU : ∀ x ∈ U,qb x:=fun x hx =>
      (qv tail.nlive x (Finset.mem_insert_of_mem hx)).1
    simp only [Finset.image_insert,us] at ih ⊢
    have hne : qx (q1 w a) ∉ insert (q1 w a) (U.image (q1 w)):= by
      rw [← Finset.image_insert,← us]
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
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
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      have hyV : qb y:= by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact ha.1
        rcases Finset.mem_insert.mp hy with rfl | hu
        · exact hb.1
        · exact hU y hu
      exact hf (sf w hyV (x9 d ha.1 hb.1) he ▸ hy)
    have hm (v : q0) (hvV : qb v) (hv : v ∉ U) : q1 w v ∉ U.image (q1 w):= by
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hv (sf w (hU y hy) hvV he ▸ hy)
    refine q2.binary (ui w ha) (ui w hb)
      (fun e=>hab (sf w ha.1 hb.1 e)) hne ?_ ?_ ih
    · intro hx; obtain ⟨h1,h2⟩:=hra ((s1 w ha.1).mp hx)
      exact ⟨h1,hm _ ha.1 h2⟩
    · intro hx; obtain ⟨h1,h2⟩:=hrb ((s1 w hb.1).mp hx)
      exact ⟨h1,hm _ hb.1 h2⟩
lemma sj (t : Nat) : (!Nat.beq t 0)=decide (0<t):= by cases t <;> rfl
def rs (v : List q0) (g : q0) : Bool :=
  !(up g v)&&!(Nat.beq g.1 0&&Nat.beq g.2 0)&&!(Nat.beq g.1 rx&&Nat.beq g.2 rx)
lemma xi {v : List q0} {g : q0} (hg : g ∉ v) (hp : qd g) :
    rs v g=true:= by
  have hm : up g v=false:= by
    cases e : up g v; rfl; exact (hg ((y5 g v).mp e)).elim
  have h0 : (Nat.beq g.1 0&&Nat.beq g.2 0)=false:= by
    cases e : (Nat.beq g.1 0&&Nat.beq g.2 0); rfl
    simp only [Bool.and_eq_true,Nat.beq_eq] at e; exact (hp.2.1 (Prod.ext e.1 e.2)).elim
  have h1 : (Nat.beq g.1 rx&&Nat.beq g.2 rx)=false:= by
    cases e : (Nat.beq g.1 rx&&Nat.beq g.2 rx); rfl
    simp only [Bool.and_eq_true,Nat.beq_eq] at e; exact (hp.2.2 (Prod.ext e.1 e.2)).elim
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
    (let g:=(a.1&&&b.1,a.2&&&b.2); rs v g&&r (g :: ug a b v))) ||
  (Nat.beq (ua&&&b.2) 0&&Nat.beq (ub&&&a.2) 0 &&
    (let g:=(a.1|||b.1,a.2|||b.2); rs v g&&r (g :: ug a b v)))
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
    rw [← cv]; ac_rfl
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
      cases e : Nat.beq rest.length (k - t); rfl; exact (tight (Nat.beq_eq.mp e)).elim
    simp only [v7,sj,hnt,Bool.false_eq_true,ite_false,List.any_eq_true,
      Bool.and_eq_true,Nat.ble_eq,Nat.beq_eq,hav,and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩
lemma x1 {c : y3} {a b : q0} (hc : sv c)
    (op : Bool) (h : r9 false (qn op a b)|||uc c (r9 false a) (r9 false b)=rx) :
    ((c.2.1&&&r9 false a)&&&(if op then b.2 else rm b.1)) |||
    ((c.2.1&&&r9 false b)&&&(if op then a.2 else rm a.1))=0:= by
  apply Nat.eq_of_testBit_eq; intro i
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
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢; exact hi.1
    have h2 : (c.2.1&&&r9 false b)&&&rm a.1=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢; exact hi.2
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · have h0:=x1 hc true hcov
    have h1 : (c.2.1&&&r9 false a)&&&b.2=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢; exact hi.1
    have h2 : (c.2.1&&&r9 false b)&&&a.2=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢; exact hi.2
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩
lemma zz {m t k : Nat} {U : Finset q0} {a : q0} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a U) (hle : m ≤ k)
    (fresh : qx a ∉ insert a U) (ha : a ∉ qf) (l : q2 m t (insert (qx a) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qx a) U->r v=true) :
    yf k t v.length r v=true:= by
  let h:=s8 U [a]; let rest:=qw [a] v
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩:=vz (del:=[a]) (U:=U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn; change (h++rest).toFinset=U at eq
  have nn : qx a ∉ v:=fun hm=>fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : qx a ∉ U:=fun hm=>fresh (Finset.mem_insert_of_mem hm)
  have hnd : (qx a :: (h++rest)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm=>nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (qx a :: (h++rest)).toFinset=insert (qx a) U:= by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]]:= by by_cases hm : a ∈ U <;> simp [h,s8,hm]
  apply List.any_eq_true.mpr; refine ⟨a,ah,?_⟩
  unfold q12; rw [sj,q0h]
  obtain ⟨hlen,hmask⟩:=q2b (decide (0<t)) hv hval ah
  rw [hlen,hmask]; apply Bool.and_eq_true_iff.mpr
  have hna : qa a=false:= by cases es : qa a; rfl; exact (ha ((ri a).mp es)).elim
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
  let g:=qn d a b; let h:=s8 U [a,b]; let rest:=qw [a,b] v
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩:=vz (del:=[a,b]) (U:=U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn; change (h++rest).toFinset=U at eq
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
  unfold u5; dsimp only; rw [q0g,hlen,hmask]
  cases d with
  | false =>
    have na : qa a=false:= by cases es : qa a; rfl; exact (Bool.false_ne_true (hra ((ri a).mp es)).1).elim
    have nb : qa b=false:= by cases es : qa b; rfl; exact (Bool.false_ne_true (hrb ((ri b).mp es)).1).elim
    apply Bool.or_eq_true_iff.mpr; left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr; right
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
  unfold vt; split
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
    have h1 : Nat.blt (S+1) t=false:= by cases e : Nat.blt (S+1) t; rfl; have:=Nat.blt_eq.mp e; omega
    have h2 : Nat.blt (S+2 - t) v.length=false:= by cases e : Nat.blt (S+2 - t) v.length; rfl; have:=Nat.blt_eq.mp e; omega
    simp [h1,h2]
  unfold v0; dsimp only; rw [hcond]; simp only [Bool.false_eq_true,ite_false,sj]
  cases h with
  | stop =>
    have p : v.Perm [qc]:=List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    rw [List.perm_singleton.mp p]; simp [u1,(rf qc qc).mpr rfl]
  | @unary m t U a _ hf hr tail =>
    apply Bool.or_eq_true_iff.mpr; left
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp,zz hv hval he (by omega) hf hr tail ?_⟩
    intro w hn hs; exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d _ _ hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr; right
    apply zw hv hval he (by omega) hab hf hra hrb tail
    intro w hn hs; exact hb' w hn m (by omega) (hs.symm ▸ tail)
lemma y9 {m t : Nat} {S : Finset q0} (h : q2 m t S) (k : Nat)
    (hk : m ≤ k) (v : List q0) (hv : v.Nodup) (hs : v.toFinset=S) : xd k t v=true:= by
  induction k generalizing m t S v with
  | zero =>
    have hm : m=0:= by omega
    subst m; cases h
    have p : v.Perm [qc]:=List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    rw [List.perm_singleton.mp p]; simp [xd,u1,(rf qc qc).mpr rfl]
  | succ k ih =>
    rw [xd]
    apply xq h hk hv hs <;> exact fun w hn l hl hh=>ih hh hl w hn rfl
def qs (k t : Nat) (v : List q0) : Prop :=
  ∀ m ≤ k,¬ q2 m t v.toFinset
lemma yy {k t : Nat} {v : List q0} (hv : v.Nodup) (hc : xd k t v=false) :
    qs k t v:= by
  intro m hm h; exact Bool.false_ne_true (hc.symm.trans (y9 h k hm v hv rfl))
lemma xv {k t : Nat} {v : List q0} {u b : List q0->Bool} (hv : v.Nodup)
    (hu : ∀ w,u w=false->qs k (t - 1) w)
    (hb : ∀ w,b w=false->qs k t w)
    (hc : v0 k t v u b=false) : qs (k+1) t v:= by
  intro m hm h
  have hu' : ∀ w,w.Nodup->∀ j ≤ k,q2 j (t - 1) w.toFinset->u w=true:= by
    intro w _ j hj r; cases e : u w; exact (hu _ e j hj r).elim; rfl
  have hb' : ∀ w,w.Nodup->∀ j ≤ k,q2 j t w.toFinset->b w=true:= by
    intro w _ j hj r; cases e : b w; exact (hb _ e j hj r).elim; rfl
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
  rw [q03 j hj]; simp only [r1,s3 _ j hj]
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
    · rename_i hi; exact xr g i (Nat.blt_eq.mp hi)
    · dsimp only
      split
      · rw [rp g fuel _]; simp only [r1,us]
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
  unfold r6; split
  · intro x hx; rcases List.mem_cons.mp hx with rfl | ht; exact y4 _; exact ha x ht
  · exact ha
lemma qi (e : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ qq (q6 0) e acc,qb x:= by
  unfold qq; split
  · exact ha
  · intro x hx; rcases List.mem_cons.mp hx with rfl | ht; exact rt 5 _; exact ha x ht
lemma qo (g : Fin 8) (code j : Nat) (hj : j<8) (acc : List q0) :
    (r6 (q6 0) code j acc).map (r1 g) =
      r6 (q6 g.val) code j (acc.map (r1 g)):= by
  unfold r6; split <;> simp [xr g j hj]
lemma sl (g : Fin 8) (e : Nat) (acc : List q0) :
    (qq (q6 0) e acc).map (r1 g) =
      qq (q6 g.val) e (acc.map (r1 g)):= by
  unfold qq; split <;> simp [rp]
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
  unfold q8 st; dsimp only
  split
  · exact qi _ (qi _ (ux _ (by simp)))
  · split
    · exact qi _ (qi _ (qi _ (ux _ (by simp))))
    · exact qi _ (qi _ (qi _ (qi _ (ux _ (by simp)))))
lemma xa (g : Fin 8) (k t i : Nat) :
    (q8 k t i).map (r1 g)=st (q6 g.val) k t i:= by
  unfold q8 st; dsimp only
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
  unfold r5 at hw; dsimp only at hw
  split at hw
  · contradiction
  · simp only [Bool.and_eq_true,Nat.blt_eq] at hw
    obtain ⟨hi,hp⟩:=hw
    have hp':=yp hp
    have hlt : (zg k t w - 1)&&&7<8:= by have : (zg k t w - 1)&&&7 ≤ 7:=Nat.and_le_right; omega
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
  · intro w hw; exact rk (hp (t - 1) (by omega)) (by simpa using hw)
  · intro w hw; exact rk (hp t ht) (by simpa using hw)
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3c : Theta.span (rb 8 0) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2v : Theta.span (rb 8 0) 250 250=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2u : Theta.span (rb 8 0) 250 500=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2t : Theta.span (rb 8 0) 250 750=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q1q : Theta.span (rb 8 0) 250 1000=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q1p : Theta.span (rb 8 0) 93 1250=true:= by decide +kernel
lemma q2r : Theta.span (rb 8 0) 1343 0=true:=(@Theta.span_join (rb 8 0) 750 0 593 (@Theta.span_join (rb 8 0) 250 0 500 q3c (@Theta.span_join (rb 8 0) 250 250 250 q2v q2u)) (@Theta.span_join (rb 8 0) 250 750 343 q2t (@Theta.span_join (rb 8 0) 250 1000 93 q1q q1p)))
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3b : Theta.span (rb 8 1) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2s : Theta.span (rb 8 1) 99 250=true:= by decide +kernel
lemma q2q : Theta.span (rb 8 1) 349 0=true:=(@Theta.span_join (rb 8 1) 250 0 99 q3b q2s)
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2p : Theta.span (rb 8 2) 6 0=true:= by decide +kernel
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
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3a : Theta.span (q4 8 0) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2l : Theta.span (q4 8 0) 250 250=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2k : Theta.span (q4 8 0) 102 500=true:= by decide +kernel
lemma q2i : Theta.span (q4 8 0) 602 0=true:=(@Theta.span_join (q4 8 0) 250 0 352 q3a (@Theta.span_join (q4 8 0) 250 250 102 q2l q2k))
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q39 : Theta.span (q4 8 1) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2j : Theta.span (q4 8 1) 128 250=true:= by decide +kernel
lemma q2h : Theta.span (q4 8 1) 378 0=true:=(@Theta.span_join (q4 8 1) 250 0 128 q39 q2j)
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q2g : Theta.span (q4 8 2) 41 0=true:= by decide +kernel
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
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q23 : Theta.span (q4 9 0) 64 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q22 : Theta.span (q4 9 1) 84 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q21 : Theta.span (q4 9 2) 43 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q20 : Theta.span (q4 9 3) 8 0=true:= by decide +kernel
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
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q1x : Theta.span (q4 10 0) 5 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q1w : Theta.span (q4 10 1) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q1v : Theta.span (q4 10 2) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q1u : Theta.span (q4 10 3) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q1t : Theta.span (q4 10 4) 1 0=true:= by decide +kernel
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
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma v3 : vk 0=true/\vk 1=true/\vk 2=true/\vk 3=true/\vk 4=true/\vk 5=true:= by decide +kernel
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
  · intro w hw; exact rk (x7 (t - 1) (by omega)) (by simpa using hw)
  · intro w hw; exact rk (x7 t ht) (by simpa using hw)
theorem no_live12 {k t : Nat} {S : Finset Sig} (hk : k ≤ 12) (h : Live k t S)
    (hsub : ∀ a ∈ S,a ∈ raw) : False:= by
  have hn : qy k t (S.image y7):=z5 h
  have hnsub : ∀ a ∈ S.image y7,a ∈ rj:= by
    intro a ha; obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ha
    exact q00 (hsub x hx)
  have eq:=q1l hn hnsub
  rw [← eq] at hn
  have sz:=xg hn
  rw [List.toFinset_card_of_nodup q19] at sz
  have hlen : rj.length=8:=rfl
  have ht : t ≤ 5:= by omega
  exact yk t ht k hk (yl hn (xf hk))
end Base1007
namespace Main1672
abbrev Sig := Nat × Nat
def top : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def unionSep (d : Bool) : List Sig → Nat
  | [] => 0
  | a :: l => sep d a ||| unionSep d l
def Valid1 (x : Nat) : Prop := ∀ j, 414 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
lemma top_eq_pow : top = 2 ^ 207 * 2 ^ 207 - 1 := by decide
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 414) := by
  rw [top_eq_pow]; exact pow_add_testBit 207 207 j
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 414 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
lemma testBit_bnot_lt (x : Nat) {j : Nat} (hj : j < 414) :
    (bnot x).testBit j = !(x.testBit j) := by
  simp [bnot, Nat.testBit_xor, testBit_top, hj]
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 414 by omega]
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 414 by omega]
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
lemma valid1_xor {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ^^^ y) := fun j hj => by
  rw [Nat.testBit_xor, hx j hj, hy j hj]; rfl
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 207 * 2 ^ 207 := by
    have hp : 0 < 2 ^ 207 * 2 ^ 207 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
lemma valid_sep {d : Bool} {a : Sig} (ha : Valid a) : Valid1 (sep d a) := by
  cases d
  · exact valid1_and ha.1
  · exact valid1_xor ha.1 ha.2
lemma valid_unionSep {d : Bool} {v : List Sig} (hv : ∀ a ∈ v, Valid a) : Valid1 (unionSep d v) := by
  induction v with
  | nil => exact valid1_zero
  | cons a l ih =>
    exact valid1_or (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
lemma land_eq (x y : Nat) : Nat.land x y = x &&& y := rfl
lemma lor_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl
lemma lxor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl
lemma testBit_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := Nat.testBit_and x y i
lemma testBit_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := Nat.testBit_or x y i
lemma testBit_lxor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simp [bne]
abbrev Cov := Nat × Nat × Nat
def ValidCov (c : Cov) : Prop :=
  Valid1 c.1 ∧ Valid1 c.2.1 ∧ Valid1 c.2.2 ∧
  (∀ i, c.2.1.testBit i = true → c.1.testBit i = true) ∧
  (∀ i, c.2.2.testBit i = true → c.1.testBit i = true)
def covAdd (z : Nat) (c : Cov) : Cov :=
  (Nat.lor z c.1,
   Nat.land (Nat.xor z c.1) (Nat.lor z c.2.1),
   Nat.xor c.2.2 (Nat.land z (Nat.xor c.2.2 c.2.1)))
def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => covAdd (sep d a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.2.1 a)
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b)))
lemma validCov_zero : ValidCov (0, 0, 0) :=
  ⟨valid1_zero, valid1_zero, valid1_zero, fun _ h => by simp at h, fun _ h => by simp at h⟩
lemma validCov_add {z : Nat} {c : Cov} (hz : Valid1 z) (hc : ValidCov c) : ValidCov (covAdd z c) := by
  refine ⟨valid1_or hz hc.1, valid1_and (valid1_xor hz hc.1), valid1_xor hc.2.2.1 (valid1_and hz), ?_, ?_⟩
  · intro i h; have h1 := hc.2.2.2.1 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
  · intro i h; have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1 h2; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases c.2.2.testBit i <;> simp
lemma validCov_coverage (d : Bool) {v : List Sig} (hv : ∀ a ∈ v, Valid a) : ValidCov (coverage d v) := by
  induction v with
  | nil => exact validCov_zero
  | cons a l ih => exact validCov_add (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma cov_one {c : Cov} {a : Nat} (hc : ValidCov c) : takeOne (covAdd a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [takeOne, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1; cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
lemma cov_two {c : Cov} {a b : Nat} (hc : ValidCov c) :
    takeTwo (covAdd a (covAdd b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
  simp only [takeTwo, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1 h2; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_two_unique_disj {c : Cov} {a b : Nat} (hc : ValidCov c) :
    Nat.land (Nat.land (covAdd a (covAdd b c)).2.1 a) b = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [covAdd, testBit_land, testBit_lor, testBit_lxor, Nat.zero_testBit]
  revert h1; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> simp
lemma covAdd_swap {c : Cov} {a b : Nat} (hc : ValidCov c) :
    covAdd a (covAdd b c) = covAdd b (covAdd a c) := by
  have h1 := hc.2.2.2.1; have h2 := hc.2.2.2.2
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  · simp only [covAdd, testBit_lor]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · have h1i := h1 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> simp
  · have h1i := h1 i; have h2i := h2 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i h2i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_perm (d : Bool) {l r : List Sig} (hl : ∀ a ∈ l, Valid a) (h : l.Perm r) :
    coverage d l = coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    exact congrArg (covAdd (sep d a)) (ih (fun x hx => hl x (by simp [hx])))
  | swap a b t =>
    exact covAdd_swap (validCov_coverage d (fun x hx => hl x (by simp [hx])))
  | trans h1 _ ih1 ih2 =>
    exact (ih1 hl).trans (ih2 (fun x hx => hl x (h1.mem_iff.2 hx)))
lemma cov_union (d : Bool) (v : List Sig) : (coverage d v).1 = unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = sep d a ||| unionSep d v; rw [ih]
def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))
def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))
lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    rw [← List.mem_toFinset, he]; simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _, hv.filter _, ?_⟩
    intro a ha b hb eq; subst b
    simp [keepOf] at ha; simp [dropped] at hb; exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_filter, keepOf, dropped,
      decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, memv]
    by_cases h : x ∈ del <;> simp_all
lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd, hv.filter _, ?_⟩
    intro a ha b hb e; subst b; simp [dropped] at hb; exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset, List.mem_append, dropped, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) :
    v.length - 1 = (dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a) = unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_one (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2 = (dropped [a, b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b) = unionSep d (dropped [a, b] v) := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a, b] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_two (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest_disj (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    Nat.land (Nat.land (coverage d v).2.1 (sep d a)) (sep d b) = 0 := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  rw [cov_perm d hval p]
  exact cov_two_unique_disj (validCov_coverage d (fun x hx => hval x (List.mem_of_mem_filter hx)))
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
lemma sep_unary (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) (neg a)).testBit i = true) :
    (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, neg, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot (valid1_bnot ha.2), testBit_bnot ha.1, testBit_bnot ha.2,
      hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simp only [sep, neg, ht, ite_true, Nat.testBit_xor,
      testBit_bnot ha.1, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
lemma sep_binary (t d : Bool) {a b : Sig} (_ha : Valid a) (_hb : Valid b) (i : Nat) (hi : i < 414)
    (h : (sep t (bin d a b)).testBit i = true) :
    (sep t a).testBit i = true ∨ (sep t b).testBit i = true := by
  cases t <;> cases d <;>
    simp only [sep, bin, Bool.false_eq_true, ite_true, ite_false, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_or, testBit_bnot_lt _ hi] at h ⊢ <;>
    revert h <;>
    cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> simp
lemma sep_weaken (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) a).testBit i = true) : (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simpa [ht] using h
lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 414) :
    ∃ a ∈ S, (sep (decide (0 < t)) a).testBit i = true := by
  induction h with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [sep, target, Nat.testBit_and, testBit_top, testBit_bnot valid1_zero, hi]
  | unary ha _ tail ih =>
    obtain ⟨x, hx, h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ, decide_true]
    rcases hx with rfl | hU
    · exact ⟨_, Finset.mem_insert_self _ _, sep_unary _ ha.1 i hi h⟩
    · exact ⟨x, Finset.mem_insert_of_mem hU,
        sep_weaken _ (live_proper tail x (Finset.mem_insert_of_mem hU)).1 i hi h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨x, hx, h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ ha.1 hb.1 i hi h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU), h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).testBit i = true ↔ ∃ a ∈ v, (sep d a).testBit i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih =>
    simp only [unionSep, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset = S) :
    unionSep (decide (0 < t)) v = top := by
  have hv : ∀ a ∈ v, Valid a := fun a ha => (live_proper h a (he ▸ List.mem_toFinset.mpr ha)).1
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_top]
  by_cases hi : i < 414
  · simp only [hi, decide_true]
    obtain ⟨a, hm, ha⟩ := live_sep h i hi
    exact (mem_unionSep _ _ _).2 ⟨a, List.mem_toFinset.mp (he.symm ▸ hm), ha⟩
  · simp only [hi, decide_false]
    exact valid_unionSep hv i (by omega)
lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l ++ r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep, ih, Nat.or_assoc]
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' ≤ k + 1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
lemma extract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pull_gate ht (gate_rep hw g (legal g (by simp))) hs
    exact ⟨l, u, T, by simp; omega, hu, hT⟩
def bit (side : Bool) (i : Fin 414) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
lemma foldl_append_getD {α : Type} (f : List α → Gate → α) (gs : List Gate)
    (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (l ++ [f l g]).length := by simp; omega
    rw [ih (l ++ [f l g]) hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
def raw0 : Sig := (0xc4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f, 0x15115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07)
def raw1 : Sig := (0x10c000000000000003ffc000000000003ffffffe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279, 0x208e08e08e08e08e08e08e08e08e08e08e08fe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038)
def raw2 : Sig := (0x218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0, 0xc50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0)
def raw3 : Sig := (0x430000000003ffc000000000003fffffc00000084208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480, 0x1a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000)
def raw4 : Sig := (0x60000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802, 0x2a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000)
def raw5 : Sig := (0x2883ffc003ffc000000003ffc0000000000000010842084210822109042108882108917fffffc00802010fffffffffe000101004, 0x6c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000)
def raw6 : Sig := (0x1100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020, 0x3703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff0000000000000000000)
def raw7 : Sig := (0xa00000003ffc003ffc000000000000000000003ffffff0002080003ffffffffffffffa108211000041004208821085000002100, 0x3383383383383383383383383383383383383fffffe0000000003ffffffffffffff8000000000000000000000000000000000)
def raw8 : Sig := (0x3403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000, 0x3c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000)
def raw : List Sig := [raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]
def symKey1 : Nat := 0x32799cc653399bc965b2b9acee5e25108bc5a2b1488c66271887c3ab558afd7abb5cacd86b760abd5a9d4ca9d4aa350a6d569f54a5d2a3d1c91c8a43208ec963f248dc6afd7cc1e0b0380bee16ff84bddeae570bbddaeb74b8de6e778b7dba0d0485c2a130882c360f0c81c0a6d349dcea73389acf66f3c99cca552897cba5b2c94cc6573093c9acd64b5daad368b2db6cf6cb1d8b1588c7e3b1b8cc4e471790c3e1a8540a3d1a8b44a0d2687489fcf90a8342219046c351acda693a9cce87639168ac582b96cb2542914caae774391cae67192890492591c482211885b0d96a359aad76934d9ed0688c05c2f188b41a090582818080301d7cbd5fb0580bc5c2dd72bb5d2cd64b45b2d55cad57ac560aa54ab156803f1fd027d3319cd0653c9ecf07a3e1dcc26031190c65d2e178be70379c4dc4e27944a04c26bfa02ff803f54aa85329d489b4f2713e9d4d3d1eef57b3cd1c9047a35f2fc7d3edf0a15128d40964aa5d329848a492893773c9daf077bc5d2ec753ad148945a310e886fb89c0e16f108884521918821e1007c3a381d0ec723c1b85c32180d05996ce663359429150ac58280201406dd6db71b43f1f1007a1c0d8cc6a341b0c8241109854280e0784192c563b1990c46130c4c27128000202
def symKey2 : Nat := 0x32995cce6b3796c9e63399dcbe4a411f8ec6a43259247a471b8e48a592b94c9a5b31984aa5f27944bab95bacd5abb61b056abf57ac57ad167b2d8ad36db659ad763b25aae973b8dbaeb79bc5caef6fb85da71379acca733d9e4da77339a4ea291388c3a2b198c44a2f0f8845aa14fa6d2aa355aa53aa74ba654b017fbedeb0385c25fb077bbe60b198bc4e1b1b91c862b1f87c463a8943a0cfa8b49a450a8f3fa051a110782c0a130d8641a17038242972b85dae96eb459ad96ab24ba5932984aa71369e4fa75349248a51267b3d1e4f8773c188c26431980bc5d2f97076391c0e878371a8d066361904c24150a04430170c8682c0f070417ebe60b0178bd7fbfa03007ebe9f2fc7dbe14ca55429d48a250a8d40af572c560ad552b156a977bc1dcf278bb5eaf47bbd9e6ea74bb1d68b45231128e4823d1a87442110a864120cd66c369a4d4e57439dcce372124944b23920462410888fe80409f4fc6734194cce06fb89c2de6db75b8da219148444231047c3f200f43e1e10074381b3a1d4ec723995cb4582d964ac532a154a4d56cb59b0d76a341a6d268b3c5e30188b45c0a0682c1809038200c70389b8de4f289409c4d263198ec96431598cb6733594c26230c5629150b05026138940202000100a03
def posKey4 : Nat := 0x5dad9eeb158ab158f678bad3e9f4ca6528947a365b2d369bb5da7c3b1c4c85f2d96caa5567144a24d269349a4d269349a4d269349a3c1b35c6231160b190271389c4e271389c4e271389c4ed56806834150a84020100804020100804020100835196cb62b15747b3d9d56070382e166b74f278b45a2a1515a90480ec76981a8d4602b15a304c26130984c26130984c2613099369648a552a8e0683410080402010080402010080402112893a1d0743a3198ce6592c8a854502815cae532998032192b1489c05028140a05028140a05028140a38178bc6e140a0a4520c060a00402010080402010080402010082e0a0501c0e070381c0e070381c0e07038442209020100804020100804020100804000000000000000000000000000
def negKey4 : Nat := 0x5bac9e6ed56ba552f376ba5e69a76a55d29179bb5a8e967bcdda77391b8c05c6a1599e52653149cf376b5184b74d1dce456260df2437193519e2d650a18af376b5184b74d1dce4561b89724d467b282cc508bcddad4612dd3477391586e0ec93519eca653156eb23b9c95aa9372dd64b7592695a56549495aa946a686e95488c85a8d14225e6ed6a2dd34873b9c8ac3712e49349548a692a8d44825e6ed6a2dd34873b9c8ac37036491a893b9c8ee373b980e4722b1b8506e27180ac5c29180b8162b1489cf376b516e9a3b9c8ac4c1b80f2437190b46e32088b4502d048a1e6ed6a2dd3477391586e25006482c1104bcddad45ba68ee722b0dc1c06c9058220979bb5a8b74d1dce4561b818079279bb5a8b74d1dce4561b80c0192
def posKey0 : Nat := 0xf68011960702a38581a189545653038984c260ca389a35178984e080d1d0080526acc582a0d041582903bd120293ab406a742a8eca4cb1d89c542f1325136101889da0086981c4c8e56250aa31480bc0e05028146a8e13864a605268112874040984e38561c12810161500ef415950e6d00c9d0629e1834d3c4d3814c0a1a4d840aa4d68134aa10029c4a85369b2ce01a080984c260c9c408354a098102729a7c9a05020f0a8902981c52ac081d854ac7b3406a9f659ed9c553d8212094130bcf80769821a027188404c71148bd96d3152502005028146a71040643405021345e9f1389810b6148ac5e072a0b02076380b1eed00ca7da63a758c47404158680a533e01d9604
def negKey0 : Nat := 0xe076480d92c901984c2193285acf292a522b23bb3ca4b2391c994a91b9dc0603652c9e6774d0395237033cd1a2d3933c647229268a4f31bb08503216ba534cf67b3c1d920364b240661308b8e92933c5a280b0dceecf168dce472748a1647743a1dd237799dd340e142c80cf346948e4cf2e1c85a9a16bcd64c254970a4ca4d33d9ecf076498592c93080c0648949d2cf650a064374d33d943779bcca42859268984c290dce49a3b83850b2611c8dce979b3d22f3651dd9472590195291748b4eecf67b3c1d926164b24c2030182c2d6533dd2a92e2c934cf74ac9e6f316aa46e9a128945ab239268ee0e548dd847237329e6cf0b3cdd277749c86e061405994523bb3d9ecf
def rawPermCodes : Fin 12 → Nat := ![0x876543210, 0x267143850, 0x374268501, 0x364872105, 0x547068321, 0x146072385, 0x846375012, 0x247361058, 0x64175832, 0x74561238, 0x567840123, 0x176240583]
def perm1 : Fin 9 → Nat := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
def perm2 : Fin 9 → Nat := ![1, 0, 5, 8, 6, 2, 4, 7, 3]
def gOfV : Fin 9 → Fin 12 := ![0, 2, 6, 10, 0, 4, 2, 4, 8]
def recipeFuel : Nat := 12
def recipeBuckets : Nat := 128
def recipeWidth : Nat := 8
def recipeMask : Nat := 255
def recipeEntryBits : Nat := 48
def recipeEntryMask : Nat := 0xffffffffffff
def recipeShift : Nat := 0x1090409000301000500000002030803000000000101000201000c150a060404010000000000020000000300000d00010000000000030000010000000000030000000200040000020200000001010505000002000005050201010000000001000b0000010104000000010200000000000000000000000102000000010802
def recipeData : Nat := 0xc2900000bc36c29000000000000000000ac6c21000000000000000000000000000c1bc19c640000cac6c24900000000ac69000000cac2970000000c4c630000c1cac6230000000000a300000bc19c64000000cac2360000000b1c64000000cac633000000000c230000cac2c634000000000c3900000000ac16c3bcac297c29000000cac3640000000c9c160000000c6c2900000bc63c140000000c1c36000000cac2610000000c4c2300bcac297c2900000000ac13000000000001cbcac297c299000000cac16900000bc29c1400000cc13c6400000cc36c2400000000000000000000ac19000000cac64200000bc14c2600000000000000000000000200000000000000000000ac630000000c2c6300000c4c1c9600000bc94c160000000000000000000000000000000000000000000c2c4100cac9c14c9400000000000000000000000000000000000000000000000000000000000000000cc92c64000000000000c1bcac297c2900cac2c41c24000000000c3400000c9c2c61000000cac264000000cac16100000000ac120000000000040000000000000000000000000000000000000000c1cac9270000000c4c6900cac2c63c26000000bac6340000000000070000000c9c1400000000000600000cc19c2400000000000000000000000000000000000900000000000000000000000000000000000000cac4c63c460000c1cac4150000c3cac638cbcac927c925000000000000000000cac6380000cac2c631cbcac297c2980000c3cac92700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ac940000c9cac145000000cac14500000000000000000000000000000000ac26000000000000000000000000000000000000000000cac36600000bc16c260000000c6c410000cac2c6380000c3cac1450000c1cac269000000000c1400000000ac2400000bc14c64000000000c640000000000050000000c3c140000cac2c63900000000ac6400000000ac14000000000000000000000000000000000000000000ac6c41000000000c240000000c9c360000000000000000000000000000000000000000000000000000c9cac461000000000c2600cac2c46c2600cac2c63c63000000000000000000000c940000000000000000000000000000000c1c390000000000000000000000000000c9cac4660000000000000000000000000000c4cac297000000000000000000000000000c7bc19c64000000000000000000000000000000000000c4bcac927c92000000cac46100000cc41c3900cac4c63c630000c3cac4610000000000a90000000000a6c6bcac927c92000c3bc19c64000000000000000000000000000000cac623000000000000000000000000000000000000000000000000000000000000000000000c120000000000a400000000ac340000000000080000000c3c920000cac2c64300000c3c6c210000c1cac622000000000000cbcac927c9220000c2cac4150000000c3c1200cac3c14c34000000000000000000000000000000cac1630000000b1c2600000bc14c240000000c9c34000000cac644000000cac14400000cc26c39000000cac639000000000c63000000cac6430000000000000000000000000000000000a2000000000000000000000c19000000cac466000000000000000000000000000000000c16000000000c130000000000000000000000000000000000000000000000a100000cc14c2600000000000000000bc26c3900000000000000000000000000cac2c63c2300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000bc41c39000000000000000000000000000000000000000000000c6900000000000300bcac145c140000000c1c92000000cac3620000000c6c2100000000000000000bc12c9400000000000000000000000000000000000000000000000000000000ac290000000c2c64000000000000000000cac64900000000000000000000000000000bc19c24000000000000000000cac631000000000000000000ac2c640000000000000000000c4c29000000bac641
def wireCount : Nat := 161
def wireEntryBits : Nat := 10
def wireEntryMask : Nat := 1023
def wireTable0 : Nat := 0x3de7fffffffffffc003fffffffffffc000003fffbdefbc077c0077ffbef7bbddf7bdbb03fd83c1fdd003f07bfef41de1bf7b802f1bf000000000ffffff000ffffffffffffffffff39cff9fe73ffe7f937fff91dffff9fbf2fff1faffffff3e39ffff8cfbffffff7d77c003ffc003ffffffffc003ffffffffffffffef7bdf7bdef7ddef6fbdef777def76e8000003ff7fdfef0000000001fffefeffb2ff000000fff000ffffffffffffffffffffffff00000000000000007def7bffdf7bffef7bef77bbddf775efbbef7bdffef7bffffef3ffffffffffffffc003fffffffffffc0000001f07dfe83fef03dfdf7bdc0f03de1df7bef77bbeefbbae81e07fa0fa183dfd86fceffffffffffffffffff000000fffffffff000f7bc07fdee03fe07f81f07fbbe07f07ef7deef703c0f0fdf77def7b775e0707c3bcfffffffffc003fffffffffffc000003ffffff7bdf7bdef7deefbb7003ffbb0001ffef606ff7600f77fdf7a0037ff768003b7f000000000000000000000000000000000000000f87ff807f1fc3ff803e180103ff8000000600007c620801207e1040021ff81000480000000003ffc000003ffc000000000000000a52fe4294ff117e40c630000a3181014bf9440188a03028a7ffca12004311004800fff0000000000000000000000000000000004a53fa1295fc89fa03e8800009fa0014a7f48007c220829257ffa420001f81002887ffc003ffc000000003ffc000000000003ffd284a28425092252904a128982528b37fffffc00902414fffffffffe02052120d020000000000000000000fff0000000000000006018a000c0280c5003e140303ff8240318633007c4a0407f8fe11fc821ff8501173c003ffc003ffffffffc000003fffffffffffff6f837b7e81dfc36e0dc37f6fc37e2884108bdc1f07c717e1f805f1df7c3c3f9feefffffffffffffffffffff000fffffffff000f7bc87fdee23fe47f91f47fbbe47f47fffffff723c8f4fffffffffff75e4747d1738003ffc003ffffffffc000003ffffffffc002d6b017b5a80dd816e05c1766d817408000003dc0f03c30000000001dd781c1f0d0cffffff000fff000000000000ffffff000000ffffffffffffffffa3ff84113fff8014a7f48a67fe2a8a9257ffa42225fff120034c000000000003fffffc003ffc000003fffffc00000000000000007000e73300016e80000016600554d0000000001768002b7b18e000000000ffffff000000000fffffffff000318c31fe62ffe61133ff1119bfff913f27ff0fa7ffff03e317fff887b5fffff436dffffffc003fffffc003fffffc003ffffffffffffffffffffffffe5fcbf4338ff27efe32fe7f3fafffefc731cff3be6cff7fdfbbffff000fffffffff000ffffffffffffffffff7bdffbfef7ffeffb77fffb3fffffbfffffffffaffffff3ffffffffffbffffff7c01c000000000000000000000000003ffffffffc6018a030c0318c600f8820300fe2621802980c1f20cc4306018cc30c60fe46d9003000000000000000000000000000000ffffff18c7f8fe31ffe3f80220880c038818920012090442199241806090c118388096753ffffffc003ffc003ffc000003fffffffffffffffffffffffffffeaffe33f4ffffe25adfdaaddff8ee7b7f5ffedf8df7ffc6f9143000000000fff000fff000000000000fffffff93e290df20c7f190a3108fc3f8c7882144221146411145f87f017c179f8c09e4084000000000000000003ffc000000000003ffca02a20014090152004a52050fd283214bf9440091241428a7ffca120a7d2120df73ffffffffffff000fffffffff000000ffffffffffffffffffffffcff9fefe7ffe7fdffffff9dfe7f9fffffffffff9fbffcf9ffcc7fffffffffffc000003fffffc000000003fffffffffffffffffff1fe3f899a7f8bf7fffffe33f8fe3efffffffffe22c7f3e0f831fff000000000000000ffffff000000000fff4a53fa1295fc89fa07e0f80441f80f918c31908fc3f0f230cc318c688a1f8f83e087ffc000000000000003ffc000000000003fffe8fa2857d092fd28048120108520324630c64009024148c330c631a02452120df6fffffffffffff000ffffff000ffffffffffffffffffffffffffffebffceff3ffffcdffffffb77febbdffffffffffb7dfff5bf75fffffffc003ffc003ffffffffffffffffffffffffffffffffffffebffff3f5fffffe5effdeefffffeffbff7ffeffaffffffefffb0fffffffffffffff000ffffff000000000000ffffffffffffffffd610f702e0840779cc19dccc23cceb306c10cc3c83084e418f38000003fffffffffffc000003ffffffffc0008420842108211045effc0feeffffc1b9dfb99cdff09c173cdffdce5dd7ffc5f038c000000fffffffff000000000ffffff000000210821084208441173ff0313bfff806c67ec4627fc26018237ff601625fff1603e03ffffffffffffffc000000000000000000003ffffffffffffffff48421c0a821001e31063311088322c41904310d004210100fbcfffffffffffffff000ffffffffffff00000027c9f7fa4ffbc4f7f7fff713ffff877deffddeefffeeeba27fffe83ea7ffff61bdfffffffffffffc003fffffffffffffffffffffffffffffffffffffbffffbfdffffff7fffffefffffefffffffffffeffffffeff3cf000000ffffffffffff000000fffffffffffff93e290df20c7f197bff0bffbffff8ee77ee6737fc3715dfb7ff77d77dfff1fe4b0c000003ffc003fffffc000000000003ffffffe0f82017c010fc2160842ffafc21e3a9412994411054557e9f815f55e7c20379921fff000000fff000000fff000000000000ffffb3eab1df62cff5b03f0480421fc0c918c319007e0b05230cc318c68091fc58375cffffffc003ffc003ffffffffc000003fffffffffffffffffffffe3fc7f3f1fff1fe4e71cee77f9fe7f9ff3fc67fa7efff3e7f963fff000000fff000ffffff000000000fffffffb3eab1df62cff5b0bf148fc3ffc7c939c73b117e4b1567fcff19fe979ffc59f4ac4000003ffc003ffc003fffffc000000003ffc210fe00847f007e15f83ec1b07e03fa520a5523f0fd3c482a0852172287e3f0f900fff000000fff0000000000000000000000006318a318c628cc53023100303f8c20129452a0046400025fc7f097e021f8c0000404000000003ffc000000000000000000003ffca52fe4294ff117e408c62050fe302200110000119842400a1fc00100a7e30209131000000000fff000000ffffff000000000fff294bf90a53fc45f907f0f80461fc0f810c21108fe3f0f0208c3108488b1fcf83ff0bfffffffffffffffffc000000000003ffc003ffffffffffffffff68421faa8211c1eb506bb55088363d7590435ed544210170beefff000fffffffffffffff000fffffffff0006318a318c628cc537bff43fbbffff47ffffff737fca747ffffffffff75fff57d3cf7fffffffffffc000003fffffffffffc003fffffffffffffffffff9ffff8ddfffebf7fffffebbfffebefffffffffeabffffe8f6df000ffffff000ffffff000fffffffffffffff9ce75ce739d733acfc0fbfffde03fbee73ce6ff81f5fbdcf33ce7397fee03afee4b3ffc000003ffc000003ffc003fffffc0000018c628c6318a3314c8ffd0044fffe1056bfd6489ff2890acb7ffeb1a897ffd484ba0fff000fffffffff000fff000000000000000ffffffd8c6aacc53fffffffffffffff9ce39d407e1a44338ee39ce7c011fcd412483ffc000003ffc000003ffc0000000000000018c628c6318a3314c0fc1000087f0104630c6401f828108c330c631a0047f1404101000000000fff000000000000000000000ffff93e290df20c7f1903f0080421fc088004200007e030101084310440091fc1827673fffffc003fffffc000003ffffffffc000003fffffffffffffffedb5ad40782d60cc210423bb6edbaa8411042109a1c2ded82dd3ffffff000fffffffff000fff000000ffffffffffffffffffffff9e10bdcce0845bb084108ddc235dbe1044108425db084adef70bfffffc003ffffffffc000000000003ffc003fffffffffffffffe68421722821140c2104235508836384110421095442101705df000fff000fffffffff000ffffffffffffffffdff7deffbdf7fbdbef7bdfdffbdfba210422ffdff7fbc5f87e017c7fffbfbfeedffffc003fffffc003fffffffffffffffffffffedffec7fdff3ffedbfffebfdffffff7fffffceffffcfdfffffffffeffffffeff12d000000000fff000000fff000ffffff000fff290aa908522c455923ff48153fff8c852fe51227fcb250a29fff284a2dfff5a356f4003ffc003fffffc003fffffffffffc003ffcb72ff7a96ffd17f6dffff457fffe3e94bf947bbffffbe28a7ffca13abfffff8f4f3000fff000000ffffffffffff000000fffffffcfffce7f9ff3ffc9fe1fdfcfff87fa318633ddfc7fdfc7f8fe11fcdfbff8fdffef7ffffffffffffffc003fffffffffffc003ffd3f4fffea7fff27ffdffbfc9f27febffffffffbbfeffbeffffffffffa387fff8f5bd000fff000ffffff000ffffffffffff000fff0dc3fdea1bff41fdb7f6fd05c1fd8fa108211eeffbfef8208821084e8e1fffe3d2c4003ffc000003ffc003fffffc000000003ffc330ff38867fc07f25f83f41307e03e842084733f0ff3e08220842132287e3f0ffbcfffffffffffffff000ffffffffffff00000067d9f7facffbccf7f7fff733ffffa77ffffffeefffeeebfffffffffea7ffff61bef3ffffffffffffffc003fffffffffffc0000011f47dfea3fef23dfdf7bdc8f23de9dfffffffbbeefbbaffffffffffa183dfd864d3000fff000000ffffff000fff000000fffffffcff5ce7f9d73fac9c21bdfcff087ba210422dd8475dbc5f87e017c5fbf08aded30c003ffc000003fffffc000000000003fffffff2f83397e01cfc32608437f2fc21e2884108b5411074717e1f805f15e7c20379ef3fffffffff000ffffffffffff000000ffffffdef7fef7bdffbbfedfe0ffeec1f87ffbd83bfddfc3fdff7de821dffdda1f8fdfff7bfffffffffffffffffc003fffffffffffc003fff19ffffc6ff8dffffc9fffffffc9fffffbbffff1bcbfffffffdedfffffcdf2fceffffffffffffffffff000000fffffffff000f7bc27fdee0bfe17fbff07fbbffff07ef7feef77fc2f0fdf77fff7b775fff17c177c003ffc003ffffffffc003ffffffffffffffef7bdf7bdef7ddef6fffef777ffff6e909f903ffffdfef2085ffc801fffffeffb5ce000fff000fffffffff000000fffffffff000b5ac25ed6a0b7615bbff05d9bfffd02427e40f77fc2f0c8217ff200775fff17c3fbbffffffffffffffffffffc003ffffffffc003def29ff7b8aff95feffd1feeffffd1fffffffddff2bd3ffffffffffdd7ffd5f4ef3fffffffff000ffffffffffff000000ffffffdef7fef7bdffbbfedfe8ffeec9fa7ffffffffddfc3fdfffffffffffdda1f8fdffbebffffffffc003ffffffffffffffc003ffc003ffd31bfffccee99bf6319fff318dd9ffffffffec4335bffffffffffff91899764da000fff000000ffffff000ffffff000fff000ffe444ffff133224fc8425ffc421523ff9000ff9104d2ffff8840007fe42225cbb8bffffffffc003ffffffffc000000003ffc0035ad21bd6b08ee91b64211faa2109d1fffffff54802353ffffffffff540101174fceffffffffffffffffff000000fffffffff000f7bc17ffeefffe07f85f17fbbe17f17ff7dfeff0bfff0fff77deffb7f5e17ffc3adbffffffffc003ffc003fffffc003fffffc0005b175bf8b7ff8b9b510bdc2b08425dff227f7f222fffaf85a10be2fe48847fd6006000000000000000000000000000ffffff0001004000c200c6200004200080210900600860300883300c100423083102111b43ac7ffffffffc003ffc003fffffc000000003ffc3b0ffbc877fe07fb5f83fc1b07e03fe720e7733f0ff3ec83a08721f2287e3f0f001000000000000000000000000000000000fff08022800100c011803e0080401f8088000200007c030100080210040081f818274c7fffffc003ffc000003fffffc000000003ffffffffffffffffffe1fc3f01187f03e4630c6633f8fe3e8c330c631a22c7f3e0fd3dffffff000fff000000ffffffffffff000fffffffffffffffffffa7fffc157fff8f95aff59aeffffafab2dfffac6aafffffa3fc83fffffffffffc000003ffc000000000000003ffffffffffffffff0c631888a318917fffffe1188a232fffffffffe004311004f2cffffffffffff000000fff000ffffff000000ffffffffffffffffe3ffc6333fffa45ffffffa67feaacbfffffffffa25fff52113cc003ffc000003fffffffffffc000003fffffe739ff39ce7fccff27f83f73307e17e842084777f0ff7f08220842137687e3f7f5ff000fff000fffffffffffffffffffffffffffbdeffdef7bff77fdbffffdddffffdfa52fe51ffffffffca29fff284fffffffffc4b0000000003ffc000003ffc003fffffc0000008422842108a111448ffd0044fffe1014bf94489ff289028a7ffca12897ffd484b3dfff000ffffff000000ffffffffffff000fff6b5bfb1ad7fccdfb67fffa377fffafdffffff2affff2f3fffffffffaafffffa3fbcfffffffffc003fffffffffffc000003ffffff7bdf7bdef7deefbb7423ffbb2109fffffffff7680f77fffffffffff768103b7f4d3000fff000000ffffff000fff000000ffffff9ce75ce739d733ac9c00bdccc0005ba000000dd8035dbc0000000005da000adec5fc000000003ffc003fffffffffffffffffffffe5ffe43fcff1ffe4bfffe3f5fffffe1cff9cceffffcfd3fe7ffcff2ffffffeffeb0fffffffff000fff000ffffff00000000000046d1d6f28df388e6d508f722c842277ffffffcca03ccebfffffffffc82040e41977c003ffc003ffffffffc003ffffffffffffffff7fdf7bfef7dfef6fffef7f7ffffee98df98bffffdfef37e5ffcdf1fffffeffb490000fff000000fff000000fff00000000000004c154e209d300a49400b500c000032000000cc8034ca8000000000482000a40977c003ffc003ffffffffc003ffffffffffffffef7bdf7fdefffdef6fbdef777def76efc027c3ff7fffeff84010be21fffeffffb55d000fff000fff000fff000fffffffff000fffad6b6d095b0855bdafffacd57fffca8427e4027ffc22bc8217ff20026ffff12afdf7fffffffffffc003ffffffffffffffc003fffbdefbc677ca377ffbfffbbddffffbb7fffffc9fff28bffffffffffe9bfffd4afa24fff000fff000000000fff000000fff000000421082188428c842414a42220a52a45ffffff20288a243fffffffffa002515213fe7ffffffffffffffffffffffffffc000003fffffffff477e8a77ffffffffffffffffffffffd1fdd613fffffffffff1bf7bb12ff79ffffffffffff000ffffffffffff000000fffef7bef11df209dffefbdeef77def6edffffff07f7480fffffffffff86fdee40bca00000003ffc003ffc0000000000000000000014a524b000208000145294caa294ad5a1082110000410042088210850000021007d9000fffffffffffffff000ffffff000000fffffffffc15b8215bdffffffffffffffe84208447d7504bd08220842146fdae84ae09bffc000000000000003ffc000003fffffc000000000fa91f7a908000000000000005ef7deee0a2bed0bdf77def7ae40945ed4559000fff000fff000fff000ffffff000000fffad6b6d015b0015bdaeb5acd575ad4a800000007d7400bc00000000006fdae00ac2dc000000000003ffc003fffffc003ffffffffc631fe3f8c7ff8fe05f8be4330fe27efc22fc7e3f2fffcf86218fe33e68fe7fdf59e000fff000ffffff000000ffffffffffff00015c575fe2bffe2b5b6d6b509c2b5933f009f0fedbbffabe10042f887962b7ff4bf9fffffffffffffffffffffc000003fffffffffffffffffffffffff6def7ffaff7bf7ffffffff5bbfff7fffffffffffe7f77ffdfa6fffffffffffffff000fff000000ffffff000ffffffffffffffffd35ad72aaad6b57fffffffc6abffcbffffffffff912d5ff53d8ffffffffffffc003fffffc000000003ffffffffffffffffffffff2ce73bf8ff39f37fffffe5599a677fffffffffe5e7f3127ddc7ffffff000fffffffff000000000fffffffffffffffffffffffff9a739dfcbf9cf9bf94dfafd4efff9fffc7f2ffe7f9f9dffe41cc000000000000003ffffffffc000003ffffffe1ffe01fc7f0ffe03f87e3f1ffe1fe0c618cc67f1fc7d1fe3f847f27effe3e7f14f000000000fff000fff000000fffffffffffff93e290df20c7f192bff08fd3ffff88637e62337fc3314df97ff37c37dfff1be556c003ffc003ffc003ffc003fffffc003fffffff5fdb417ec10fef6bad6b3f5feb5ea08410885f5d046f17e1f805f05ffeb827baf7fff000fff000ffffffffffff000ffffffffffafffafff5fffffa5febfbfefffaffffffffff9fcffff7fffffffffffbff9fffeadfffc003ffc003ffc003fffffc003ffffffffd6b5febfad7ffafe95fabecbb2feafffffffffe3f2fffcffffffffffe68fe7fdfa73fff000fff000000fffffffff000000fffffffa7ffa17f5fcbffa4fe9fafe7ffa7fdffffff19fc7f1f7fffffffff9fbff8f9fc3dc000000000003fffffffffffc003fffffffffe3ffe3ffc7ffffe07f8fe7f3ffe3fefc63fcfe7f3fffdffe3f8fff3feffe7fffbeffff000fffffffffffffff000fffffffffffffbbebbfff6ffff5b7bff5bffbffffdffffffffb7ffff57fffffffffffdffffff6ebbffc003ffffffffc003ffc003ffffffffc001ce72cffb9bffb94dcffd4ceefffed5fffffffe9ffffd0ffffffffffed7ffffd4b6ffff000ffffff000ffffff000fffffffffffffb3eab1df62cff5b6bff4aff3ffffcdffffff337fcb357fffffffffb7dfff5bf473c000000003ffffffffc000003ffffffffffffe6f8e7ffcbfffc64effc67f6ffffe6fcdffcbedffffc5ffe5fffff1ff7fffff9ae7fff000fff000fffffffff000000ffffffffffabe9afff4ffff4a596b5bfebf5afdffffffff92cfff57fffffffffff9f59fff7ce3fffffffffffc000003ffffffffc0000000011d479c423c8223df9e73988d239c997fffffc1bcc203afffffffffe018399006fbefffffffffffffff000fffffffffffffff00057d5f7feafffeaf7f7def72bcaf7b77fffffffefbbffebffffffffff962f7ff5bdeffffffffffffc003fffffffffffc003fffffffdffbc57fc92ffffbef7bbfdffbdfb7fffffc5fdd247ffffffffffe5fffb927f5df000fff000fffffffff000ffffffffffffffffdff7dfffbffffbdbef7bdfdffbdfbbf10df2ffdffffbfff87e2ffc7fffbfffede60003fffffffffffc000003fffffc000000003ffffff002e0802d7ffffffffffffffa1082111b4c412a420882108501829a1020c7000000000000ffffff000000000ffffffffff8be18fff0ffff08186319fcbf18f9bf10df2f90cfff17ff87e2ffc7f9f19ffe5460003ffc003ffc000000003fffffc000000000150594002c0002d69a52900502940800000001b4c002a0000000000018298002aa6fff000fff000fff000fff000000ffffff000529492fea4ffea42514a532a8a52b57fffffff828bff43ffffffffff90251ff5361bfffffc003fffffc000000000003fffffc003fffffffffffffffe494a54228a5244fe127e3f12affe2fc5114bf29e44a57fd0500000fff000fff000000000000000000000000ad6b6d015b0015bd821084002084000000000044200088000000000001084000298fffc003ffc000003fffffc000000003ffffffe8fa2857d092fd2924a52bf8fd29f37fffffc44912455fffffffffe5e7d2127dd43ffffff000fff000fff000000000000ffffffffffffffffffffff8a318cfc3f8c78929452a95466199e5fc7f097e179f8c09e5400003ffc003ffc0000000000000000000000001705d7a82f6d02d608421000021000000000211088222000000000000021000011c000000000fff000000000fffffffff0000002948610a5318443127ff20157fff82052fe402affc6220a29fff2002affff3208a60000003ffc003ffc000003fffffc000000003ffffff294e480083ffffffffffffffb5ac211aa4451086aaea31085ab908a902a38fff000fff000000000fffffffff0000000006b50c21ad7308862658c62374c63265ffffff2ab10c063fffffffffaae462601bb6bffffffffc003fffffc003fffffc003ffc003ffd11bfffc4ee89bf2109fff1085c9ffe46bbfe44134bfffe2135edff9088972443000fff000000000fff000000000000fffffffc3f0c25f8453f8c8a318cfc3f0878929452a95466199c5f87e017c179f0809e44f4000000003ffc000003fffffffffffc003ffca52fe4294ff117e49fffe055fffe3e14bf944abfffcbc28a7ffca12abffffe8fa31fff000fff000000000ffffff000000000fff4a53fa1295fc89fa47e8fa2649fa2fdffffff08fc3f0f3fffffffff88a1f8f83ecb3ffc003fffffc000003ffc003fffffc0000018c628c6318a3314d8ffd08ccfffe917fffffc89ff2890fffffffffe897ffd484458000fff000000000fff000ffffff000000000ffe1447fff5110a4feb5acffd421421ffd52affd7659bffff9840107fec22208bbf3ffffffffc003fffffffffffffffffc00000318c618c63186631bffffff8f61cf9dfffffffffffffffffffffffffb1a1cfda6e60fffffffff000000ffffff000000000000000c63186318c6198c6cb39cee21842645ffffff9566699dffffffffff8408404091bf0003fffffc003fffffffffffffffffc0000021084108421044213ffffff0f41cf1dfffffffffffffff690e43da47b1a1cfda6440000fff000000000fff00000000000000000084210421084110848a318cc0100040129452a95466199c0401000100408000083403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000280000000fff000fff000000000000000000000ffffffc000820000ffffffffffffffe8420844000104010822084214000008401100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020a20fff000fff000000000fff0000000000000004210821084208842410842220842245ffffff002008043fffffffff8000404010060000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff908880210c000000000fff000000000000ffffff000000210821084208441123ff00113fff800427e40227fc22008217ff200225fff1200218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0043000000000000000fff000000000000fffffff83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e40c4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f
def wireTable1 : Nat := 0x3fff3af3af3af3af3af3af3af3af3af3af3af3affffffe07fc007fffffffffffffffff83ff83c1fff003f07ffffc1fe1ffffc03f00077d77d77d77d77d77d77d77d77d77d77d77d0001f87e00ffe0f803fff8003fff879f07ff0f87fffff3e007fff80781fffff1fffff93f93f93f93f93f93f93f93f93f93f93f93ffffffffffffffffffffffffffffff8000003ffffffff0000000001ffffffffffff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffdf71f71f71f71f71f71f71f71f71f71f71f701f07fff83fff83fffffffe0f03fe1fffffffffffffffff81e07fe0fe183fffc7fffabbabbabbabbabbabbabbabbabbabbabbabbfffe07ffff03ff07fc1f07ffff07f87ffffffff83c0f0ffffffffffffff0707e3fffe5be5be5be5be5be5be5be5be5be5be5be5bfffffffffffffffff003ffff0001ffffe07fffe00fffffffe003fffff8003fff000d61d61d61d61d61d61d61d61d61d61d61d61f83ff801f0fc1ff803e000003ff8000000000007c000000007e0000001ff800000014254254254254254254254254254254254240007e00003f003e000000000000000001f800000000000001ffc0000000000000005495495495495495495495495495495495490001f80000fc00f803e0000000f8000007e00007c000000007ff0000000f8000000006c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000000063063063063063063063063063063063063000000000000000003e000003ff8000000000007c000001f87e007c001ff80003ffea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ffff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c307e1f801f1fffc1c1f8fffabbabbabbabbabbabbabbabbabbabbabbabbfffe07ffff03ff07fc1f07ffff07f87ffffffff83c0f0ffffffffffffff0707e3ffea82a82a82a82a82a82a82a82a82a82a82a83fff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c30000000001fffc1c1f8000f69f69f69f69f69f69f69f69f69f69f69f69ffffffffffffffff03ff00003fff800007e00007fc00000007ff000001fff0003ffc2102102102102102102102102102102102100000000000000003f003ffff0001ff8000003fe00ffff0000000001ff8003fff00037d37d37d37d37d37d37d37d37d37d37d37d0000007e00ffe00003ff00003fff801f07ff0f87ffff03e007fff80781fffff00003d53d53d53d53d53d53d53d53d53d53d53d53fffffffffffffffc0f83e00003e01e7c007c3e1f0fffcf800003e01e003e3fc700077f77f77f77f77f77f77f77f77f77f77f77f0001f87e00ffe0f803fff8003fff879fffffff87fffff3ffffffffff81fffff1c00010010010010010010010010010010010010000000000000000000f80000003e000000000001f0000000000000000003e00000007007007007007007007007007007007007000001f87e00ffe0f80000000000000000000000000000000000000000000000000003dafdafdafdafdafdafdafdafdafdafdafdaffffffffffffffffc0ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00000a40a40a40a40a40a40a40a40a40a40a40a4000000000000000000000000fc0000001f800000000000001ffc000007c00000000f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7fffffffffffffffff03e0f87c3ff87f9ffffff007c3f0f3fffffffff879ff8f8fc003d7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7ffffffffffffffffc0f83e00003e01e7fffffc01f0fc3cfffffffffe0003e3e070005445445445445445445445445445445445440001f80000fc00f803e0f80000f8078000000007c3f0f00000000000000f8f81c002002002002002002002002002002002002003e0f80007c0007c00000000000000000000000000000000000000000000000000000f7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bffffffffffffffff03ff007c3ffff81ffffff007fc0003fffffffff879fff00e0003dbfdbfdbfdbfdbfdbfdbfdbfdbfdbfdbfdbffffffffffffffffc0fffe1f0fffffe001f80001fffc3c07e1ffc1f01e7fffe3fffff94f94f94f94f94f94f94f94f94f94f94f94fffffffffffffffffc00ff83c00007fff81ffff803ffffe07800f83f86000ff1fffc3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec0000000000000003fffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8fff0f90f90f90f90f90f90f90f90f90f90f90f90000000000000000ffff0783ffff807ffffffffffc0f0fe07ffff83f87fff0703fffe43e43e43e43e43e43e43e43e43e43e43e43fffffffffffffffff0001e0f000001ffe07fffe0003c3f81e003e0fe180001c0fff7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd07c1fffe0fffe0ffffffff83ffff87ffffffffffffffffe07ffff83f87fffff1c003dffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffc0fffe1f0fffffe7fffffc01fffc3cfffffffffe1e7fffe3ffff8fb8fb8fb8fb8fb8fb8fb8fb8fb8fb8fb8fbf83e0001f0001f00ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e3ffe2ce2ce2ce2ce2ce2ce2ce2ce2ce2ce2ce2cfe0f80007c0007c03f0001ffffc01e1ffe07fffe0003c3fffff83ffffffc001f8000840840840840840840840840840840840840f83e0001f0001f0003e0000000f8000000000007c000000000000000000f80000003d9fd9fd9fd9fd9fd9fd9fd9fd9fd9fd9fd9ffffffffffffffffc0f83e1f0ffe1fe000000001f0fc3c07e1f801f01e7fe3e3f000863863863863863863863863863863863863f83e0001f0001f0003e0007c3ff8780000000007c000001f87e007c079ff800e3ffd7517517517517517517517517517517517500007e00003f003e3ff83fe0f03e01fffe07fffff0fffff81e003e0fe183e3fc70000230230230230230230230230230230230230000000000000000000000003f000000000000000000001f87e007c001f0000000014854854854854854854854854854854854840007e00003f003e000000000fc00000000000000000000001f80000007c000000005445445445445445445445445445445445440001f80000fc00f803e0f80000f8078000000007c3f0f00000000000000f8f81ffffe4be4be4be4be4be4be4be4be4be4be4be4bfffffffffffffffff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8fff0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0000000000000000ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e0003dffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffc0fffe000fffe1e7fffffc01fffc3cfffffffffe007fffe07ffffbffbffbffbffbffbffbffbffbffbffbffbffffffffffffffffffc1fffffff07fffffffffff83ffffffffffffffffff07fffc0001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff8000000000ffffffffffffffe000000007c000000000000000000f8000000010010010010010010010010010010010010000000000000000000f80000003e000000000001f0000000000000000003e0000000840840840840840840840840840840840840f83e0001f0001f0003e0000000f8000000000007c000000000000000000f80003ffff13f13f13f13f13f13f13f13f13f13f13f13fffffffffffffffffffffe0f03fe1f8000003ffffffff0000000001e183fffc7ffff84f84f84f84f84f84f84f84f84f84f84f84fffffffffffffffffc00ffffc0007fe000000ff803fffc0000000007fe000fffffffe03e03e03e03e03e03e03e03e03e03e03e03fffffffffffffffff0001fff0001e18000003fe0003c30000000001ff80001f8ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffffffffffffffffe000000ffffffffc1f87e007c7ffffffffc0035ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ffe0ffe007c3f07fe00fffe1f0fffffe7fffffc01fffc3cfffffffffe1e7fffe3f000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0003ffdfb5fb5fb5fb5fb5fb5fb5fb5fb5fb5fb5fb41f07fff83fff83fffffffe0ffffe1f801f803ffffffff0001ffc001e1fffffc7ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffffe0fffffff87fe000000fffc3fffc1f87e007c7ffff8ffffffdf7df7df7df7df7df7df7df7df7df7df7df7c1f07fff83fff83fffffffe0f03fe1ffffffffffffffffffffffffffe183fffc7fff7c47c47c47c47c47c47c47c47c47c47c47c407c1fffe0fffe0ffffffff83c0ff87e000000ffffffffc0000000007860ffff1fffdf11f11f11f11f11f11f11f11f11f11f11f101f07fff83fff83ffff83fe0f03e01f8000003fff0ffff0000000001e183e3fc7fff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff07c1fffe0fffe0ffffffff83ffff87ffffffffffffffffffffffffff87fffff1fffdf7df7df7df7df7df7df7df7df7df7df7df7c1f07fff83fff83fffffffe0f03fe1ffffffffffffffffffffffffffe183fffc7ffffa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fffffffffffffffffc00ffffff007fe000000ff803fffc1f87e007c7fff00ffffffea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ffff81ffffc0ffc1ff0001ffffc01e18000003fe0003c307e1f801f1fffc001f8ffffd6fd6fd6fd6fd6fd6fd6fd6fd6fd6fd6fd6ffffffffffffffffffe0ffffc0f87ffff81fffffc3fffffff800fffffe0f8ffffffebeebeebeebeebeebeebeebeebeebeebeebeffff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8fffafbafbafbafbafbafbafbafbafbafbafbafbfffe07ffff03ff07ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e3ffffb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7ffffffffffffffffffffffffffffff801f803ffffffff0001ffc001ffffffffffffae9ae9ae9ae9ae9ae9ae9ae9ae9ae9ae9ae9fffe07ffff03ff07ffff07fffffff86007e00ffffc0f0c0007ff0007fffff07e3ffebeebeebeebeebeebeebeebeebeebeebeebeffff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8ffffdffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffffe0ffffc0f87fffffffffffc3fffffffffffffffe0f8ffffffea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ffff81ffffc0ffc1ff0001fff0001e1ffffffffe0003c3ffffffffffff80001f8fffa92a92a92a92a92a92a92a92a92a92a92a92fffe07ffff03ff07fc0007ffc000787ff8000ff8000f0ffff8000007fe00007e3ffea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ffff81ffffc0ffc1ff0001fff0001e1ffffffffe0003c3ffffffffffff80001f8fffbbfbbfbbfbbfbbfbbfbbfbbfbbfbbfbbfbbffffe07ffffffff07fc1f07ffff07f87ffffffff83fff0ffffffffffffff07ffe3ffde51e51e51e51e51e51e51e51e51e51e51e501f07fff83fff83fff003fe0f00001fffe07fffe00fffff81e003e0fe18003fc700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffdf51f51f51f51f51f51f51f51f51f51f51f501f07fff83fff83ffff83fe0f03e01fffe07fffff0fffff81e003e0fe183e3fc7000040040040040040040040040040040040040000000000000000003e0000000f8000000000007c000000000000000000f80000003d13d13d13d13d13d13d13d13d13d13d13d13fffffffffffffffc0f83e00003e01e000000001f0fc3c00000000000003e3e07000f6df6df6df6df6df6df6df6df6df6df6df6dffffffffffffffff03fff8003fff878007e00007fff0f00007ff000001ffff81c003c6fc6fc6fc6fc6fc6fc6fc6fc6fc6fc6fc6ffffffffffffffffc000000000000007fffffc00000000fffffffffe000000000000f7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bffffffffffffffff03ff00003fff801ffffff007fc0003fffffffff801fff0003ffff13f13f13f13f13f13f13f13f13f13f13f13ffffffffffffffffff83ffff03e1ff8000003fff0ffff0000000001ff83e3fffffffedfedfedfedfedfedfedfedfedfedfedfedffffffffffffffffffffffffffffffe007e00ffffffffc0007ff0007ffffffffc0001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc00000057f57f57f57f57f57f57f57f57f57f57f57f0001f80000fc00f803fff8003fff879ffffff007fff0f3fffffffff801ffff81ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffff003ffff0001ffffffffffe00ffffffffffffffff8003fffffff84f84f84f84f84f84f84f84f84f84f84f84fffffffffffffffffc00ffffc0007fe000000ff803fffc0000000007fe000fffc0035bf5bf5bf5bf5bf5bf5bf5bf5bf5bf5bf5bfe0ffe007c3f07fe00fffe1f0fffffe001f80001fffc3c07e1ffc1f01e7fffe3ffff79f79f79f79f79f79f79f79f79f79f79f79f07c1fffe0fffe0fffc00ff83c00007fffffffff803ffffffffffffff86000ff1fffffbffbffbffbffbffbffbffbffbffbffbffbfffffffffffffffffffffffffffffff801f803ffffffff07e1ffc1f1ffffffffffff78478478478478478478478478478478478407c1fffe0fffe0fffc00ff83c00007e000000ff803fffc000000000786000ff1fffffd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fffffffffffffffffffffffffffffffc007c3fffffffff800003e01ffffffffffffce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ffffff81ff001fffffffffffffffffe007e0007ffc00fc0007ff00007ffff00fffff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03f00001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003fff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03ffffcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbffffff81ff001ffffffffffffffffffffffff07ffc00fffffffffff87ffff00fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff81ff001fffffffffffffffffe00000007ffc00fc00000000007ffff00fc000c7cc7cc7cc7cc7cc7cc7cc7cc7cc7cc7cc7c000001f803ff8000000000000000007ffffffe000ffc0ffffffffffe00003fc0fffce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff81ff001fffffffffffffffffe00000007ffc00fc00000000007ffff00fc001d51d51d51d51d51d51d51d51d51d51d51d500007e1f803ff83e00f83e00003e01e7c007c3e1f0fffcf800003e01e003e3fc7fff7d47d47d47d47d47d47d47d47d47d47d47d407c1fffe0fffe0ffffffff83c0ff87ff001f0fffffffffe00000f807860ffff1c003cffcffcffcffcffcffcffcffcffcffcffcfffffffffffffffffc000001f0fc01e07ffffffe000ffc0fffffffffffe7c03ff8000f1ff1ff1ff1ff1ff1ff1ff1ff1ff1ff1ff1fffffffffffffffff000000000000001fffffff8003ff03ffffffffff80000ff00003cefcefcefcefcefcefcefcefcefcefcefceffffffffffffffffc000001f0fc01e07fffffc00000000fffffffffe1e7c00038000f37f37f37f37f37f37f37f37f37f37f37f37ffffffffffffffff0000007c3f00781f001f0f8003ff03ff87e0ffc7f9f00ffe000359f59f59f59f59f59f59f59f59f59f59f59fe0ffe007c3f07fe00f83e1f0ffe1fe000000001f0fc3c07e1f801f01e7fe3e3f00086b86b86b86b86b86b86b86b86b86b86b86bf83e0001f0001f0003ff007c3ffff80007e00007fc00001f87ff07c079fff00e3fff38f38f38f38f38f38f38f38f38f38f38f38ffffffe07fc007fffffffffffffffff80000001fff003f07e1f801f01ffffc03f000f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff83ff87ff0fffff803e0f87c3ff87f9fffffff87c3fff3fffffffffff9ff8fffc001d7dd7dd7dd7dd7dd7dd7dd7dd7dd7dd7dd7c0007e1f803ff83e00f83e00003e01e7ffffffe1f0fffcffffffffffe003e3fc7000d7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7ff83ff801f0fc1ff803e0f87c3ff87f9ffffff007c3f0f3fffffffff879ff8f8fc003ddfddfddfddfddfddfddfddfddfddfddfddfe0ffe1ffc3ffffe00f83e1f0ffe1fe7c007c3e1f0fffcffe1f83ff1fe7fe3fff000b7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7ff83e007ff0ffff0003ff007c3ffff81fffffff87ffff03fffffffffff9fffffe0000dfcdfcdfcdfcdfcdfcdfcdfcdfcdfcdfcdfc000001f803ff80000ffc0000fffe007ffffffe1ffffc0ffffffffffe07ffffc000087b87b87b87b87b87b87b87b87b87b87b87bf83e0001f0001f0003ff007c3ffff81ffffff007fc0003fffffffff879fff00e0002dfedfedfedfedfedfedfedfedfedfedfedffe0f801ffc3fffc000ffc01f0ffffe07c1ffc3e1ffffc0ffe1fffff1fe7fffff8000b3fb3fb3fb3fb3fb3fb3fb3fb3fb3fb3fb3ff83e007ff0ffff000000007c3f00781fffffff8003ff03fffffffffff9f00ffe3ffd36d36d36d36d36d36d36d36d36d36d36d36c1f07fe003c0003fffffffe0f03fe1fffffffc1fff003ffffffffffe0183fc007fff7df7df7df7df7df7df7df7df7df7df7df7df07c1fffe0fffe0ffffffff83c0ff87ffffffffffffffffffffffffff860ffff1ffff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03ffffff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ffffffffffffffffffffffffffffffff001f0fffffffffff87e0ffc7ffffffffffff383383383383383383383383383383383383fffffe003c0003ffffffffffffffff80000001fff003f00000000000183fc007000b37b37b37b37b37b37b37b37b37b37b37b37f83e007ff0ffff000000007c3f00781f001f0f8003ff03ff87e0ffc7f9f00ffe3ffd3013013013013013013013013013013013001f07fe003c0003fffffffe0f03fe1f80000001fff003f00000000000183fc00700031f31f31f31f31f31f31f31f31f31f31f31f0000007e00ffe000000000000000001fffffff8003ff03ffffffffff80000ff00003c53c53c53c53c53c53c53c53c53c53c53c53fffffffffffffffc000000000000007c007c3e000ffc0f800003e01e00003fc0000c00c00c00c00c00c00c00c00c00c00c00c00ffffff81ff001fff00000000000000000000000000000000000000000000000000020ee0ee0ee0ee0ee0ee0ee0ee0ee0ee0ee0efe0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038000f23f23f23f23f23f23f23f23f23f23f23f23ffffffffffffffff0000007c3f007800000000000000001f87e007c079f0000e0001c01c01c01c01c01c01c01c01c01c01c01c001f07fff83fff83fc000000000000000000000000000000000000000000000000000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0000003383383383383383383383383383383383383fffffe0000000003ffffffffffffff800000000000000000000000000000000000001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003ffea4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bfff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00015b55b55b55b55b55b55b55b55b55b55b55b40007e00003f003e00fffe000fffe1e001f80001fffc3c0001ffc000007fffe0700055f55f55f55f55f55f55f55f55f55f55f55f0001f80000fc00f803e0f80000f8079ffffff007c3f0f3fffffffff8000f8f81c0001ec1ec1ec1ec1ec1ec1ec1ec1ec1ec1ec1ec00000000000000000ffc0000fffe007fffffc01ff0000fffffffffe007ffc000000a92a92a92a92a92a92a92a92a92a92a92a92ffc0007fff000000fc00007fc000001ff8000ff8000003fff8000007fe0000003ffc37c37c37c37c37c37c37c37c37c37c37c37c0000000000000003fffffe0f03fe1ffffffffffffffffffffffffffe183fffc700001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003ffc3703703703703703703703703703703703700000000000000003fffffe0f03fe1fffffffffffffffff81e07fe0fe183fffc700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff8000000000ffffffffffffffe00000000000000000000000000000000000003703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff000000000000000000000001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000000002a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0000000c50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00015115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07
def frontierCount : Nat → Nat → Nat
  | 9, 0 => 15
  | 10, 0 => 341
  | 10, 1 => 12
  | 11, 0 => 253
  | 11, 1 => 230
  | 11, 2 => 81
  | 11, 3 => 6
  | 12, 0 => 25
  | 12, 1 => 34
  | 12, 2 => 34
  | 12, 3 => 17
  | 12, 4 => 3
  | 13, 0 => 3
  | 13, 1 => 4
  | 13, 2 => 4
  | 13, 3 => 4
  | 13, 4 => 4
  | 13, 5 => 1
  | _, _ => 0
def leafCount : Nat → Nat → Nat
  | 9, 0 => 15
  | 10, 0 => 339
  | 10, 1 => 12
  | 11, 0 => 223
  | 11, 1 => 228
  | 11, 2 => 81
  | 11, 3 => 6
  | _, _ => 0
def frontierSlotBits : Nat → Nat → Nat
  | 9, 0 => 104
  | 10, 0 => 114
  | 10, 1 => 104
  | 11, 0 => 124
  | 11, 1 => 114
  | 11, 2 => 104
  | 11, 3 => 94
  | 12, 0 => 114
  | 12, 1 => 114
  | 12, 2 => 114
  | 12, 3 => 104
  | 12, 4 => 94
  | 13, 0 => 104
  | 13, 1 => 104
  | 13, 2 => 104
  | 13, 3 => 104
  | 13, 4 => 104
  | 13, 5 => 94
  | _, _ => 0
def frontierData : Nat → Nat → Nat
  | 9, 0 => 0x151201e1500201421068099000151404803802014210680990004c1201e0380201421068099130161201e038020142106809a000150481e0340111022090099054280481e034011102209009a0541207840038020182209009a0f0160481e034020182209009a0e0160481e038010182209009a000150d01e0340101822090099054340a01e034010182209009a0002c0481e03401018220900990c0160481e034010182209009a0b0160481e034010182209009a0b0280481e034010182209009a
  | 10, 0 => 0x150481e0340101822090099000150a0120780d004060882402686c180120784003930018220680ab1803c0481e8f00e4c0060881a02ac94058120780e8e002018220680ab0e0160481e100022f0060881a02ac3805812078403405c018220680ab1b0380481e10002170060881a02ae34058120780e0085c018220680ab1b0160481e03802740060881a02ac3805812078404c074018220680ab250160481e10002018680881a02ad98058120780e008061a0220680ab1b0160481e03802019ac0881a02ad28058120780e008060881a8c00ab0e0160481e038020182206a2c02ac00000150481e100b44c05c0680990012805812078402d1300181a0268000e0160481e101301700606809a00114058120780e4c05c0181a0269140e0160481e039301700606809b300160481e1000e4c05c0181a026e180581207840039301700606809b000000e1280481e101300141a0264600581207840039e04c02206809b000600f0120780d781300881a026800250160481e100021702206809a2506005812078400085c0881a026c9405812078402d0021702206809b300160481e100b40085c0881a026c150481e820402d0021702206809b05412078408a0b40085c0881a026c0005412078402d0028902206809a05412078402d002172240881a026c150481e100b40085c7402206809b0009405812078404c0060881a0268940e0160481e101300182206809b2506005812078404c0060881a026c380581207908101300182206809b250160481e100b44c0060881a026d1405812078402d1300182206809b860160481e100b44c0060881a026c150481e820402d1300182206809b0541207908100b44c0060881a026c941803c0481e039300182206809b450600f0120780e4c0060881a026c600f0120792c039300182206809b660160481e1000e4c0060881a026e1c0581207840039300182206809b05812078408800e4c0060881a026e1c1803c0481e035300182206809b182180f0120780d4c0060881a026c380581207840781300182206809b000600f0120780d850060881a0268600f0120780d4c2140182206809b180160481e1000e840060881a026c00058120784003a100182206809a058120784003930840060881a026c600f0120780d4c2100182206809b000150481e100b4730060881a026800180160481e039cc0182206809a180160481e1000e730060881a026c150481e100b44c1cc0182206809b180160481e03930730060881a026e0c250160481e100020182206809b830380581207840008060881a026c380581207a08100020182206809b250160481e4b040008060881a026c1504a04078402d0020182206809b054127201e100b4008060881a026c007c0160481e038020182206809a7c094058120780e008060881a026c1504a000780e780020182206809b054127f01e039e0008060881a026c38058120780e770020182206809b000160481e039dc008060881a026815049f80780e2e0020182206809b055f40481e2d130008060881a026df0058120780e4c0020182206809b054127b01e03930008060881a026c15049e80780e4c0020182206809b05412078b403930008060881a026c160481e039dc4c0020182206809b250160481e039e4008060881a026c00058120780e790020182206809a058120780e4c1e4008060881a026c94058120780e6c0020182206809b058120780e781b0008060881a026c160481e039dc6c0020182206809b054125901e10002170060881a026c3805812079180085c0182206809b000160481e46002170060881a0268160481e101180085c0182206809b054127601e03802170060881a026c151201e1000e0085c0182206809b054120784003802170060881a026c380581207840009d40182206809b0e0160481e10002740060881a026dc00e0160481e101300142206809b0e0160481e4b0404c0050881a026c3805812078404c1b00142206809b000380581207840730050881a02683805812078404c1cc0142206809b0003805812079b8008050881a026800000160481e6e002014220680994a0160496407840008050881a026c38058127201e100020142206809b00038058126d00e008050881a02680000016049b4038020142206809900016049bc0780e008050881a0269280584807840038020142206809b4a0160481e1000e008050881a026c3805812079b84c0020142206809b000160481e6e130008050881a02683805812079604c0020142206809b0e016049b403930008050881a026c00058126d00e4c0020142206809a440380481e03930008050881a026dc4058120780e4c0020142206809b0e0160481e03930008050881a026c38058120792c6c0020142206809b0e0160481e6e1b0008050881a026c0005812079b86c0020142206809a0e016049b4039b0008050881a026c00058126d00e6c0020142206809a700160481e039b0008050881a026c16049bc0780e6c0020142206809b05812079b84c1b0008050881a026c16049b4039306c0020142206809b05412078402d130019ac0881a026c60058120780d2e0026a02206809b1803c0481e03402019a80881a026ca4058120780d008066a02206809b0e0160481e10002015a40881a026d14058120780e008056902206809b450160481e03802015a00881a026c38058120780e008056802206809b0f0160481e03802015a00881a026c160481e1000e008056802206809b000600f0120780d0099c0841a026860058125b01e1000e0182106809b180160481e1000e610060841a026c001803c0481e035840182106809a000a4058120780d610060841a0268a4180160481e035840182106809b660940581207840008060841a026c60058125901e100020182106809b000940581207994008060841a026800000160481e6500201821068099250160481e10194008060841a026c000581207840650020182106809a520160481e100b4008060841a026c600581207990038020182106809b180161201e1000e008060841a026d781801207840038020182106809b180160481e1000e008060841a026c00620600481e034020182106809a62178180120780d008060841a026d78290600481e034020182106809b000600f0120780d008060841a026800290160481e034020182106809a29060058120780d008060841a026c38058120780e630020182106809b0e0160481e580b8008060841a026d100e0120780e2e0020182106809b0e0160481e038b8008060841a026c94058120780e610020182106809b620600481e03584008060841a026c60058120780d610020182106809b250160481e03920008060841a026c60058120780e600020182106809b05812078b403980008060841a026d7c5e0600481e038010182106809b00104180120780e004060841a026978250600481e038010182106809b00094058120780e004060841a0268000581207900038010182106809a250160481e2d00e004060841a026c160481e400b4038010182106809b0e0160481e100025d0060841a026c38058120780e005740182106809b450160481e038025c0060841a026c38058120780e009700182106809b0f0160481e038025c0060841a026c160481e1000e009700182106809b00038058125b01e100050841a026954058125b01e1000e0142106809b450160496c07840038050841a026c000e0160481e101200142106809a00114058120780e480050841a0269140e0160481e039200142106809b0003c058120780e480050841a0268000581207840039200142106809a00038058120791c008050841a0268000e0161201e100020142106809a000155a04807840008050841a026800440380481e100020142106809a001480e01207840008050841a026800560160481e100020142106809a560380581207840008050841a026c000e0160481e100020142106809a000151216407840008050841a026958058125901e100020142106809b450160496407840008050841a026c00054125901e100020142106809a0e0160481e47040008050841a026d140e0160481e580020142106809b0e0160481e47160008050841a026c00450160481e570020142106809a00038058120795c008050841a0268000581207840570020142106809a00114058480780e008050841a026800450165301e038020142106809a000380594c0780e008050841a0268000f0165301e038020142106809a00148450120780e008050841a026954440380481e038020142106809b001480e0120780e008050841a026910450380481e038020142106809b001480f0120780e008050841a026800560160481e038020142106809a00154058120780e008050841a026800450160481e038020142106809a56038058120780e008050841a026d140e0160481e038020142106809b5503c058120780e008050841a026c00058120791c038020142106809a540161201e1000e008050841a026d480584807840038020142106809b450161201e1000e008050841a026c000544807840038020142106809a000165301e1000e008050841a0269480581207840038020142106809b450160481e1000e008050841a026c160481e47040038020142106809b0e0160481e47120008050841a026c38058120780e480020142106809b001100e0120780e004050841a026800054120780d0045c0182209009a054280481e034011700608824026c00000150481e034020142106808900015049440780d008050841a022800054120780d340020142106808a054125101e034d0008050841a022c001b0160481e034010142106808a00000058120780d004050841a02246c058120780d004050841a3e008b000160481e0340101421068f8022800054120780e004060841a0293ca054125001e03801018210680a4f2c150481e2d00e004060841a0293cb000150481e0380201821068094d2815049380780e008060841a02534b05412078b40380201821068094d2c380581207840340050841a0290cb1b0380481e10002014210680a432c3805812078404c0050881a0250cb0e0160481e4b0020142206809432c384a01207840008050881a0250cb0e1280481e038010142206809432d24058120780e004050881a0250cb250160481e100020182106809432c94058120780e004060841a0250cb0e0160481e101200142106809432c38058120791c008050841a0250cb440380481e100020142106809432c380581207840008050841a0250cb0e0160481e460020142106809432c000581207918008050841a0250ca0581207840460020142106809432d14058120780e008050841a0250cb440380481e038010142106809432c160481e100b4008060841a024fcb1803c0481e0380201821068093f2ca4058120780e008060841a024fcb05812079080380201821068093f2d04180120780e004060841a024fcb05812079000380101821068093f2c6c180120780d3400201821068d4b1b0380481e038d0008050841a352c6c0e0120780e004050841a3e0d4b1b0600481e034b8008210680a352ca8180120780d008060841a028d4b1b0940481e03801018210680a352c6c0e01207840008050841a028d4b1b0380481e3d001014210680a352c6c0e0123700e004050841a028d4b26016048dc03801014210680a352c6c3c0120780e004050841a028d4b1b0380481e03801014210680a352c6c3b0120780e004050841a028d4b0e0ec0481e03801014210680a352c003b0120780e004050841a028d4a260160481e03801014210680a352c6c3a0123700d004050841a028d4b1b0e4048dc03401014210680a352c6c058123700d004050841a028d4b1b0e40481e03401014210680a352c6c058123800d004050841a028d4b00016048e003401014210680a352816048dc3800d004050841a028d4b05812370d803401014210680a352c6c058120780d004061a02206870b230160481e034d0008060841a1c2c6c058120780d340020182106870b058120780d340021d0060841a1c2c8c058120780d004060841a33070b1b0160481e0340101821068cc1c2c160481e034011d0060841a33070b180160481e03401170220680a1c2cc8058120780d004060881a02870b310160481e03401018220680a1c2cc0058120780d004060881a02870b058120780d004bc018220680a1c2c60058120780d2e0020841a02870b05812078b4038011d0210680a1c2c8c058120780d004b00841a02870b180160481e034012c0210680a1c2c160481e034011d0b00841a02870b1803c0481e03402018210680a1c2cac058120780d008060841a02870b2a0160481e03402018210680a1c2ca4058120780d008060841a02870b058120780d28002018210680a1c2c6c0e0120780e004060841a02870b270160481e03801018210680a1c2c98058120780e004060841a02870b250160481e03801018210680a1c2c160481e2400e004060841a02870b230160487803401018210680a1c2c6c058121e00d004060841a02870b180160487803401018210680a1c2c8c220120780d004060841a02870b1b0880481e03401018210680a1c2c60220120780d004060841a02870b210160481e03401018210680a1c2c80058120780d004060841a02870b058120780d0047c018210680a1c2c1604878034011d0060841a02870b1b0160481e03401014680881a192c60058120780d0045c0881a02458b
  | 10, 1 => 0x58120784003a100182206809a0003c0481e0361001822068099058120780e770020182206809a000160481e101b001422068099000160481e6e0020142206809900016049b4038020142206809905812079b86c0020142206809a058126d00e6c0020142206809a520161201e038020142106809a0e0123700e004050841a028d4a3a0123700d004050841a028d4a390123700d004050841a028d4a
  | 11, 0 => 0x1b0160481e1000e0085c018220680ac180160481e1000e008061a0220680ac0000005412078402d0021702206809a0000005412078402d1300182206809a000600581207840039300182206809b000001803c0481e035300182206809a00094058120780e4c0020182206809b0003805812078400085c0182206809b000000e0160481e101300142206809a00000058120780e6c0020142206809a0e0160481e039306c0020142206809c000160481e039306c0020142206809b00000250160481e100020182106809a00060058120780d610020182106809b00000054125901e100020142106809a000000544807840038020142106809a000000541207840038020142106809a00038058120780e480020142106809b00000440380481e038010142106809a000000e0160481e038010142106809a000380581207840008050841a0250cb00038058120780e004050841a0250cb000160481e2d00e004060841a024fcb0006c0e0120780e004050841a028d4b0006c058123700d004050841a028d4b0006c058120780d004050841a028d4b0008c058120780d004060841a02870b0006c058120780d004060841a02870b00060058120780d004060841a02870b000160481e034011d0060841a02870b4a0160481e1000e00874018220680ac0f0160481e9100e00874018220680ac0e0160481e038b8008061a0220680ac0003c05812078b4039300182206809b0012805812078402d0020182206809b000150481e4b0402d0020182206809b000150481e102282d0020182206809b000000541207a08038020182206809a0003c0581207a28038020182206809b0021805812078b4038020182206809b8612805812078b4038020182206809c0f0160481e8a0b4038020182206809c00038058120780e780020182206809b000150481e8200e780020182206809b000150481e4b00e780020182206809b000150481e4200e780020182206809b000150481e8a00e780020182206809b000380581207a442e0020182206809b000384a0120780e2e0020182206809b00124058120780e2e0020182206809b49038058120780e2e0020182206809c49128058120780e2e0020182206809c000150481e8200e2e0020182206809b4a0160481e4200e2e0020182206809c290160481e9100e2e0020182206809c0541207a089100e2e0020182206809c0e0160481e039e02e0020182206809c0541207a08039e02e0020182206809c0541207908039e02e0020182206809c25060058120780e4c0020182206809c000150481e8200e4c0020182206809b250160481e2d00e4c0020182206809c860160481e2d00e4c0020182206809c0541207a082d00e4c0020182206809c0e0160481e039e04c0020182206809c0541207a08039e04c0020182206809c054120792c039e04c0020182206809c00114058120780e0085c0182206809b45038058120780e0085c0182206809c4503c058120780e0085c0182206809c000150481e8200e0085c0182206809b300160481e1000e0085c0182206809c0541207a081000e0085c0182206809c0f0160481e8a00e0085c0182206809c0e0160481e039e00085c0182206809c0541207a08039e00085c0182206809c0541207a28039e00085c0182206809c00000054120780e009d00182206809a000150481e03802171d00182206809b054120784003802171d00182206809c00000054120780e00a640182206809a000150481e038b800a640182206809b0541207a44038b800a640182206809c000000e0160481e4b0020142206809a000000e1280481e100020142206809a001240e0160481e100020142206809b00038058120792c100020142206809b001140e0160481e910020142206809b00038058120792c910020142206809b001140e1280481e038020142206809b00038861280481e038020142206809b00000700160481e038020142206809a001c0860160481e038020142206809b00124860160481e038020142206809b001c04a0160481e038020142206809b702184a0160481e038020142206809c492184a0160481e038020142206809c001c0058120792c038020142206809b00114058120792c038020142206809b00124058120792c038020142206809b00218058120792c038020142206809b001c00581207840038020142206809b701280581207840038020142206809c700160481e4b040038020142206809c450160481e4b040038020142206809c001280581207a60038020142206809b000000581207a60038020142206809a4a0160481e10260038020142206809c000160481e10260038020142206809b001c00581207a44038020142206809b701240581207a44038020142206809c7003c0581207a44038020142206809c700160481e4b244038020142206809c490160481e4b244038020142206809c000000581207a5c038020142206809a0f0160481e9125c038020142206809c000160481e9125c038020142206809b00038058120792c4c0020142206809b001c0058120780e4c0020142206809b70038058120780e4c0020142206809c70218058120780e4c0020142206809c700160481e4b00e4c0020142206809c860160481e4b00e4c0020142206809c00000054120780e008066b02206809a000150481e03930008066b02206809b05412078b403930008066b02206809c00094180160481e100020182106809b0009405812078402d0020182106809b0011405812078402d0020182106809b000941803c0481e038020182106809b001141803c0481e038020182106809b00000660160481e038020182106809a00198250160481e038020182106809b00198290160481e038020182106809b00094290160481e038020182106809b00198180160481e038020182106809b66094180160481e038020182106809c660a4180160481e038020182106809c250a4180160481e038020182106809c001980581207908038020182106809b000940581207908038020182106809b001140581207908038020182106809b000a40581207908038020182106809b001980581207840038020182106809b660600581207840038020182106809c660160481e42040038020182106809c450160481e42040038020182106809c000600581207a20038020182106809b000000581207a20038020182106809a180160481e10220038020182106809c000160481e10220038020182106809b0019805812078b4038020182106809b6609405812078b4038020182106809c660160481e420b4038020182106809c250160481e420b4038020182106809c000a41803c0481e034020182106809b00000182580481e034020182106809a000600f2580481e034020182106809b000000f2580481e034020182106809a00000002580481e034020182106809900198058120780e2e0020182106809b66038058120780e2e0020182106809c660a4058120780e2e0020182106809c660160481e4200e2e0020182106809c290160481e4200e2e0020182106809c00038058120780e950020182106809b00000058120780e950020182106809a0e0160481e038b8950020182106809c000160481e038b8950020182106809b00000058120780d610020182106809a0003c058120780d00a500182106809b00000058120780d00a500182106809a00038058120780e005740182106809b00000058120780e005740182106809a001140e0160481e100020142106809b000000e0160481e460020142106809a00000000160481e4600201421068099000380581207840460020142106809b000000581207840460020142106809a00000000151201e038020142106809900000520160481e038020142106809a001480581207840038020142106809b0003c058120795c038020142106809b00000058120795c038020142106809a000009303c0481e034020142106809a000000f0160481e034020142106809a00000058120780e480020142106809a0f0160481e8f00e008050841a02a48c000160481e8f00e008050841a02a48b0f0160481e03402170060881a02648c000160481e03402170060881a02648b0f0160481e9100e008050881a02648c000160481e9100e008050881a02648b0f0160481e2d00e008060841a02648c000160481e2d00e008060841a02648b000600f0120780d008060841a02648b000a4058120780d008060841a02648b2903c058120780d008060841a02648c0f0160481e03402940060841a02648c000160481e03402940060841a02648b00114058120780e008050841a02648b4503c058120780e008050841a02648c0f0160481e5700e008050841a02648c000160481e5700e008050841a02648b0024c0f0120780d008050841a02648b0003c058120780d008050841a02648b0e0160481e038d0008050841a0290cc000160481e038d0008050841a0290cb0e0160481e03801170060881a0250cc000160481e03801170060881a0250cb0e0160481e03930008050881a0250cc000160481e03930008050881a0250cb000384a0120780e004050881a0250cb00124058120780e004050881a0250cb49038058120780e004050881a0250cc0e0160481e03801015a40881a0250cc000160481e03801015a40881a0250cb0e0160481e038b8008060841a0250cc000160481e038b8008060841a0250cb00094058120780e004060841a0250cb25038058120780e004060841a0250cc0e0160481e038015d0060841a0250cc000160481e038015d0060841a0250cb00114058120780e008050841a0250cb45038058120780e008050841a0250cc0e0160481e03920008050841a0250cc000160481e03920008050841a0250cb001100e0120780e004050841a0250cb00124058120780e004050881a02640b49038058120780e004050881a02640c00038058120780e004050881a02640b00000058120780e004050881a02640a490160481e9100e004050881a02640c000160481e9100e004050881a02640b00094058120780e004060841a024fcb00000058120780e004060841a024fca250160481e2d00e004060841a024fcc1b0160481e034b8008060841a028d4c000160481e034b8008060841a028d4b1b0160481e2d00e004060841a028d4c000160481e2d00e004060841a028d4b1b0160481e1000e008050841a028d4c000160481e1000e008050841a028d4b00098058120780e004050841a028d4b2606c058120780e004050841a028d4c1b0160481e3d00e004050841a028d4c000160481e3d00e004050841a028d4b00000058123700d004050841a028d4a0006c390120780d004050841a028d4b2306c058120780d004060841a02870c23060058120780d004060841a02870c00000058120780d004060841a02870a230160481e034011d0060841a02870c
  | 11, 1 => 0x160481e039b0008050881a026800058123700d004050841a028d4a000150481e100b40085c0881a02680005412078402d1300182206809a180160481e1000e4c0060881a026c3c05812078b4039300182206809b000600f0120780d4c0060881a02692805812078402d0020182206809b054120792c100b4008060881a026c150481e102282d0020182206809b000150481e8200e008060881a02683c0581207a28038020182206809b860160481e2d00e008060881a026c38058120780e780020182206809b0541207a08039e0008060881a026c150481e4b00e780020182206809b0541207908039e0008060881a026c150481e8a00e780020182206809b0e0160481e910b8008060881a026c384a0120780e2e0020182206809b490160481e038b8008060881a026c150481e8200e2e0020182206809b250160481e03930008060881a026c150481e8200e4c0020182206809b0e0160481e10002170060881a026d14058120780e0085c0182206809b0541207a0803802170060881a026c00054120780e009d00182206809a054120780e0085c740060881a026c00054120780e00a640182206809a054120780e2e002990060881a026c000e0160481e101300142206809a00038058120792c008050881a0268000e1280481e100020142206809a490380581207840008050881a026c38058120792c100020142206809b450380581207a44008050881a026c38058120792c910020142206809b450384a0120780e008050881a026c38861280481e038020142206809b001c0058120780e008050881a0269c0860160481e038020142206809b49218058120780e008050881a026dc04a0160481e038020142206809b700160481e4b00e008050881a026d14058120792c038020142206809b490160481e4b00e008050881a026e18058120792c038020142206809b700160481e1000e008050881a026d280581207a60038020142206809b000160481e9800e008050881a0268160481e10260038020142206809b700160481e9100e008050881a026c000581207a5c038020142206809a0581207a449700e008050881a026c38058120792c4c0020142206809b700160481e03930008050881a026c160481e039306c0020142206809b000150481e03802019ac0881a0268150481e03930008066b02206809b000940581207840008060841a026894180160481e100020182106809b250160481e100b4008060841a026d1405812078402d0020182106809b250600f0120780e008060841a026d141803c0481e038020182106809b00198058120780e008060841a026998250160481e038020182106809b660a4058120780e008060841a026c94290160481e038020182106809b66060058120780e008060841a026d980581207908038020182106809b250160481e4200e008060841a026d140581207908038020182106809b290160481e4200e008060841a026d980581207840038020182106809b180160481e8800e008060841a026c000581207a20038020182106809a05812078408800e008060841a026d9805812078b4038020182106809b290600f0120780d008060841a026c00182580481e034020182106809a1803c960120780d008060841a026c000f2580481e034020182106809a00000960120780d008060841a026598058120780e2e0020182106809b0e0160481e03a54008060841a026c00058120780e950020182106809a058120780e2e254008060841a026c60058120780d610020182106809b000160481e03584008060841a02683c058120780d00a500182106809b000160481e03402940060841a026838058120780e005740182106809b000160481e038015d0060841a0269140e0160481e100020142106809b000150496407840008050841a0268000e0160481e460020142106809a000000581207918008050841a0264380581207840460020142106809b000160481e10118008050841a026800000151201e038020142106809900148058120780e008050841a0268000544807840038020142106809a520160481e1000e008050841a026c000541207840038020142106809a0f0160481e5700e008050841a026c00058120795c038020142106809a0024c0f0120780d008050841a0268000f0160481e034020142106809a0e0160481e03920008050841a026c00058120780e480020142106809a001100e0120780e004050841a0268000e0160481e038010142106809a002830481e034b8008060841a9ee800a0c12078b4038010182106a7ba000120780d340021d0060841a9ee800a0c1207840038020142106a7ba000120780d8e002014220680a9ee81207a3c03930008050881a02a7bb0481e036384c002014220680a9eec120780d2e002018680881a02a7bb0481e1000e008051a0220680a9eec120780d8e002014680881a02a7bb000120780d2e0d0018210680a9ee8000481e034a0008060841a02a7ba0481e8f00e2e002018210680a9eec120780d280b8008060841a02a7bb0481e2d00e34002018210680a9eec120780d280d0008060841a02a7bb0001207a3c2d001018210680a9ee8000481e2400e004060841a02a7ba0481e240b403801018210680a9eec1207840038021d0060841a02a7bb0481e034a000874018210680a9eec1207890038011d0060841a02a7bb000129bc1e8f00e014210680a9ee8000481e1000e340050841a02a7ba0001207a7c03802014210680a9ee81207a7c1000e008050841a02a7bb0481e9f23c03802014210680a9eec0004a6b078d0008050841a02a7ba0481e9f00e34002014210680a9eec1207a44038b8008060881a0267bb0481e2d00e4c00201822068099eec0004a6f0780d170060881a0267ba0481e1000e0085c01822068099eec0004a6f07a44038050881a0267ba00012078400393001422068099ee8000481e4b00e008050881a0267ba0481e4b0400380201422068099eec120792c9100e008050881a0267bb000129ac1e4c00201422068099ee8120792c03930008050881a0267bb0000004a739bc1e03421068099ee40004a7307840038020841a0267ba0000004a739ac1e00421068099ee40004a6f078b4038060841a0267ba00012078402d00201821068099ee8000481e4200e008060841a0267ba0481e420400380201821068099eec12079082d00e008060841a0267bb000129ac1e2e00201821068099ee81207908038b8008060841a0267bb0000004a6f9ac1e01421068099ee4160481e8f00e008050841a02a48b058120780d0085c0182206809922c160481e9100e008050881a02648b0f01604a730780d0082106809922c00058129cc1e034020841a02648a05812078b4038020182106809922c00180120780d008060841a02648a1803c0481e034020182106809922ca4058120780d008060841a02648b058120780d00a500182106809922c3c058129ac1e008050841a02648b0001604a6b078020142106809922914058120780e008050841a02648b058120795c038020142106809922c00930120780d008050841a02648a9303c0481e034020142106809922c3c058120780d008050841a02648b058120780e34002014210680a432c3805a770481e038010141a0250cb000169dc120780e00405068094328160481e03801170060881a0250cb058120780e4c0020142206809432c384a0120780e004050881a0250cb001280481e038010142206809432924058120780e004050881a0250cb058120780e004056902206809432c38058129cc1e038010841a0250cb0001604a730780e00421068094328160481e038b8008060841a0250cb250160481e038010182106809432c160481e038015d0060841a0250cb0e01604a6f0780e0142106809432c00058129bc1e038050841a0250ca0e0160481e100020142106809432c000581207840008050841a0250ca450160481e038020142106809432c160481e03920008050841a0250cb001100481e0380101421068094329100e0120780e004050841a0250cb0e0160481e038010142106809432d24058120780e004050881a02640b0e0160481e038010142206809902c00058120780e004050881a02640a0581207a44038010142206809902c94058120780e004060841a024fcb000160481e0380101821068093f28160481e2d00e004060841a024fcb058120780d2e002018210680a352c160481e2d00e004060841a028d4b058120784003802014210680a352c6c058129ac1e004050841a028d4b0001604a6b07801014210680a35286c0e0120780e004050841a028d4b000380481e03801014210680a352898058120780e004050841a028d4b05812078f403801014210680a352c6c058123700d004050841a028d4b1b0e40481e03401014210680a352c00390120780d004050841a028d4a1b0160481e03401014210680a352c8c058120780d004060841a02870b1b0160481e03401018210680a1c2c60058120780d004060841a02870b000160481e03401018210680a1c28160481e034011d0060841a02870b
  | 11, 2 => 0x5412078402d0021702206809a05412078402d1300182206809a1803c0481e035300182206809a0541207a08038020182206809a054120780e009d00182206809a054120780e00a640182206809a0e0160481e101300142206809a0e0160481e4b0020142206809a0e1280481e100020142206809a700160481e038020142206809a0581207a60038020142206809a0581207a5c038020142206809a058120780e6c0020142206809a054120780e008066b02206809a250160481e100020182106809a660160481e038020182106809a0581207a20038020182106809a182580481e034020182106809a0f2580481e034020182106809a002580481e0340201821068099058120780e950020182106809a058120780d610020182106809a058120780d00a500182106809a058120780e005740182106809a054125901e100020142106809a0e0160481e460020142106809a000160481e46002014210680990581207840460020142106809a000151201e0380201421068099520160481e038020142106809a0544807840038020142106809a0541207840038020142106809a058120795c038020142106809a9303c0481e034020142106809a0f0160481e034020142106809a058120780e480020142106809a440380481e038010142106809a0e0160481e038010142106809aa0c120780d2e0020182106a7baa0c12078b4038010182106a7ba0481e034d0008740182106a7baa0c1207840038020142106a7ba0481e03638008050881a02a7ba0481e034b8340060841a02a7ba0481e034a0008060841a02a7ba0481e8f0b4004060841a02a7ba0481e2400e004060841a02a7ba04a6f07a3c038050841a02a7ba0481e1000e340050841a02a7ba0481e9f00e008050841a02a7ba04a6b078d0008050841a02a7ba04a6f0780d170060881a0267ba04a6f07a44038050881a0267ba0481e1000e4c0050881a0267ba0481e4b00e008050881a0267ba04a6b07930008050881a0267ba000129ce6f0780d0841a0267b904a7307840038020841a0267ba000129ce6b078010841a0267b904a6f078b4038060841a0267ba0481e100b4008060841a0267ba0481e4200e008060841a0267ba04a6b078b8008060841a0267ba000129be6b078050841a0267b9058129cc1e034020841a02648a180120780d008060841a02648a058129ac1e008050841a02648a930120780d008050841a02648a05a770481e038010141a0250ca4a0120780e004050881a0250ca058129cc1e038010841a0250ca058129bc1e038050841a0250ca0581207840008050841a0250ca440120780e004050841a0250ca058120780e004050881a02640a058120780e004060841a024fca058129ac1e004050841a028d4a0e0120780e004050841a028d4a058123700d004050841a028d4a390120780d004050841a028d4a058120780d004060841a02870a
  | 11, 3 => 0x960120780d008060841a0264160481e4600201421068099054480780e008050841a0264129ce6f0780d0841a0267b904a739ac1e00421068099ee4129be6b078050841a0267b9
  | 12, 0 => 0x150481e9100e2e0020182206809b05412078b403930008060881a026c150481e1000e0085c0182206809b4a0160481e1000e008050881a026c3c0581207a44038020142206809b0e0160481e03930008050881a026c600581207840038020182106809b000600f0120780d008060841a026800290160481e034020182106809a29060058120780d008060841a026c38058120780e2e0020182106809b290160481e034b8008060841a026c00250160481e038010182106809a250160481e2d00e004060841a026c000e0160481e100020142106809a00114058120780e008050841a0269140e0160481e038020142106809b4503c058120780e008050841a026d140581207840038020142106809b0f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 1 => 0x541207a44038b8008060881a026c150481e2d00e4c0020182206809b054120784003802170060881a026d280581207840038020142206809b0f0160481e9100e008050881a026c38058120780e4c0020142206809b180160481e1000e008060841a026c001803c0481e034020182106809a000a4058120780d008060841a0268a4180160481e034020182106809b0e0160481e038b8008060841a026ca4058120780d2e0020182106809b00094058120780e004060841a02689405812078b4038010182106809b000380581207840008050841a026800450160481e038020142106809a45038058120780e008050841a026d140f0160481e038020142106809b450160481e1000e008050841a026c00002830481e034010142106a7b9000120780d34002014210680a9ee8000481e8f00e004050841a02a7ba000120780d4c00201422068099ee8000481e034b8008060841a0267ba00012078b40380101821068099ee800000129bc1e034050841a0267b900012078400380201421068099ee800000129ac1e004050841a0267b90f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 2 => 0x541207a44038b8008060881a026c150481e2d00e4c0020182206809b054120784003802170060881a026d280581207840038020142206809b0f0160481e9100e008050881a026c38058120780e4c0020142206809b180160481e1000e008060841a026c001803c0481e034020182106809a000a4058120780d008060841a0268a4180160481e034020182106809b0e0160481e038b8008060841a026ca4058120780d2e0020182106809b00094058120780e004060841a02689405812078b4038010182106809b000380581207840008050841a026800450160481e038020142106809a45038058120780e008050841a026d140f0160481e038020142106809b450160481e1000e008050841a026c00002830481e034010142106a7b9000120780d34002014210680a9ee8000481e8f00e004050841a02a7ba000120780d4c00201422068099ee8000481e034b8008060841a0267ba00012078b40380101821068099ee800000129bc1e034050841a0267b900012078400380201421068099ee800000129ac1e004050841a0267b90f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 3 => 0x1803c0481e034020182106809a290160481e034020182106809a250160481e038010182106809a0e0160481e100020142106809a450160481e038020142106809a002830481e034010142106a7b90481e034d0008050841a02a7ba0481e8f00e004050841a02a7ba0481e03530008050881a0267ba0481e034b8008060841a0267ba0481e2d00e004060841a0267ba000129bc1e034050841a0267b90481e1000e008050841a0267ba000129ac1e004050841a0267b9058120780d008050841a02648a058120780e004050841a0250ca058120780d004050841a028d4a
  | 12, 4 => 0x2830481e034010142106a7b904a6f0780d01421068099ee4129ac1e004050841a0267b9
  | 13, 0 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a
  | 13, 1 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 2 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 3 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 4 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 5 => 0x120780d004050841a0267b9
  | _, _ => 0
def tableData : Nat → Nat → Nat
  | 9, 0 => 0xa0940000b100004200009a00004936ab18308d00880000002b000d1e0c0055243d072a0000009f007900192587061f316d937e12611301998e00725b664e
  | 10, 0 => 0xde1f79e356d990d750000000000000000000000000000000000000000000000000000000000000f850000000a9e4d0003cd2920000000000000007433310d91b1000000a15f93000000d2d000000000f3050619900043f000000000000000000f61000000ae1aca00027100000000000000033d0000001459be457eca000b278b7558f92c5c6ebaa57db2dd6c10008a2000000516000d995f0901ccd4cb22922b000000000000000000000000000000000e86829c88e6ee059d6fc166e0000006bb3d9c26a5bec589e240000691000000000000000000aff000d39667000f880001c9000000000e580007ea96b00001900052d841000000c83000b4d33a32bf19d15000fa23855469a46aa0005240006d7704000617000a210008e4dce000000000e56000000a9f000000abe2f2000000000a4f8350004e12883087709fdeba1390000000003791f99b2f31d8b00068b00000000000062c2ad0790000008f5a61d611810000004b00002954220000000000006a3b33b8900000036100054df4a6f88aae6520541672140900000000000000000000081db06e10211955c1958ff7767a000b29e7d049f91000000000000000000000000000c9d000000000af700000000054ec6700085300000000000018d9b0000000593000000f9f0006da000e41000f9e00000000060d000000000d818e900000000021d6e300000000000000039d00031f000f2200000083b0000000000006a92ce98c34f00000000015d000fcd4bcf3fcf1000000000f9d000000b9d7bdabb0000000000007edb7d7f6560241ab1000000e4b235000f18ca9f0055700000027000059c0000000000005cc0000000000000fdcce53f0000002c2000a37000000000000000000000b8ad5a0008a19800006cd00000000000000003d8196e58c512d30d0f11159755d1c9bf67515bc5692025f0ae9e589de63a9679f23d7500000000027d00000069b000000000000ded000000294d14dda00074b355f16df8bf50000000000008c2000000618e59cfdfe7000000518000db1000000885ed1267000b5700000000000077c000000000000000000000e4e000000000a6e64f5450003910008b54986389b5175f589311d58790cd50f34974f00afa436dd458050000000000000003b5b7e535e890000000000c12f593db1b000000000000577ea1b110000007818ad548000000000000dc93d309dbdd28b715a6c061a97fbf000d92000fa00000000002d1ac9d090000000000000000000000000007dc000000000737000d38edda81ef73c19bcb71000fad7d2594a75bc6000000000000000000000000000000000000000000bf3c770009193e50005fc4787ff000000000000e330001690004a4000000000000000655a5d7a6bad23e78df6dfa99e2e71151dbdfaa00024d000000a43000a51000d3d505000a3900000000000000000076400000000000006d000eb9e280000000005e40005b91ed9cad550000000004ed30754060e2374bf000000f24000000000000abd00000000094a0000000000009f1000f44000f73000000000286571460c6d0000000000004e7b35fb566dce51e1bdb121000000000000000000758000000aeb0000000000000000000000000000000004db9e5000892620665f6b00000000009100000000027fb053f10e5000000000e11697f0f5170000008d1000000000fe11bdad5cbcb59000000000799584e950006e486d000000000f25000000000000000b41000000055c36000cf20000000000000005a8a7351058a00000000000056cd6ecc2b65c0de57f1b343689000000bd10000000000000000004840007090006df000e2937fd7a5473160005b4000000a2b000000000ba1000fd90b5000998000207000000ff3031000df9000a8d000259000500dd5d8d265e1dcd9000000e7a738000000000000000000744c41000949000000a0900000000000000f000109c49000000eeb53600060800000000000000044bbb97b169cc01000000000000000000000000000da5d2181ee1c886d4ecc846c8cf21f000b3f3fd6af85926e000000643fab289d5d925eb600000042e1a5000000000000ee0000085000000000000d69f8600000000000032c0002a10000000004d5d5100000071c
  | 10, 1 => 0x377534900000089002400000000190022000000000000000d0f000000002a0000002b7d00000000478e00006d2c003d005f0000001b0000553b316129000001
  | 11, 0 => 0x62f48da470be8b4bad8ec99a07a2032967f7282a6934200088d0000000000000004a2bd11f309700000088904b1e1a000007de0009ecaed00030e6bf8950000000000000005597e18b100000021825e26a0000000000882d1542a6d3fd0000005110000000000008e9000a2e0cd58912d90520c422679052000000000b157396559fe0006be8b800000051d3d288835a241000000b8b00000000000000000009d000000000000000b47baa000ad59910000000000000002ad000000000246ba17bb4ba28e07834e4ed00000007907319f00000000000061cb2f3ed0000009b68860007150000004be54a2b94e148107bb210000006360000000008dbbaf3910007240000002dd33106a0aebae42100000060345da507bd00000066b24d989786000000000000aa581d0000fa2f9862000949b05229aa10000000603de000336000000ae16538a10000008eb0000635d172b0001b10000004094c6000439b5761e0000006b50000007d3000000000000000000000a460000008bd0a3000000871000031000000000000726a3991a9165a933d7eb0000002c5a09ab14758d13670003b57f90005cc1a50009e02ba77a14500000000000093100000093d0930004695d20006e565f2590000009039900001d00006f1b841ff00000087f60d00020500000000900022c6340000009145b9bab0009115dd1dc00000000000000000000000000000000000000000000069d49a7849879ff16300000064e1694d52350b55b506700000000000000000000000000000000000027100000000083534900000000079206d4c9049000661000000ac83799ad0ee000000000a51a4a0baba5000000000980000000000000000000000000000015000000000000000b888117ea4511ab98c00000079e02da0db3d5c5913325995a15a0aa3a5e93590002be0000000000000000001ed18d0000000000002db00000039d0009a831fb8a5e65cb000b410006490000000000002a200000000000000000068e1f722a000a28000000b4d00026500035c0000003020210b266d971abf55f0000000008af7a227d8600000006230001bd00000041500000000064c87d0000006cd000000000000000000a7d00000015d0007ae0000000000000009fd13f0007900002ed0000000000002a60000000572d60007ed2cab99a5db7f0000000003c17dcb8f0000000000000000000000001e700000000095e89e0000000003cd0003660000000000009f64990917699d1b4999f00000000005e82b577211000000000000000ba21d553521e086289000845bc9000309b7d0000000007c400000000011c00000052958f982000000000000157a950008f70000006d90001753714b1a229f89dd86912806c5657a5a1299d08598e07688b95400029a54ebb90002e20000000000000000000000000000000000000873855950000000000000000000000000009853d91ea000054000583000000000000a89000000929b7100006f000000445000000000899000000000a370005f59e600000000054174f00080e0002e95a71811f90000000000000000000009d94bd76296a000000000b0b0005de00000000000063d737a1003da43182bc52e7935000000000a4e2a1000affb59b95976000b2d0005a17c900042e0003f1000000000000000b860002207f40000009a435b000000000b8d000000000a1600000000000000000000000000000000009f709151851000000000110000000000ac300014b9a65b30000000000007564f92c630100000000069ba1307c8dd2f51040a900057d1330006010c18f500000000000000000094b0000000000006c100068f000000ae795685d00000000086e5ad8c92950000000000000000000339e3bba50618e0000000001c90000008aa000000000abd0006b20617b80000000000550007d5000000000000000962000000a450000000000008b631521d3193658adbbb3a92b27368d578d00000076e000000000000000000000252000276707ac930d9594a6b65000a40000000000000000000a54000000000000ac60000009c500052a00036890180500097986c8290009749e20d9b898a85ef452000000000961000000000000000000000199952000af9000000000139
  | 11, 1 => 0xa832b90af998a996fd0b60000000009e200094729a5be98900000025e00000000000020b0c700000098506f1f9a3048d92e5710000008574450000000000000000000000009310009950002290000000000000002e954175e0005290000000000004ed0003d7186139a5e09d9ad0e57812188414150760005430005d58290008a100085699c5e2a2e73967228e39a24d0000009b70002d20000000005370000000000003e77f33b200012d1929d93a4a960000002ad00000000007fa8d4cb33190b2520845ca0ab72d1b70b55334f100000000064368d38542d0000009fe40b00087d51d00070a7662c50006f10b75ed000721000000000499000a9b62500088c0004fd3665ad0000d2000a9a0002d67fb6cda8c90d0002654508d69d183f00000000000003d00000000000000038d00000059503900000000067e0005b200055b1754938270000000005110007c98930001d50000006a971200000081b18d00000084d00000092300049f000000000000000a820000000000000000000000000550003f500034988ea690004397a100093b5b9000061a394726e53915fb0006550000007c42c6a281f31c98ca3de0000000000000000001ca3560c36d92e27ca8338719ab5395104382209d80000000000000009a40000000b4805000211000000000000000000000000a977d57b10004790001e80000000000000000000000000000000000000000000000000008d4a2f4fe1639cf0004211990008220007ad24100054d0b200004b4510000000000000000002710009790000855c50009f530d8e207971506d3dd8353fd3cb09c4c860d000106000000000a86000a910000000000000000000000000002d10004440000150000004d600056e9a89610006c100093a1be9d43257bda3d69936d50e8ee9dda45a3a5a17e15e1a6a2ca00000000000008e0002051a50000000002f348c00058f6313f19f03a39b67de7c30007ed81d2834c90000000002a200042000000000020f000000000000a5853833d8110003790005e40000003020000d60930000000000003b399350f0002958f20000000000000000000006b50005590008200000005050000000000000002dd00000900000015d0008fe000000000000000a2d1573118e02f90000000000000002a60000000002ee00093d4b3a7900099f00014b9bb92c6613ca33a00000000045d00028f32b1ff18700000000000000000066d16f4e35fa0000000000000000000c18b9a197f59e700000000000096f0a908b0000000004ab000a8e1e13bf00075123634a0004d532c30999d4ea09f53591400000000000000048174578700000000000000000002d0000000000008650000003a6000605000a25a5212827d8f59d6000a422de9e598708250200000000076a000000aa500000000000000000039b00000000000000061978d0000000000000000000000000000006799cd00007820277b0000003520000213ff00000094900007b00000000000000000000036a000000a671f631200000047e75d0008b700095e31a2f500079f000000000000000000709049a213c10009ca00000000059b1ed3817d60005560004b589fa40ab1000000a730002890000000002a1a8a583565314a7551a21d6410009197990000004e569d0000009a65320000000002389440000a39ec5e300046f1459b93d90a8000a460000000003e50000000000000000000000000003190002be00000011c4be0000000974ae0009ee7ab00000000000000000000030100000033e22ca430b80004091100cd0a677513f0000000007f90000000000000000000000001930000008590000000004bd00017b0000003550000007a509045c00048239d000000000057a2baa60000000001a60003cd3653610000000000000000000913329080000000000000009250000000003890009c2000000a810000004e100099a5899912355f989eaa76492b216948a8dd0000008be00000000000000000054f26a5132763d60000d9000000abd181a700000000000000004b10000000003b53e209a000000a0d0007469a94c65fc95500000000096d00051f087a2a9b50f17e76c20000002829c12590000004e00000000000001b135e57d4a51bd313151
  | 11, 2 => 0x34c000000000000003b52d400001ed000000037700000918000000028800000000000000000000000000000000d60d1814005d400000000000000000003610036d003ad00000000000005b7554200000000006340037d4f6f473000001c83d19f3d0c6b96ce6a001d7002510000000000003210000000000af8000002b000006ac00308000000072c0000000c7ce0398000cdba72534000000000000000000000000000000000000000000000001c1d2400001369d521a9ecd000002a40000000000000000000000bd40097400c0400f059900000ede8900000001028d40000000003b60000031add000000000000180000000000000000000ee00000000004a779000000000000000000008e906001ef000d2238000000000000000000000000000b44000000000000000000000d4e40067c00000000000047485001ea0000000000064000016100000000e500241dae177e4d4ea400246a5000009aead6d4000000000000000005588b00374000370000000000155510f2e90039e3c80000000251cd00000000000000000000c94ba000000000000000000006b800c4c0000000000000000000000000000000000000000500003a00000000000000000000000005a4000000000000c5400784000000f60400000003c4000030d0c18c003914b425000cdd6800f08000014550d554067d3f400000000000000000000000000000000000000000000000304000240000202495b1003850021ddaa69000d91ebc318509d5400000000039d002290000078c0000000538000b800cc4001b4000000000000a5400002234cc005755a003192bc0000000000009b00000000000000000009c000000073000454ae0009d000000000000000000003ea111e40069400
  | 11, 3 => 0xe0000100140003a00031420000800a4c80000068000f40000c00000
  | 12, 0 => 0x728000000578000000001dc00785680000000000122d960a84006e001fc00aa4300000008000000cd00065e27962b24f400002104a0000001ac4954b497a001e841c60000001ec000000000000000214d591458000018c25d20000000a85a2980000002a8000000003f49400000000083003840000391b40000003f80000000000873001840000000000000000013c67
  | 12, 1 => 0xa8800007a8da14000071a6800e48c8000000a2bf65a910043400da758000116790000000b6002727d0cd766ae54e4c5cc00781584a004bad6851594cf800101e9e69e00000000162000000000370028376c7608a031ba956aa004e97d80bf630014c60608000000005a56c0077800006da6b7800892f3655000005a9040032aa408df5133400000000000612480214d3
  | 12, 2 => 0xa8800007a8da14000071a6800e48c8000000a2bf65a910043400da758000116790000000b6002727d0cd766ae54e4c5cc00781584a004bad6851594cf800101e9e69e00000000162000000000370028376c7608a031ba956aa004e97d80bf630014c60608000000005a56c0077800006da6b7800892f3655000005a9040032aa408df5133400000000000612480214d3
  | 12, 3 => 0xc63c000000009d0000250000000000009600970049bd84552c7e0000000000000000a30000000076000000000000410078005e009b00823200000000a80000009e0000000031006d91c1793b4aca00a70d9200007300000000b500003a00000000616556853d000000000400009c0000000000c900a900001959b9000000
  | 12, 4 => 0x19000211341
  | 13, 0 => 0x800c001b0402000000046400003c04dd18000001500d391
  | 13, 1 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 2 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 3 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 4 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 5 => 0x24103750
  | _, _ => 0
def tableDisplacements : Nat → Nat → Nat
  | 9, 0 => 0x3420400c3000000000141000081003080000000002000000
  | 10, 0 => 0x1000070000000000000000040000002000000040000802000000040003c0000800000000000100000000000000000001000030080000000008010000000006000000000000c0000000000000000000000000000000000000000020000000001000000040000800000000000000001000010000200000000020080000000000090040700005000000000400000000000000000001000000000000000000000000000000004000000000000000000040e00c01000000040000400000000000000800000000100000c040080001c000000000c0000c0001400000000040000004000010040200800000000080000001004000000000000000000040001000008000000000000000000000000000000000000000000000000000000000000010080000000000000000000000000000000000000000000000600000000000000000004000000000000000008000000000003000000000000c00000000000000000000000080000000000000000000001000000000000c0000c00000000080000000000000000000000000000000000000000000080000000000010000000401000000000001000000000000000000000000040300000000000040000c010000000400000000000000001000000000100000000000000300001000000000100000000050040000000000000000000c00000000000000402000000040200403000000000000001000000000000400000000000000000000000000000c010000000c00000010000200001004000000000003004000000100000000000000000001008000080000000000000080100000000000000000000000000040000400004000000000c000000000800000000040000000000000000100000004000000000000
  | 10, 1 => 0x40000000000000000000000000000000000000000
  | 11, 0 => 0x2c00000000040000400000000040000406000020080200000004000000000000000010000000c00000000000000000000000000000401000040000000000004010080000801008000000000401000010000001405000010000000402000000000000007000000040001400008000000000000000000000100004000000000000c00000000080100000000000040200000000000040200000004000000000400000010000000c000000000000004000000000000000000000300000010000000000405000010000000000000020000100001004000000000000004000000002002000000040000002000020080000c000080000400000000000000800004000000000400000000000000402000010040000000000000000000003000010000000000000000000200000000000000000004000000000000001000000000000001000000000700000000000000000400000000040000000008030000000000000000000000800000050040100003000000000000000000000000000000000000040000000000000080000000000000000000c0100001000000000300000008000000000c00004000000000000000000000000000000000000300000000000000000001000010000000000008000000000000000000000000000000000000000000000000000000000000000040000000000050000000000000020000000800000000000000800000000000100000000000000000000000000000000000000010000100000000000000000000000000000100000000000040000000000000000300001000000040000000000020000000000000000000000000000000040000000004000000000c0000000000000000400000000000000000000000010000000000
  | 11, 1 => 0x1400010000040400400000000040200c0900400004000000600c0000000004000080000000000000000000001030000000000000004000000000000004000000000400000000000c00003010000000000000000000000000000018000000000000000030000000000014000000000000000000000000001000020000100000000000040000001004000000100000000000000100800000000000000000008000000100400000000000000000000000040000001000000000100000010010000000000000000000001000000010000100001000000000000000000000000702c0100000004010000300002004000000100000000000100000000008000000000000008000000000000014000000100000000000000000000000000000000003008030000000002000000000001000000000000000400000000000000001000000000000004000000000000801000000000000001000000000000000000000000000000010000000000401000000000000000000010000000800000000000000000000000000000800000000000000400008000000000000000000000100000000000000000000000000000000000004000000000000000030000000000000000040100000000000000000000000010000000000000000000000000008000000000000000000040000000000000000000001004000000000c0000000008000000000c000000000000000000000000000000000000200000000000000000003000010000000000000000000001c00000030000000000000000000000000000010040100000000000000000001000000000001000000000080100000004000000200000000000000000000000000100600001000000080000001000000000000000
  | 11, 2 => 0x40000000000001000000000000000001000000003000000000000000200010000000000000000000000000010000000000040003010040000000000200000000000000000000000000000000000000000000000000000000000000000000040800008000000008000000000000204000000600000000000000000001000000000008000001000000002000000200000000000000000002000000000000000000000000000000000000000040000000000000000040000008000000000040000000000000000000000000000000000000000018000200000000000010000000000000000000000000000000000008000000008000000000000000000000000000000000000000000000000000000000000008000000000040000000000000
  | 11, 3 => 0x0
  | 12, 0 => 0x8000000000004100020000100001000000000020000200000000000000000008002000000000002000008000000000000000
  | 12, 1 => 0x40000608080000000006001000800082020c1810000000000000300000000000000000418000000000004002000008100001020000000
  | 12, 2 => 0x40000608080000000006001000800082020c1810000000000000300000000000000000418000000000004002000008100001020000000
  | 12, 3 => 0xc000040000002000000200000040000300000000000000000000002000000000000000000000000000000000000000000000000000000
  | 12, 4 => 0x8
  | 13, 0 => 0x8402000000000000000
  | 13, 1 => 0x801014010000010000
  | 13, 2 => 0x801014010000010000
  | 13, 3 => 0x801014010000010000
  | 13, 4 => 0x801014010000010000
  | 13, 5 => 0x880
  | _, _ => 0
def tableBuckets : Nat → Nat → Nat
  | 9, 0 => 32
  | 10, 0 => 512
  | 10, 1 => 32
  | 11, 0 => 512
  | 11, 1 => 512
  | 11, 2 => 256
  | 11, 3 => 16
  | 12, 0 => 64
  | 12, 1 => 64
  | 12, 2 => 64
  | 12, 3 => 64
  | 12, 4 => 4
  | 13, 0 => 16
  | 13, 1 => 16
  | 13, 2 => 16
  | 13, 3 => 16
  | 13, 4 => 16
  | 13, 5 => 4
  | _, _ => 1
def tableMultiplier : Nat → Nat → Nat
  | 9, 0 => 1000
  | 10, 0 => 1000
  | 10, 1 => 1000
  | 11, 0 => 1000
  | 11, 1 => 1000
  | 11, 2 => 1000
  | 11, 3 => 1000
  | 12, 0 => 1001
  | 12, 1 => 1001
  | 12, 2 => 1001
  | 12, 3 => 1000
  | 12, 4 => 1002
  | 13, 0 => 1000
  | 13, 1 => 1000
  | 13, 2 => 1000
  | 13, 3 => 1000
  | 13, 4 => 1000
  | 13, 5 => 1000
  | _, _ => 1
def tableSalt (_ _ : Nat) : Nat := 0
def tableBits : Nat → Nat → Nat × Nat
  | 9, 0 => (6, 8)
  | 10, 0 => (10, 12)
  | 10, 1 => (6, 8)
  | 11, 0 => (10, 12)
  | 11, 1 => (10, 12)
  | 11, 2 => (9, 10)
  | 11, 3 => (5, 7)
  | 12, 0 => (7, 9)
  | 12, 1 => (7, 9)
  | 12, 2 => (7, 9)
  | 12, 3 => (7, 8)
  | 12, 4 => (3, 6)
  | 13, 0 => (5, 6)
  | 13, 1 => (5, 6)
  | 13, 2 => (5, 6)
  | 13, 3 => (5, 6)
  | 13, 4 => (5, 6)
  | 13, 5 => (3, 4)
  | _, _ => (1, 1)
def sample (s : Bool) (i : Fin 414) (j : Fin 9) : Bool :=
  bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
set_option maxRecDepth 20000 in
lemma sample_ok : ∀ (s : Bool) (i : Fin 414), edgeF (sample s i) = s := by decide +kernel
lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := rfl
lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by
      rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]
lemma raw_lt : raw.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true := by decide +kernel
lemma raw_valid : ∀ a ∈ raw, Valid a := by
  intro a ha
  have h := of_decide_eq_true (List.all_eq_true.mp raw_lt a ha)
  exact ⟨valid1_of_le_top h.1, valid1_of_le_top h.2⟩
lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel
lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi, decide_true]
      obtain ⟨b, hb, h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b, hm, sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi, decide_false]
      exact valid_unionSep (fun x hx => raw_valid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates raw raw_valid
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ raw_valid (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list, sample_ok] at eq
    exact eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)
lemma wire9_sig (g0 : Gate) (gs : List Gate)
    (hg0 : g0.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hw9 : ∀ y : Fin 9 → Bool,
      ((Circuit.mk (g0 :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) :
    gv raw g0 = bin false raw4 raw6 := by
  have hv : Valid (gv raw g0) := gv_valid raw_valid g0
  have hv46 : Valid (bin false raw4 raw6) :=
    valid_bin (raw_valid raw4 (by simp [raw])) (raw_valid raw6 (by simp [raw]))
  have hbit (s : Bool) (i : Fin 414) : bit s i (gv raw g0) = bit s i (bin false raw4 raw6) := by
    have h1 := hw9 (sample s i)
    simp only [Circuit.wires, List.foldl_cons] at h1
    have hlen : (List.ofFn (sample s i)).length = 9 := by simp
    have hlt : 9 < (List.ofFn (sample s i) ++ [g0.op.eval (g0.inputs.map fun j =>
        (List.ofFn (sample s i)).getD j false)]).length := by simp
    rw [foldl_append_getD _ gs _ 9 hlt false] at h1
    have hget : (List.ofFn (sample s i) ++ [g0.op.eval (g0.inputs.map fun j =>
        (List.ofFn (sample s i)).getD j false)]).getD 9 false =
        g0.op.eval (g0.inputs.map fun j => (List.ofFn (sample s i)).getD j false) := by
      simp [List.getD_eq_getElem?_getD]
    rw [hget, sample_list] at h1
    rw [run_bit s i g0 raw raw_valid hg0, h1, bit_bin]
    rfl
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 414
    · simpa [bit] using hbit true ⟨i, hi⟩
    · rw [hv.1 i (by omega), hv46.1 i (by omega)]
  · apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 414
    · simpa [bit] using hbit false ⟨i, hi⟩
    · rw [hv.2 i (by omega), hv46.2 i (by omega)]
def index9 (key : Nat) (j : Nat) : Nat := (key >>> (9 * j)) &&& 511
def reindexLoop (f : Fin 414 → Fin 414) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 414 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 414 → Fin 414) (x : Nat) : Nat := reindexLoop f x 414
lemma reindexLoop_testBit (f : Fin 414 → Fin 414) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 414 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 414
    · simp only [hn, dite_true]
      by_cases hx : x.testBit (f ⟨n, hn⟩).val = true
      · simp only [hx, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
        by_cases hj : j = n
        · subst j; simp [hn, hx]
        · have h1 : ¬ (j ≥ n ∧ (1 : Nat).testBit (j - n) = true) := by
            intro ⟨hge, htb⟩
            have hpos : 1 ≤ j - n := by omega
            have hlt2 : 1 < 2 ^ (j - n) := by
              have h2 : 2 ^ 1 ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by omega) hpos
              omega
            rw [Nat.testBit_lt_two_pow hlt2] at htb; contradiction
          have hbit : (decide (n ≤ j) && (1 : Nat).testBit (j - n)) = false := by
            cases hle : decide (n ≤ j)
            · rfl
            · cases ht : (1 : Nat).testBit (j - n)
              · rfl
              · exact (h1 ⟨of_decide_eq_true hle, ht⟩).elim
          rw [hbit, Bool.or_false]
          by_cases hlt : j < n
          · have hlt' : j < n + 1 := by omega
            have hj414 : j < 414 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 414 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 414
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
lemma reindex_testBit (f : Fin 414 → Fin 414) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 414 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 414 j
lemma reindex_valid1 (f : Fin 414 → Fin 414) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 414 by omega]
lemma reindex_and (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_and]
lemma reindex_or (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_or]
lemma reindex_bnot (f : Fin 414 → Fin 414) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_zero (f : Fin 414 → Fin 414) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
lemma reindex_top (f : Fin 414 → Fin 414) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 414
  · simp [hj, testBit_top, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_comp (f g : Fin 414 → Fin 414) (x : Nat) :
    reindex f (reindex g x) = reindex (fun j => g (f j)) x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, reindex_testBit, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_id {x : Nat} (hx : Valid1 x) : reindex (fun j => j) x = x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
structure SigHom where
  fn : Sig → Sig
  valid : ∀ a, Valid (fn a)
  hneg : ∀ {a}, Valid a → fn (neg a) = neg (fn a)
  hbin : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)
  hzero : fn zero = zero
  hone : fn one = one
  htarget : fn target = target
def pairHom (fp fn : Fin 414 → Fin 414) : SigHom where
  fn a := (reindex fp a.1, reindex fn a.2)
  valid a := ⟨reindex_valid1 fp a.1, reindex_valid1 fn a.2⟩
  hneg ha := Prod.ext (reindex_bnot fp ha.1) (reindex_bnot fn ha.2)
  hbin d a b := by cases d <;> simp [bin, reindex_and, reindex_or]
  hzero := Prod.ext (reindex_zero fp) (reindex_zero fn)
  hone := Prod.ext (reindex_top fp) (reindex_top fn)
  htarget := Prod.ext (reindex_top fp) (reindex_zero fn)
def compHom (h1 h2 : SigHom) : SigHom where
  fn a := h1.fn (h2.fn a)
  valid a := h1.valid (h2.fn a)
  hneg ha := by rw [h2.hneg ha, h1.hneg (h2.valid _)]
  hbin d a b := by rw [h2.hbin, h1.hbin]
  hzero := by rw [h2.hzero, h1.hzero]
  hone := by rw [h2.hone, h1.hone]
  htarget := by rw [h2.htarget, h1.htarget]
def sym1 (j : Fin 414) : Fin 414 := Fin.ofNat 414 (index9 symKey1 j.val)
def sym2 (j : Fin 414) : Fin 414 := Fin.ofNat 414 (index9 symKey2 j.val)
set_option maxRecDepth 20000 in
lemma sym1_invol : ∀ j : Fin 414, sym1 (sym1 j) = j := by decide +kernel
set_option maxRecDepth 20000 in
lemma sym2_invol : ∀ j : Fin 414, sym2 (sym2 j) = j := by decide +kernel
set_option maxRecDepth 20000 in
lemma sym11_eq : ∀ j : Fin 414,
    sym1 (sym2 (sym1 (sym2 (sym1 (sym2 j))))) = sym2 (sym1 (sym2 (sym1 (sym2 (sym1 j))))) := by
  decide +kernel
def hom1 : SigHom := pairHom sym1 sym1
def hom2 : SigHom := pairHom sym2 sym2
abbrev action1 (a : Sig) : Sig := hom1.fn a
abbrev action2 (a : Sig) : Sig := hom2.fn a
lemma action1_invol {a : Sig} (ha : Valid a) : action1 (action1 a) = a := by
  apply Prod.ext <;> dsimp [action1, hom1, pairHom] <;> rw [reindex_comp] <;>
    simpa [sym1_invol] using reindex_id (by first | exact ha.1 | exact ha.2)
lemma action2_invol {a : Sig} (ha : Valid a) : action2 (action2 a) = a := by
  apply Prod.ext <;> dsimp [action2, hom2, pairHom] <;> rw [reindex_comp] <;>
    simpa [sym2_invol] using reindex_id (by first | exact ha.1 | exact ha.2)
lemma action11_swap (a : Sig) :
    action1 (action2 (action1 (action2 (action1 (action2 a))))) =
    action2 (action1 (action2 (action1 (action2 (action1 a))))) := by
  apply Prod.ext <;> dsimp [action1, action2, hom1, hom2, pairHom] <;>
    simp only [reindex_comp] <;>
    exact congrArg (fun f => reindex f _) (funext fun j => (sym11_eq j).symm)
def homG (g : Fin 12) : SigHom :=
  match g.val with
  | 0 => pairHom id id
  | 1 => hom1
  | 2 => hom2
  | 3 => compHom hom1 hom2
  | 4 => compHom hom2 hom1
  | 5 => compHom hom1 (compHom hom2 hom1)
  | 6 => compHom hom2 (compHom hom1 hom2)
  | 7 => compHom hom1 (compHom hom2 (compHom hom1 hom2))
  | 8 => compHom hom2 (compHom hom1 (compHom hom2 hom1))
  | 9 => compHom hom1 (compHom hom2 (compHom hom1 (compHom hom2 hom1)))
  | 10 => compHom hom2 (compHom hom1 (compHom hom2 (compHom hom1 hom2)))
  | _ => compHom hom1 (compHom hom2 (compHom hom1 (compHom hom2 (compHom hom1 hom2))))
abbrev action (g : Fin 12) (a : Sig) : Sig := (homG g).fn a
def invG (g : Fin 12) : Fin 12 :=
  ![0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 11] g
lemma action0_eq {a : Sig} (ha : Valid a) : action 0 a = a :=
  Prod.ext (reindex_id ha.1) (reindex_id ha.2)
lemma action_valid (g : Fin 12) (a : Sig) : Valid (action g a) := (homG g).valid a
lemma action_neg (g : Fin 12) {a : Sig} (ha : Valid a) : action g (neg a) = neg (action g a) :=
  (homG g).hneg ha
lemma action_bin (g : Fin 12) (d : Bool) (a b : Sig) :
    action g (bin d a b) = bin d (action g a) (action g b) := (homG g).hbin d a b
lemma action_zero (g : Fin 12) : action g zero = zero := (homG g).hzero
lemma action_one (g : Fin 12) : action g one = one := (homG g).hone
lemma action_target (g : Fin 12) : action g target = target := (homG g).htarget
lemma action_inv (g : Fin 12) {a : Sig} (ha : Valid a) :
    action (invG g) (action g a) = a := by
  fin_cases g
  · exact (action0_eq (action_valid 0 a)).trans (action0_eq ha)
  · exact action1_invol ha
  · exact action2_invol ha
  · change action2 (action1 (action1 (action2 a))) = a
    rw [action1_invol (hom2.valid a), action2_invol ha]
  · change action1 (action2 (action2 (action1 a))) = a
    rw [action2_invol (hom1.valid a), action1_invol ha]
  · change action1 (action2 (action1 (action1 (action2 (action1 a))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _), action1_invol ha]
  · change action2 (action1 (action2 (action2 (action1 (action2 a))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _), action2_invol ha]
  · change action2 (action1 (action2 (action1 (action1 (action2 (action1 (action2 a))))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol ha]
  · change action1 (action2 (action1 (action2 (action2 (action1 (action2 (action1 a))))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _),
        action2_invol (hom1.valid _), action1_invol ha]
  · change action1 (action2 (action1 (action2 (action1 (action1 (action2 (action1 (action2 (action1 a))))))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol (hom1.valid _), action1_invol ha]
  · change action2 (action1 (action2 (action1 (action2 (action2 (action1 (action2 (action1 (action2 a))))))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _),
        action2_invol (hom1.valid _), action1_invol (hom2.valid _), action2_invol ha]
  · change action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 a))))))))))) = a
    rw [action11_swap]
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol ha]
lemma invG_inv (g : Fin 12) : invG (invG g) = g := by fin_cases g <;> rfl
lemma action_inj {g : Fin 12} {a b : Sig} (ha : Valid a) (hb : Valid b)
    (he : action g a = action g b) : a = b := by
  have := congrArg (action (invG g)) he
  rwa [action_inv g ha, action_inv g hb] at this
lemma action_proper (g : Fin 12) {a : Sig} (ha : proper a) : proper (action g a) := by
  refine ⟨action_valid g a, ?_, ?_⟩
  · intro h0; exact ha.2.1 (action_inj ha.1 valid_zero (h0.trans (action_zero g).symm))
  · intro h1; exact ha.2.2 (action_inj ha.1 valid_one (h1.trans (action_one g).symm))
def rawImage (g : Fin 12) (i : Fin 9) : Sig :=
  raw.getD ((rawPermCodes g >>> (4 * i.val)) &&& 15) zero
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma raw1_eq : ∀ i : Fin 9, raw.getD (perm1 i) zero = action1 (raw.getD i.val zero) := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma raw2_eq : ∀ i : Fin 9, raw.getD (perm2 i) zero = action2 (raw.getD i.val zero) := by
  decide +kernel
def p1 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (perm1 i)
def p2 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (perm2 i)
lemma rawImage_eq (g : Fin 12) (i : Fin 9) : rawImage g i = action g (raw.getD i.val zero) := by
  have h1 : ∀ j : Fin 9, hom1.fn (raw.getD j.val zero) = raw.getD (p1 j).val zero := fun j =>
    (raw1_eq j).symm.trans (by fin_cases j <;> rfl)
  have h2 : ∀ j : Fin 9, hom2.fn (raw.getD j.val zero) = raw.getD (p2 j).val zero := fun j =>
    (raw2_eq j).symm.trans (by fin_cases j <;> rfl)
  fin_cases g
  · have hr0 : rawImage ⟨0, by decide⟩ i = raw.getD i.val zero := by
      unfold rawImage; apply congrArg (fun k => raw.getD k zero); revert i; decide
    exact hr0.trans (action0_eq (valid_getD raw_valid i.val)).symm
  all_goals
    dsimp only [action, homG, compHom]
    simp only [h1, h2]
    unfold rawImage
    apply congrArg (fun k => raw.getD k zero)
    revert i; decide
lemma rawImage_mem (g : Fin 12) (i : Fin 9) : rawImage g i ∈ raw := by
  fin_cases g <;> fin_cases i <;> simp [rawImage, rawPermCodes, raw]
lemma action_raw_subset (g : Fin 12) : raw.toFinset.image (action g) ⊆ raw.toFinset := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [List.mem_toFinset] at hb ⊢
  have hex : ∃ i : Fin 9, raw.getD i.val zero = b := by
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
  obtain ⟨i, rfl⟩ := hex
  rw [← rawImage_eq g i]
  exact rawImage_mem g i
def Feasible (H : SigHom) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image H.fn
lemma feasible_mono {H : SigHom} {k k' : Nat} {S : Finset Sig}
    (h : Feasible H k S) (hk : k ≤ k') : Feasible H k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h; exact ⟨m, hm.trans hk, t, T, hl, hs⟩
lemma feasible_subset {H : SigHom} {k : Nat} {S S' : Finset Sig}
    (h : Feasible H k S) (hsub : S.image H.fn ⊆ S'.image H.fn) : Feasible H k S' := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h; exact ⟨m, hm, t, T, hl, hs.trans hsub⟩
lemma neg_rep (w : List Sig) {a : Sig} (hva : Valid a) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases hva (Or.inl ha : represented w a) with rfl | rfl | ⟨hm, hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.2.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
lemma feasible_pull {H : SigHom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image H.fn).toList (H.fn g) ∨ witness (S.image H.fn).toList (H.fn g))
    (h : Feasible H q S') : Feasible H (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image H.fn).toList ++ [H.fn g] := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩
lemma feasible_free {H : SigHom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image H.fn).toList (H.fn g))
    (h : Feasible H q S') : Feasible H q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb
lemma pull_unary {H : SigHom} {q : Nat} {a : Sig} {U : Finset Sig} (hva : Valid a)
    (h : Feasible H q (insert (neg a) U)) : Feasible H (q + 1) (insert a U) := by
  apply feasible_pull (g := neg a) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hneg hva]
  exact neg_rep _ (H.valid a) (by simp)
lemma pull_binary {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible H q (insert (bin d a b) U)) : Feasible H (q + 1) (insert a (insert b U)) := by
  apply feasible_pull (g := bin d a b) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hbin]
  exact bin_rep _ (H.valid a) (H.valid b) (Or.inl (by simp)) (Or.inl (by simp))
lemma free_unary {H : SigHom} {q : Nat} {a : Sig} {U : Finset Sig} (hva : Valid a)
    (ha : ¬ proper (H.fn a)) (h : Feasible H q (insert (neg a) U)) :
    Feasible H q (insert a U) := by
  apply feasible_free (g := neg a) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rcases operand_cases (H.valid a) (Or.inr ha : represented [] (H.fn a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2.2 (by rw [H.hneg hva, hz, neg_laws.1]))
  · exact Or.inr (fun hp => hp.2.1 (by rw [H.hneg hva, ho, neg_laws.2]))
  · simp at hm
lemma free_binary_left {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : ¬ proper (H.fn a)) (h : Feasible H q (insert (bin d a b) U)) :
    Feasible H q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hbin, bin_comm]
  rcases operand_cases (H.valid a) (Or.inr ha : represented [] (H.fn a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp => hp.2.1 (bin_laws (H.valid b)).2.2.1)
    · rw [(bin_laws (H.valid b)).2.1]; exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(bin_laws (H.valid b)).1]; exact Or.inl (by simp)
    · exact Or.inr (fun hp => hp.2.2 (bin_laws (H.valid b)).2.2.2.1)
  · simp at hm
lemma free_binary_right {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : ¬ proper (H.fn b)) (h : Feasible H q (insert (bin d a b) U)) :
    Feasible H q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h
lemma feasible_live {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom) :
    Feasible H k S := by
  induction h with
  | stop => refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩; simp [H.htarget]
  | unary ha _ _ ih => exact pull_unary ha.1 ih
  | binary _ _ _ _ _ ih => exact pull_binary ih
lemma feasible_const {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom)
    (a : Sig) (ha : a ∈ S) (hc : ¬ proper (H.fn a)) :
    ∃ q < k, Feasible H q S := by
  induction h with
  | stop =>
    have ht : a = target := Finset.mem_singleton.mp ha
    exact (hc (by rw [ht, H.htarget]; exact target_proper)).elim
  | @unary k t U b hp _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k, by omega, free_unary hp.1 hc (feasible_live tail H)⟩
    · obtain ⟨q, hq, h⟩ := ih (Finset.mem_insert_of_mem ha)
      exact ⟨q + 1, by omega, pull_unary hp.1 h⟩
  | @binary k t U b c d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k, by omega, free_binary_left hc (feasible_live tail H)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k, by omega, free_binary_right hc (feasible_live tail H)⟩
      · obtain ⟨q, hq, h⟩ := ih (Finset.mem_insert_of_mem hU)
        exact ⟨q + 1, by omega, pull_binary h⟩
lemma not_proper_bin_consts {H : SigHom} {a b : Sig} (d : Bool)
    (hca : ¬ proper (H.fn a)) (hcb : ¬ proper (H.fn b)) :
    ¬ proper (H.fn (bin d a b)) := by
  rw [H.hbin]
  rcases operand_cases (H.valid a) (Or.inr hca : represented [] (H.fn a)) with ha0 | ha1 | hm
  · rw [ha0, bin_comm]
    rcases operand_cases (H.valid b) (Or.inr hcb : represented [] (H.fn b)) with hb0 | hb1 | hm'
    · rw [hb0]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_zero).2.2.1
      · exact fun hp => hp.2.1 (bin_laws valid_zero).2.1
    · rw [hb1]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_one).2.2.1
      · exact fun hp => hp.2.2 (bin_laws valid_one).2.1
    · simp at hm'
  · rw [ha1, bin_comm]
    rcases operand_cases (H.valid b) (Or.inr hcb : represented [] (H.fn b)) with hb0 | hb1 | hm'
    · rw [hb0]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_zero).1
      · exact fun hp => hp.2.2 (bin_laws valid_zero).2.2.2.1
    · rw [hb1]; cases d
      · exact fun hp => hp.2.2 (bin_laws valid_one).1
      · exact fun hp => hp.2.2 (bin_laws valid_one).2.2.2.1
    · simp at hm'
  · simp at hm
lemma feasible_two_consts {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom)
    (a b : Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ proper (H.fn a)) (hcb : ¬ proper (H.fn b)) :
    ∃ q, q + 2 ≤ k ∧ Feasible H q S := by
  induction h with
  | stop =>
    have e1 := Finset.mem_singleton.mp ha
    have e2 := Finset.mem_singleton.mp hb
    exact (hab (e1.trans e2.symm)).elim
  | @unary k t U c hpc _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
      exact ⟨q, by omega, free_unary hpc.1 hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q, by omega, free_unary hpc.1 hcb hf⟩
      · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
        exact ⟨q + 1, by omega, pull_unary hpc.1 hf⟩
  | @binary k t U c e d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H (bin d a b) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hca hcb)
          exact ⟨q, by omega, free_binary_left hca hf⟩
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
          exact ⟨q, by omega, free_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H (bin d b a) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hcb hca)
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
            exact ⟨q, by omega, free_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
            exact ⟨q, by omega, free_binary_right hcb hf⟩
          · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
            exact ⟨q + 1, by omega, pull_binary hf⟩
def posIdx4 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 posKey4 (if j.val < 252 then j.val else 0))
def negIdx4 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 negKey4 (if j.val < 252 then j.val else 0))
def homProject4 : SigHom := pairHom posIdx4 negIdx4
abbrev project4 (a : Sig) : Sig := homProject4.fn a
def posIdx0 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 posKey0 (if j.val < 232 then j.val else 232))
def negIdx0 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 negKey0 (if j.val < 232 then j.val else 232))
def homProject0 : SigHom := pairHom posIdx0 negIdx0
abbrev project0 (a : Sig) : Sig := homProject0.fn a
def leafIdx (j : Fin 414) : Fin 414 :=
  if h : j.val < 232 then ⟨j.val, by omega⟩ else ⟨0, by omega⟩
def homProjectLeaf : SigHom := pairHom leafIdx leafIdx
abbrev projectLeaf (a : Sig) : Sig := homProjectLeaf.fn a
def homProject (i : Fin 9) : SigHom :=
  if i.val = 4 ∨ i.val = 6 ∨ i.val = 7 then compHom homProject4 (homG (gOfV i))
  else compHom homProject0 (homG (gOfV i))
abbrev project (i : Fin 9) (a : Sig) : Sig := (homProject i).fn a
def to1007 (a : Sig) : Base1007.Sig := (BitVec.ofNat 252 a.1, BitVec.ofNat 252 a.2)
lemma b1007_one_eq : Base1007.one = (BitVec.allOnes 252, BitVec.allOnes 252) := rfl
lemma b1007_target_eq : Base1007.target = (BitVec.allOnes 252, 0) := rfl
lemma to1007_zero : to1007 zero = Base1007.zero := rfl
lemma to1007_one : to1007 one = Base1007.one := by decide +kernel
lemma to1007_target : to1007 target = Base1007.target := by decide +kernel
lemma to1007_neg (a : Sig) : to1007 (neg a) = Base1007.neg (to1007 a) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [to1007, neg, Base1007.neg, BitVec.getLsbD_ofNat, BitVec.getLsbD_not,
      testBit_bnot_lt _ (show i < 414 by omega), hi, decide_true, Bool.true_and]
lemma to1007_bin (d : Bool) (a b : Sig) :
    to1007 (bin d a b) = Base1007.bin d (to1007 a) (to1007 b) := by
  cases d <;> apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
    simp [to1007, bin, Base1007.bin]
lemma b1007_bin_laws (a : Base1007.Sig) :
    Base1007.bin false a Base1007.one = a ∧ Base1007.bin true a Base1007.zero = a ∧
    Base1007.bin false a Base1007.zero = Base1007.zero ∧ Base1007.bin true a Base1007.one = Base1007.one ∧
    Base1007.bin false a a = a ∧ Base1007.bin true a a = a := by
  obtain ⟨p, n⟩ := a
  simp only [Base1007.bin, b1007_one_eq, Base1007.zero, Bool.false_eq_true, ite_true, ite_false,
    BitVec.and_allOnes, BitVec.or_allOnes, BitVec.and_self, BitVec.or_self]
  simp
lemma b1007_bin_comm (d : Bool) (a b : Base1007.Sig) :
    Base1007.bin d a b = Base1007.bin d b a := by
  cases d <;> simp [Base1007.bin, BitVec.and_comm, BitVec.or_comm]
lemma b1007_neg_laws :
    Base1007.neg Base1007.zero = Base1007.one ∧ Base1007.neg Base1007.one = Base1007.zero := by
  simp [Base1007.neg, Base1007.zero, b1007_one_eq]
lemma b1007_live_proper {k t S} (h : Base1007.Live k t S) : ∀ a ∈ S, Base1007.proper a := by
  induction h with
  | stop =>
    intro a ha; rw [Finset.mem_singleton.mp ha]
    unfold Base1007.proper; rw [b1007_target_eq, Base1007.zero, b1007_one_eq]; decide
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma b1007_pull_gate {w : Finset Base1007.Sig} {z : Base1007.Sig} {k t S} (h : Base1007.Live k t S)
    (hz : (z ∈ w ∨ ¬ Base1007.proper z) ∨
      (∃ a ∈ w, Base1007.proper a ∧ z = Base1007.neg a) ∨
      (∃ d a b, a ∈ w ∧ b ∈ w ∧ Base1007.proper a ∧ Base1007.proper b ∧ a ≠ b ∧ z = Base1007.bin d a b))
    (sub : S ⊆ insert z w) :
    ∃ k' t' S', k' ≤ k + 1 ∧ Base1007.Live k' t' S' ∧ S' ⊆ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha; rcases Finset.mem_insert.mp (sub ha) with rfl | ha'
      · exact hw
      · exact ha'
    · have hp := b1007_live_proper h z hm
      rcases hz with hr | ⟨a, ha, hp', eq⟩ | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (Base1007.neg a)
        have ht : Base1007.Live k t (insert (Base1007.neg a) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : U ⊆ w := fun v hv => by
          obtain ⟨hne, hm'⟩ := Finset.mem_erase.mp hv
          exact (Finset.mem_insert.mp (sub hm')).resolve_left hne
        have hf : Base1007.neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu u)
        exact ⟨_, _, _, Nat.le_refl _, Base1007.Live.unary hp' hf ht,
          Finset.insert_subset_iff.mpr ⟨ha, hu⟩⟩
      · subst z
        let U := S.erase (Base1007.bin d a b)
        have ht : Base1007.Live k t (insert (Base1007.bin d a b) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : U ⊆ w := fun v hv => by
          obtain ⟨hne, hm'⟩ := Finset.mem_erase.mp hv
          exact (Finset.mem_insert.mp (sub hm')).resolve_left hne
        have hf : Base1007.bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu u)
        exact ⟨_, _, _, Nat.le_refl _, Base1007.Live.binary pa pb hab hf ht,
          Finset.insert_subset_iff.mpr ⟨ha, Finset.insert_subset_iff.mpr ⟨hb, hu⟩⟩⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; exact (Finset.mem_insert.mp (sub ha)).resolve_left (fun eq => hm (eq ▸ ha))
lemma live_to1007 {k t S} (h : Live k t S) :
    ∃ k' t' T, k' ≤ k ∧ Base1007.Live k' t' T ∧ T ⊆ S.image to1007 := by
  induction h with
  | stop =>
    refine ⟨0, 0, {Base1007.target}, Nat.le_refl _, Base1007.Live.stop, ?_⟩
    simp [to1007_target]
  | @unary k t U a _ _ _ ih =>
    obtain ⟨k', t', T, hk, hl, hsub⟩ := ih
    rw [Finset.image_insert, to1007_neg] at hsub
    have hsub' : T ⊆ insert (Base1007.neg (to1007 a)) ((insert a U).image to1007) :=
      hsub.trans (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.subset_insert a U)))
    have ha_mem : to1007 a ∈ (insert a U).image to1007 := Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
    have hz : (Base1007.neg (to1007 a) ∈ (insert a U).image to1007 ∨ ¬ Base1007.proper (Base1007.neg (to1007 a))) ∨
        (∃ x ∈ (insert a U).image to1007, Base1007.proper x ∧ Base1007.neg (to1007 a) = Base1007.neg x) ∨
        (∃ d x y, x ∈ (insert a U).image to1007 ∧ y ∈ (insert a U).image to1007 ∧
          Base1007.proper x ∧ Base1007.proper y ∧ x ≠ y ∧ Base1007.neg (to1007 a) = Base1007.bin d x y) := by
      by_cases h0 : to1007 a = Base1007.zero
      · exact Or.inl (Or.inr (fun hp => hp.2 (by rw [h0, b1007_neg_laws.1])))
      by_cases h1 : to1007 a = Base1007.one
      · exact Or.inl (Or.inr (fun hp => hp.1 (by rw [h1, b1007_neg_laws.2])))
      exact Or.inr (Or.inl ⟨to1007 a, ha_mem, ⟨h0, h1⟩, rfl⟩)
    obtain ⟨k'', t'', T', hk', hl', hT'⟩ := b1007_pull_gate hl hz hsub'
    exact ⟨k'', t'', T', by omega, hl', hT'⟩
  | @binary k t U a b d _ _ _ _ _ ih =>
    obtain ⟨k', t', T, hk, hl, hsub⟩ := ih
    rw [Finset.image_insert, to1007_bin] at hsub
    let W := (insert a (insert b U)).image to1007
    have hsub' : T ⊆ insert (Base1007.bin d (to1007 a) (to1007 b)) W :=
      hsub.trans (Finset.insert_subset_insert _ (Finset.image_subset_image
        (fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))))
    have ha_mem : to1007 a ∈ W := Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
    have hb_mem : to1007 b ∈ W := Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hz : (Base1007.bin d (to1007 a) (to1007 b) ∈ W ∨ ¬ Base1007.proper (Base1007.bin d (to1007 a) (to1007 b))) ∨
        (∃ x ∈ W, Base1007.proper x ∧ Base1007.bin d (to1007 a) (to1007 b) = Base1007.neg x) ∨
        (∃ d' x y, x ∈ W ∧ y ∈ W ∧ Base1007.proper x ∧ Base1007.proper y ∧ x ≠ y ∧
          Base1007.bin d (to1007 a) (to1007 b) = Base1007.bin d' x y) := by
      have la := b1007_bin_laws (to1007 a)
      have lb := b1007_bin_laws (to1007 b)
      by_cases ha0 : to1007 a = Base1007.zero
      · rw [ha0, b1007_bin_comm]; cases d
        · exact Or.inl (Or.inr (fun hp => hp.1 lb.2.2.1))
        · rw [lb.2.1]; exact Or.inl (Or.inl hb_mem)
      by_cases ha1 : to1007 a = Base1007.one
      · rw [ha1, b1007_bin_comm]; cases d
        · rw [lb.1]; exact Or.inl (Or.inl hb_mem)
        · exact Or.inl (Or.inr (fun hp => hp.2 lb.2.2.2.1))
      by_cases hb0 : to1007 b = Base1007.zero
      · rw [hb0]; cases d
        · exact Or.inl (Or.inr (fun hp => hp.1 la.2.2.1))
        · rw [la.2.1]; exact Or.inl (Or.inl ha_mem)
      by_cases hb1 : to1007 b = Base1007.one
      · rw [hb1]; cases d
        · rw [la.1]; exact Or.inl (Or.inl ha_mem)
        · exact Or.inl (Or.inr (fun hp => hp.2 la.2.2.2.1))
      by_cases he : to1007 a = to1007 b
      · rw [← he]; cases d
        · rw [la.2.2.2.2.1]; exact Or.inl (Or.inl ha_mem)
        · rw [la.2.2.2.2.2]; exact Or.inl (Or.inl ha_mem)
      exact Or.inr (Or.inr ⟨d, to1007 a, to1007 b, ha_mem, hb_mem, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩, he, rfl⟩)
    obtain ⟨k'', t'', T', hk', hl', hT'⟩ := b1007_pull_gate hl hz hsub'
    exact ⟨k'', t'', T', by omega, hl', hT'⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma project4_raw4 : homProject4.fn raw4 = zero := by decide +kernel
def raw1007Order : List Sig := [raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma to1007_project4_raw : raw1007Order.map (fun a => to1007 (project4 a)) = Base1007.raw := by
  decide +kernel
lemma root_project4_impossible : ¬ Feasible homProject4 12 raw.toFinset := by
  rintro ⟨m, hm, t, T, hl, hsub⟩
  obtain ⟨m', t', T', hm', hl', hT'⟩ := live_to1007 hl
  apply Base1007.no_live12 (hm'.trans hm) hl'
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hT' ha)
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (hsub hb)
  have hcm : c ∈ raw := List.mem_toFinset.mp hc
  by_cases hc4 : c = raw4
  · subst c
    have h0 : to1007 (homProject4.fn raw4) = Base1007.zero := by rw [project4_raw4]; rfl
    exact False.elim ((b1007_live_proper hl' _ ha).1 h0)
  · have hmem : c ∈ raw1007Order := by
      simp only [raw, raw1007Order, List.mem_cons, List.not_mem_nil, or_false] at hcm ⊢
      rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    rw [← to1007_project4_raw]
    exact List.mem_map_of_mem hmem
def lo232 : Nat := 2^232 - 1
def thetaWord (a : Sig) : Nat := ((a.1 &&& lo232) <<< 232) ||| (a.2 &&& lo232)
lemma thetaWord_bit (a : Sig) (j : Nat) :
    (thetaWord a).testBit j =
      if j < 232 then a.2.testBit j else if j < 464 then a.1.testBit (j - 232) else false := by
  simp only [thetaWord, lo232, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft]
  by_cases hj : j < 232
  · simp [hj, show ¬ 232 ≤ j by omega]
  · by_cases hk : j < 464
    · simp [hj, hk, show 232 ≤ j by omega, show j - 232 < 232 by omega]
    · simp [hj, hk, show 232 ≤ j by omega, show ¬ j - 232 < 232 by omega]
lemma thetaWord_target : thetaWord target = Base1007.Theta.goal 232 := by decide +kernel
lemma testBit_thetaMask (j : Nat) :
    (Base1007.Theta.mask 232).testBit j = decide (j < 464) := by
  change (2 ^ (232 + 232) - 1).testBit j = decide (j < 464)
  rw [Nat.testBit_two_pow_sub_one]
lemma thetaWord_neg {a : Sig} :
    thetaWord (neg a) = thetaWord a ^^^ Base1007.Theta.mask 232 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, thetaWord_bit, thetaWord_bit, testBit_thetaMask]
  by_cases hl : j < 232
  · simp [hl, neg, testBit_bnot_lt _ (show j < 414 by omega), show j < 464 by omega]
  · by_cases hh : j < 464
    · simp [hl, hh, neg, testBit_bnot_lt _ (show j - 232 < 414 by omega)]
    · simp [hl, hh]
lemma thetaWord_bin (d : Bool) (a b : Sig) :
    thetaWord (bin d a b) =
      if d then thetaWord a ||| thetaWord b else thetaWord a &&& thetaWord b := by
  apply Nat.eq_of_testBit_eq; intro j
  cases d <;> simp only [bin, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_or,
    Nat.testBit_and, thetaWord_bit] <;> split_ifs <;> rfl
lemma live_thetaRun {k t S} (h : Live k t S) (v : List Sig) (hv : v.Nodup) (he : v.toFinset = S) :
    Base1007.Theta.NatRun (Base1007.Theta.mask 232) (Base1007.Theta.goal 232) k (v.map thetaWord) := by
  induction h generalizing v with
  | stop =>
    have hp : ([target] : List Sig).Perm v :=
      List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [he])
    have hp' := hp.map thetaWord
    simp only [List.map_cons, List.map_nil, thetaWord_target] at hp'
    exact Base1007.Theta.Run.perm hp' Base1007.Theta.Run.done
  | @unary k t U a ha hf _ ih =>
    let rest := dropped [a] v
    have ham : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hn, eq⟩ := edit_list (del := [a]) hv (by simp) (by simpa using he)
    let save := decide (a ∈ U)
    have hkeep : Base1007.Theta.kept save a rest = keepOf U [a] ++ rest := by
      by_cases hm : a ∈ U <;> simp [save, Base1007.Theta.kept, keepOf, hm]
    rw [← hkeep] at hn eq
    have hs : (neg a :: Base1007.Theta.kept save a rest).toFinset = insert (neg a) U := by
      rw [List.toFinset_cons, eq]
    have hnd : (neg a :: Base1007.Theta.kept save a rest).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem ?_), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := (recover_perm [a] v hv (by simp) (by simpa using ham)).symm.map thetaWord
    have hdone := ih _ hnd hs
    have hmap : (neg a :: Base1007.Theta.kept save a rest).map thetaWord =
        (thetaWord a ^^^ Base1007.Theta.mask 232) ::
          Base1007.Theta.kept save (thetaWord a) (rest.map thetaWord) := by
      cases save <;> simp [Base1007.Theta.kept, thetaWord_neg]
    rw [hmap] at hdone
    exact Base1007.Theta.Run.perm p (Base1007.Theta.Run.one true save hdone)
  | @binary k t U a b d _ _ hab hf _ ih =>
    let rest := dropped [a, b] v
    have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨hn, eq⟩ := edit_list (del := [a, b]) hv (by simp [hab]) (by simpa using he)
    let sa := decide (a ∈ U)
    let sb := decide (b ∈ U)
    have hkeep : Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest) = keepOf U [a, b] ++ rest := by
      by_cases ham : a ∈ U <;> by_cases hbm : b ∈ U <;>
        simp [sa, sb, Base1007.Theta.kept, keepOf, ham, hbm]
    rw [← hkeep] at hn eq
    have hs : (bin d a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).toFinset =
        insert (bin d a b) U := by rw [List.toFinset_cons, eq]
    have hnd : (bin d a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := (recover_perm [a, b] v hv (by simp [hab]) (by simp [ah, bh])).symm.map thetaWord
    have hdone := ih _ hnd hs
    have hkeptMap (x : Sig) (l : List Sig) (fl : Bool) :
        (Base1007.Theta.kept fl x l).map thetaWord =
        Base1007.Theta.kept fl (thetaWord x) (l.map thetaWord) := by
      cases fl <;> simp [Base1007.Theta.kept]
    cases d
    · have hmap : (bin false a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).map thetaWord =
          (thetaWord a &&& thetaWord b) ::
            Base1007.Theta.kept sa (thetaWord a) (Base1007.Theta.kept sb (thetaWord b) (rest.map thetaWord)) := by
        simp [List.map_cons, thetaWord_bin, hkeptMap]
      rw [hmap] at hdone
      exact Base1007.Theta.Run.perm p (Base1007.Theta.Run.two true sa sb hdone)
    · have hmap : (bin true a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).map thetaWord =
          (thetaWord a ||| thetaWord b) ::
            Base1007.Theta.kept sa (thetaWord a) (Base1007.Theta.kept sb (thetaWord b) (rest.map thetaWord)) := by
        simp [List.map_cons, thetaWord_bin, hkeptMap]
      rw [hmap] at hdone
      exact Base1007.Theta.Run.perm p (Base1007.Theta.Run.two false sa sb hdone)
def thetaOrder : List Sig := [raw2, raw8, raw3, raw1, raw6, raw7, raw5]
def thetaInputs : List Sig := thetaOrder.map (fun a => projectLeaf (project0 a))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma project0_raw0 : project0 raw0 = zero := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectLeaf_project0_raw4 : projectLeaf (project0 raw4) = zero := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaInputs_word : thetaInputs.map thetaWord = Base1007.Theta.xs517 := by decide +kernel
lemma thetaWords_nodup : Base1007.Theta.xs517.Nodup := by decide +kernel
lemma thetaInputs_nd : thetaInputs.Nodup := by
  have h := thetaWords_nodup
  rw [← thetaInputs_word] at h
  exact List.Nodup.of_map _ h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bit232_unique : raw.all (fun a => decide (a = raw4) || !(sep true (project0 a)).testBit 232) = true := by
  decide +kernel
lemma root_project0_impossible : ¬ Feasible homProject0 11 raw.toFinset := by
  rintro ⟨m, hm, t, T, hl, hsub⟩
  have h4 : project0 raw4 ∈ T := by
    obtain ⟨x, hxT, hsep⟩ := live_sep hl 232 (by omega)
    obtain ⟨a, haRaw, rfl⟩ := Finset.mem_image.mp (hsub hxT)
    have hsw := sep_weaken t (live_proper hl _ hxT).1 232 (by omega) hsep
    have hall := List.all_eq_true.mp bit232_unique a (List.mem_toFinset.mp haRaw)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hall
    rcases hall with rfl | hf
    · exact hxT
    · exact False.elim (by rw [hsw] at hf; contradiction)
  have hz4 : ¬ proper (homProjectLeaf.fn (project0 raw4)) := fun hp =>
    hp.2.1 projectLeaf_project0_raw4
  obtain ⟨q, hq, m', hm', t', T', hl', hT'⟩ := feasible_const hl homProjectLeaf (project0 raw4) h4 hz4
  have hsubTheta : ∀ a ∈ T', a ∈ thetaInputs := by
    intro a ha
    obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp (hT' ha)
    obtain ⟨c, hcRaw, rfl⟩ := Finset.mem_image.mp (hsub hbT)
    have hcm := List.mem_toFinset.mp hcRaw
    by_cases hc0 : c = raw0
    · subst c
      have h0 : projectLeaf (project0 raw0) = zero := by
        rw [project0_raw0]; exact homProjectLeaf.hzero
      exact False.elim ((live_proper hl' _ ha).2.1 h0)
    by_cases hc4 : c = raw4
    · subst c
      exact False.elim ((live_proper hl' _ ha).2.1 projectLeaf_project0_raw4)
    · have hmem : c ∈ thetaOrder := by
        simp only [raw, thetaOrder, List.mem_cons, List.not_mem_nil, or_false] at hcm ⊢
        rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      exact List.mem_map_of_mem hmem
  let v := thetaInputs.filter (fun a => decide (a ∈ T'))
  have he : v.toFinset = T' := by
    ext a; simp only [v, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨hsubTheta _ ha, ha⟩⟩
  have hrun := live_thetaRun hl' v (thetaInputs_nd.filter _) he
  apply Base1007.Theta.noSub (show m' ≤ 10 by omega) _ hrun
  have sub := List.Sublist.map thetaWord (List.filter_sublist (l := thetaInputs) (p := fun a => decide (a ∈ T')))
  rwa [thetaInputs_word] at sub
def extraAnd := bin false raw0 raw3
def supplied := raw ++ [extraAnd] ++ [neg extraAnd]
lemma extraAnd_valid : Valid extraAnd :=
  valid_bin (raw_valid raw0 (by simp [raw])) (raw_valid raw3 (by simp [raw]))
lemma supplied_valid : ∀ a ∈ supplied, Valid a := by
  intro a ha
  simp only [supplied, List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | rfl) | rfl
  · exact raw_valid _ ha
  · exact extraAnd_valid
  · exact valid_neg extraAnd_valid
lemma target_from_augmented (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!(x 0 && x 3)]) = edgeF x) :
    target ∈ execute C.gates supplied := by
  let w := execute C.gates supplied
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates supplied supplied_valid
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates supplied).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ supplied_valid (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list, sample_ok] at eq
    have eu : bit s i extraAnd = (sample s i 0 && sample s i 3) := by
      exact bit_bin s i false raw0 raw3
    have en := bit_neg s i extraAnd_valid
    simpa only [Circuit.eval, Circuit.wires, supplied, List.map_append, List.map_cons, List.map_nil, en, eu] using eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq
      intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]
        simp [hi]
    · apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]
        exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)
lemma forced_input {k t S} (hl : Live k t S) (hs : ∀ a ∈ S, a ∈ supplied)
    (v : Sig) (i : Nat) (hi : i < 414)
    (unique : supplied.all (fun a => decide (a = v) || !(sep true a).testBit i) = true) :
    v ∈ S := by
  obtain ⟨a, ha, hdiff⟩ := live_sep hl i hi
  have diff := sep_weaken t (live_proper hl a ha).1 i hi hdiff
  have hu := List.all_eq_true.mp unique a (hs a ha)
  simp only [diff, Bool.not_true, Bool.or_false, decide_eq_true_eq] at hu
  exact hu ▸ ha
lemma augmented_bound {k t S} (hl : Live k t S) (hs : ∀ a ∈ S, a ∈ supplied)
    (hk : k ≤ 13) : False := by
  have m0 := forced_input hl hs raw0 3 (by decide) (by decide +kernel)
  have m4 := forced_input hl hs raw4 1 (by decide) (by decide +kernel)
  have c0 : ¬ proper (project0 raw0) := fun hp => hp.2.1 project0_raw0
  have ez : project0 extraAnd = zero := by
    change homProject0.fn (bin false raw0 raw3) = _
    rw [homProject0.hbin]
    change bin false (project0 raw0) (project0 raw3) = zero
    rw [project0_raw0, bin_comm]
    exact (bin_laws (homProject0.valid raw3)).2.2.1
  have nz : project0 (neg extraAnd) = one := by
    rw [show project0 (neg extraAnd) = neg (project0 extraAnd) from homProject0.hneg extraAnd_valid, ez, neg_laws.1]
  have ec : ¬ proper (project0 extraAnd) := fun hp => hp.2.1 ez
  have nc : ¬ proper (project0 (neg extraAnd)) := fun hp => hp.2.2 nz
  by_cases hx : extraAnd ∈ S ∨ neg extraAnd ∈ S
  · obtain ⟨q, hq, m, hm, u, T, run, hT⟩ : ∃ q, q + 2 ≤ k ∧ Feasible homProject0 q S := by
      rcases hx with hx | hx
      · exact feasible_two_consts hl homProject0 raw0 extraAnd m0 hx (by decide +kernel) c0 ec
      · exact feasible_two_consts hl homProject0 raw0 (neg extraAnd) m0 hx (by decide +kernel) c0 nc
    apply root_project0_impossible
    refine ⟨m, by omega, u, T, run, ?_⟩
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hT hv)
    have mem := hs a ha
    simp only [supplied, List.mem_append, List.mem_singleton] at mem
    rcases mem with (hr | rfl) | rfl
    · exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hr)
    · exact (ec (live_proper run _ hv)).elim
    · exact (nc (live_proper run _ hv)).elim
  · have onlyRaw : S ⊆ raw.toFinset := by
      intro a ha
      have mem := hs a ha
      simp only [supplied, List.mem_append, List.mem_singleton] at mem
      rcases mem with (hr | rfl) | rfl
      · exact List.mem_toFinset.mpr hr
      · exact (hx (Or.inl ha)).elim
      · exact (hx (Or.inr ha)).elim
    have c4 : ¬ proper (project4 raw4) := fun hp => hp.2.1 project4_raw4
    obtain ⟨q, hq, hf⟩ := feasible_const hl homProject4 raw4 m4 c4
    exact root_project4_impossible (feasible_mono (feasible_subset hf (Finset.image_mono _ onlyRaw)) (by omega))
theorem augmented_main (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!(x 0 && x 3)]) = edgeF x) :
    14 ≤ C.size := by
  obtain ⟨k, t, S, hk, hl, hs⟩ := extract C.gates supplied supplied_valid hf (target_from_augmented C hf he)
  by_contra! small
  change C.gates.length < 14 at small
  exact augmented_bound hl hs (by omega)
end Main1672
end PEqualNP.Outside.L_meta_3116

theorem PEqualNP.Outside.L_meta_3116 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))] ++ [!(x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size :=
  PEqualNP.Outside.L_meta_3116.Main1672.augmented_main
