import Mathlib
import Mathlib.Data.List.Sort
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18264
namespace Ae
abbrev Gates:=ℕ→Bool × ℕ × ℕ
def bin (op a b:Bool):=if op then a && b else a || b
def val (S:Finset ℕ) (g:Gates) (x:ℕ→Bool) (w:ℕ):Bool:=
  if w∈S then bin (g w).1
    (if (g w).2.1 < w then val S g x (g w).2.1 else false)
    (if (g w).2.2 < w then val S g x (g w).2.2 else false)
  else x w
termination_by w
def Good (H:ℕ) (S:Finset ℕ) (g:Gates):Prop:=
  ∀ w∈S, H≤w∧(g w).2.1 < w∧(g w).2.2 < w
lemma vin {S:Finset ℕ} {g:Gates} {x:ℕ→Bool} {w H:ℕ} (h:Good H S g) (hw:w∈S):
    val S g x w=bin (g w).1 (val S g x (g w).2.1) (val S g x (g w).2.2):=by
  rw [val, ite_eq_left hw, ite_eq_left (h w hw).2.1, ite_eq_left (h w hw).2.2]
lemma vout {S:Finset ℕ} {g:Gates} {x:ℕ→Bool} {w:ℕ} (hw:w∉S):val S g x w=x w:=by
  rw [val, ite_eq_right hw]
def lport (i:ℕ):=2*i+2
def rport (i:ℕ):=2*i+3
def point (M:Finset ℕ) (u v w:ℕ):Bool:=
  decide (w=0∨w=lport u∨w=rport v∨(u∉M∧w=rport u)∨(v∉M∧w=lport v))
def AY (K M S:Finset ℕ) (g:Gates) (o:ℕ):Prop:=
  ∀ u∈K, ∀ v∈K, val S g (point M u v) o=decide (u≠v)
def Dark (K S:Finset ℕ) (g:Gates) (w:ℕ):Prop:=
  ∀ i∈K, val S g (point ∅ i i) w=false
def AN (K S:Finset ℕ) (g:Gates):Prop:=
  ∀ w∈S, Dark K S g (g w).2.1∨Dark K S g (g w).2.2→Dark K S g w
def Alias (K M S:Finset ℕ) (g:Gates) (w:ℕ):Prop:=
  ∃ t < w, ∀ u∈K, ∀ v∈K, val S g (point M u v) w=val S g (point M u v) t
lemma GN (M:Finset ℕ) (i:ℕ):point M i i=point ∅ i i:=by
  funext w
  unfold point
  congr 1
  apply propext
  tauto
def GJ (t b w:ℕ):=if w=t then b else w
lemma GK {b t:ℕ} (hb:b < t) (w:ℕ):GJ t b w≤w:=by
  by_cases hw:w=t <;> simp [GJ, hw, hb.le]
def nrSet (S:Finset ℕ) (t f:ℕ):=insert f (S.erase t)
def GP (g:Gates) (t b d o f:ℕ):Gates:=fun w=>
  if w=f then (false, d, GJ t b o)
  else ((g w).1, GJ t b (g w).2.1, GJ t b (g w).2.2)
lemma GO {H t b d o f:ℕ} {S:Finset ℕ} {g:Gates}
    (hg:Good H S g) (hT:Good H (nrSet S t f) (GP g t b d o f)) (hb:b < t)
    (hv:∀ x, val S g x t=(val S g x d || val S g x b)) (x:ℕ→Bool) (w:ℕ):
    w < f→(w < t∨val S g x d=false)→
      val (nrSet S t f) (GP g t b d o f) x (GJ t b w)=val S g x w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    intro hwf hx
    by_cases hwt:w=t
    · subst w
      have hd:val S g x d=false:=hx.resolve_left (Nat.lt_irrefl _)
      have hB:=ih b hb (hb.trans hwf) (Or.inl hb)
      simpa [GJ, hb.ne, hv x, hd] using hB
    · rw [show GJ t b w=w by simp [GJ, hwt]]
      by_cases hw:w∈S
      · have hnew:w∈nrSet S t f:=Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwt, hw⟩)
        rw [vin hT hnew, vin hg hw]
        simp only [GP, ite_eq_right hwf.ne]
        have hrec (c:ℕ) (hc:c < w):=ih c hc (hc.trans hwf) (hx.imp_left (fun h=>hc.trans h))
        rw [hrec _ (hg w hw).2.1, hrec _ (hg w hw).2.2]
      · have hnew:w∉nrSet S t f:=by simp [nrSet, hwf.ne, hw]
        rw [vout hnew, vout hw]
lemma GM {K S:Finset ℕ} {g:Gates} {H t:ℕ} (hg:Good H S g) (ht:t∈S)
    (hc:Dark K S g (g t).2.1∨Dark K S g (g t).2.2) (hn:¬Dark K S g t):
    ∃ d b:ℕ, d < t∧b < t∧Dark K S g d∧
      ∀ x, val S g x t=(val S g x d || val S g x b):=by
  have hop:(g t).1=false:=by
    cases hh:(g t).1 with
    | false=>rfl
    | true=>
      exfalso
      apply hn
      intro i hi
      rw [vin hg ht, hh]
      rcases hc with hd | hd <;> simp [bin, hd i hi]
  rcases hc with hd | hd
  · refine ⟨(g t).2.1, (g t).2.2, (hg t ht).2.1, (hg t ht).2.2, hd, ?_⟩
    intro x
    rw [vin hg ht, hop]
    rfl
  · refine ⟨(g t).2.2, (g t).2.1, (hg t ht).2.2, (hg t ht).2.1, hd, ?_⟩
    intro x
    rw [vin hg ht, hop]
    exact Bool.or_comm _ _
noncomputable def nrLit (K S:Finset ℕ) (g:Gates):Finset ℕ:=by
  classical
  exact S.filter (fun w=>¬Dark K S g w)
lemma GR {K M S:Finset ℕ} {g:Gates} {H o:ℕ}
    (hg:Good H S g) (hs:AY K M S g o) (hn:¬AN K S g):
    ∃ T:Finset ℕ, ∃ h:Gates, ∃ p:ℕ, Good H T h∧AY K M T h p∧
      T.card≤S.card∧(nrLit K T h).card < (nrLit K S g).card:=by
  classical
  unfold AN at hn
  push Not at hn
  obtain ⟨t, ht, hc, hnt⟩:=hn
  obtain ⟨d, b, hdt, hbt, hdark, hv⟩:=GM hg ht hc hnt
  let f:=S.sup id+o+H+1
  have hf (w:ℕ) (hw:w∈S):w < f:=by
    have hh:id w≤S.sup id:=Finset.le_sup hw
    change w≤S.sup id at hh
    dsimp [f]
    omega
  have hof:o < f:=by dsimp [f]; omega
  have hHf:H≤f:=by dsimp [f]; omega
  have hdf:d < f:=hdt.trans (hf t ht)
  let T:=nrSet S t f
  let h:=GP g t b d o f
  have hT:Good H T h:=by
    intro w hw
    change w∈insert f (S.erase t) at hw
    rcases Finset.mem_insert.mp hw with he | he
    · subst w
      simpa [h, GP] using And.intro hHf (And.intro hdf ((GK hbt o).trans_lt hof))
    · have hws:=(Finset.mem_erase.mp he).2
      have hwf:=(hf w hws).ne
      obtain ⟨hH, ha, hb⟩:=hg w hws
      simpa [h, GP, hwf] using And.intro hH (And.intro ((GK hbt _).trans_lt ha) ((GK hbt _).trans_lt hb))
  have heq (x:ℕ→Bool) (w:ℕ) (hwf:w < f) (hx:w < t∨val S g x d=false):
      val T h x (GJ t b w)=val S g x w:=
    GO hg hT hbt hv x w hwf hx
  have hdeq (x:ℕ→Bool):val T h x d=val S g x d:=by
    simpa only [GJ, ite_eq_right hdt.ne] using heq x d hdf (Or.inl hdt)
  have hfT:f∈T:=Finset.mem_insert_self _ _
  have hfeq (x:ℕ→Bool):val T h x f=(val S g x d || val T h x (GJ t b o)):=by
    rw [vin hT hfT]
    simp [h, GP, bin, hdeq]
  have hsol:AY K M T h f:=by
    intro u hu v hw
    let x:=point M u v
    change val T h x f=_
    rw [hfeq]
    cases hdx:val S g x d with
    | false=>
      rw [Bool.false_or, heq x o hof (Or.inr hdx)]
      exact hs u hu v hw
    | true=>
      have huv:u≠v:=by
        intro he
        have hx:x=point ∅ u u:=by change point M u v=_; rw [← he, GN]
        rw [hx, hdark u hu] at hdx
        contradiction
      simp [huv]
  have hfdark:Dark K T h f:=by
    intro i hi
    simpa only [GN M i, ne_self_iff_false, decide_false] using hsol i hi i hi
  have hsub:nrLit K T h⊆(nrLit K S g).erase t:=by
    intro w hw
    obtain ⟨hwT, hnw⟩:=Finset.mem_filter.mp hw
    rcases Finset.mem_insert.mp hwT with he | he
    · exact (hnw (he ▸ hfdark)).elim
    · obtain ⟨hwt, hws⟩:=Finset.mem_erase.mp he
      apply Finset.mem_erase.mpr
      refine ⟨hwt, Finset.mem_filter.mpr ⟨hws, ?_⟩⟩
      intro hd
      apply hnw
      intro i hi
      have hval:=heq (point ∅ i i) w (hf w hws) (Or.inr (hdark i hi))
      simpa only [GJ, ite_eq_right hwt, hd i hi] using hval
  have hcs:T.card≤S.card:=by
    exact (Finset.card_insert_le f (S.erase t)).trans (Finset.card_erase_add_one ht).le
  have htLit:t∈nrLit K S g:=Finset.mem_filter.mpr ⟨ht, hnt⟩
  exact ⟨T, h, f, hT, hsol, hcs, (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem htLit)⟩
lemma GQ {n:ℕ} {K M S:Finset ℕ} {g:Gates} {o:ℕ}
    (hg:Good (2*n+2) S g) (hs:AY K M S g o):
    ∃ T:Finset ℕ, ∃ h:Gates, ∃ p:ℕ,
      Good (2*n+2) T h∧AY K M T h p∧AN K T h∧T.card≤S.card:=by
  classical
  generalize hq:(nrLit K S g).card=q
  induction q using Nat.strong_induction_on generalizing S g o with
  | ind q ih=>
    by_cases hn:AN K S g
    · exact ⟨S, g, o, hg, hs, hn, le_rfl⟩
    · obtain ⟨T, h, p, hT, hsol, hle, hlt⟩:=GR hg hs hn
      obtain ⟨U, k, a, hU, hsol', hnorm, hle'⟩:=ih _ (hlt.trans_le hq.le) hT hsol rfl
      exact ⟨U, k, a, hU, hsol', hnorm, hle'.trans hle⟩
def CL (b:Bool) (i:ℕ):=if b then rport i else lport i
def CI (M:Finset ℕ) (b:Bool) (u v:ℕ):=if b then point M v u else point M u v
def CQ (M:Finset ℕ) (b:Bool) (u w:ℕ):=w=CL b u∨(u∉M∧w=CL (!b) u)
lemma crHit {M:Finset ℕ} {b:Bool} {u v w:ℕ}:CI M b u v w=true↔w=0∨CQ M b u w∨CQ M (!b) v w:=by
  cases b <;> simp [CI, point, CQ, CL] <;> tauto
lemma crEq {b c:Bool} {i j:ℕ}:CL b i=CL c j↔b=c∧i=j:=by
  cases b <;> cases c <;> simp [CL, lport, rport] <;> omega
lemma CG (b:Bool) (i:ℕ):CL b i≠0:=by cases b <;> simp [CL, lport, rport]
lemma Cu {i w:ℕ} {b:Bool}:point ∅ i i w=true↔w=0∨w=CL b i∨w=CL (!b) i:=by
  cases b <;> simp [point, CL] <;> tauto
lemma Cv {M:Finset ℕ} {i:ℕ}:point M i i=point ∅ i i:=by
  funext w
  apply Bool.eq_iff_iff.mpr
  simp [point]; tauto
lemma CR {K M S:Finset ℕ} {g:Gates} {o:ℕ} (hs:AY K M S g o) {b:Bool} {i j:ℕ} (hi:i∈K) (hj:j∈K) (hij:i≠j):val S g (CI M b i j) o=true:=by
  cases b <;> simp [CI, hs i hi j hj, hs j hj i hi, hij, Ne.symm hij]
lemma Cx {K M S:Finset ℕ} {g:Gates} {o:ℕ} (hs:AY K M S g o) {i:ℕ} (hi:i∈K):val S g (point ∅ i i) o=false:=by simpa [Cv] using hs i hi i hi
lemma Cr {M:Finset ℕ} {b:Bool} {i j w:ℕ} (hi:i∈M) (hw:w≠CL b i) (hx:CI M b i j w=true):point ∅ j j w=true:=by
  apply (Cu (b:=b)).2
  rw [crHit] at hx
  simp [CQ, hi, hw] at hx
  tauto
lemma crOff {M:Finset ℕ} {b:Bool} {i j:ℕ} (hi:i∈M) (hij:i≠j):CI M b i j (CL (!b) i)=false:=by
  apply Bool.eq_false_iff.mpr
  simp [crHit, CQ, crEq, CG, hi, hij]
lemma CB {M:Finset ℕ} {b:Bool} {i u v:ℕ} (hu:u≠i) (hv:v≠i):point M u v (CL b i)=false:=by
  cases b <;> simp [CL, point, lport, rport] <;> omega
lemma Cw (b:Bool) (i:ℕ):point ∅ i i (CL b i)=true:=(Cu (b:=b)).2 (Or.inr (Or.inl rfl))
lemma CE {M:Finset ℕ} {b:Bool} {i u v:ℕ} (hp:point (M.erase i) u v (CL b i)=true) {w:ℕ} (hw:point ∅ i i w=true):point (M.erase i) u v w=true:=by
  have h:u=i∨v=i:=by by_contra! h; simp [CB h.1 h.2] at hp
  rcases h with rfl | rfl <;> rcases (Cu (b:=false)).1 hw with rfl | rfl | rfl <;> simp [point, CL]
def CM (g:Gates) (t p:ℕ):=(g t).2.1=p∨(g t).2.2=p
lemma CU {g:Gates} {t p:ℕ} (h:CM g t p):∃ W, ((g t).2.1=p∧(g t).2.2=W)∨((g t).2.1=W∧(g t).2.2=p):=by
  rcases h with h | h
  · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨rfl, h⟩⟩
lemma Cy {H S g t p W} (hg:Good H S g) (ht:t∈S) (hf:((g t).2.1=p∧(g t).2.2=W)∨((g t).2.1=W∧(g t).2.2=p)) (x:ℕ→Bool):val S g x t=bin (g t).1 (val S g x p) (val S g x W):=by
  rw [vin hg ht]; rcases hf with h | h <;> rw [h.1, h.2]
  cases (g t).1 <;> simp [bin, Bool.and_comm, Bool.or_comm]
lemma CD {H S g t p W} (hg:Good H S g) (ht:t∈S) (hf:((g t).2.1=p∧(g t).2.2=W)∨((g t).2.1=W∧(g t).2.2=p)):p < t∧W < t:=by
  obtain ⟨_, ha, hb⟩:=hg t ht
  rcases hf with h | h <;> grind
lemma crCut {H S g} (hg:Good H S g) {x y:ℕ→Bool} {B:ℕ→Prop} {d:ℕ}
    (hraw:∀ w, ¬B w→w∉S→x w=true→y w=true)
    (hgate:∀ w∈S, w≤d→¬B w→(B (g w).2.1∨B (g w).2.2)→val S g x w=true→val S g y w=true)
    {w:ℕ} (hd:w≤d) (hw:¬B w) (hx:val S g x w=true):val S g y w=true:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    by_cases hS:w∈S
    · by_cases ha:B (g w).2.1∨B (g w).2.2
      · exact hgate w hS hd hw ha hx
      · push Not at ha
        obtain ⟨_, hl, hr⟩:=hg w hS
        have l:=ih _ hl (by omega) ha.1
        have r:=ih _ hr (by omega) ha.2
        rw [vin hg hS] at hx ⊢
        cases ho:(g w).1 <;> simp [bin, ho] at hx ⊢ <;> tauto
    · rw [vout hS] at hx ⊢; exact hraw _ hw hS hx
lemma CF {H S g} (hg:Good H S g) {x y:ℕ→Bool} (h:∀ w, x w=true→y w=true) {w:ℕ} (hx:val S g x w=true):val S g y w=true:=
  crCut (B:=fun _=>False) hg (fun w _ _=>h w) (by simp) (Nat.le_refl _) (by simp) hx
lemma crRaw {n S g i} (hg:Good (2*n+2) S g) (hi:i∈Finset.range n) (b:Bool):CL b i∉S:=by
  intro h; have hz:=(hg _ h).1; have:=Finset.mem_range.mp hi
  cases b <;> simp [CL, lport, rport] at hz <;> omega
lemma CV {n S g} (hg:Good (2*n+2) S g):0∉S:=by intro h; have:=(hg _ h).1; omega
lemma crTwo {K:Finset ℕ} {i:ℕ} (hi:i∈K) (h3:3≤K.card):∃ j∈K, ∃ k∈K, j≠i∧k≠i∧j≠k:=by
  have hc:1 < (K.erase i).card:=by rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨j, hj, k, hk, hjk⟩:=Finset.one_lt_card.mp hc
  exact ⟨j, (Finset.mem_erase.mp hj).2, k, (Finset.mem_erase.mp hk).2, (Finset.mem_erase.mp hj).1, (Finset.mem_erase.mp hk).1, hjk⟩
lemma CJ {K M S g o i j} (hs:AY K M S g o) (hi:i∈K) (hj:j∈K) (hij:i≠j):o∈S:=by
  by_contra ho
  have hx:=CR (b:=false) hs hi hj hij
  rw [vout ho, crHit] at hx
  have a:=Cx hs hi; have b:=Cx hs hj
  rw [vout ho] at a b
  have aux (u:ℕ) (hu:point ∅ u u o=false):¬ (o=0∨o=CL false u∨o=CL true u):=fun h=>by have:=(Cu (b:=false)).2 h; simp_all
  have:=aux i a; have:=aux j b
  simp [CQ] at hx; tauto
lemma CP {n K M S g o i j} (hg:Good (2*n+2) S g) (hs:AY K M S g o) (hi:i∈M) (him:i∈K) (hin:i∈Finset.range n) (hj:j∈K) (hij:i≠j) (b:Bool):∃ t∈S, CM g t (CL b i):=by
  by_contra! h
  have hout:=CJ hs him hj hij
  have ho:o≠CL b i:=fun e=>crRaw hg hin b (e ▸ hout)
  have hz:=crCut (B:=fun w=>w=CL b i) hg (fun _ hw _=>Cr hi hw) (fun w hw _ _ hr=>False.elim (h w hw hr)) (Nat.le_refl o) ho (CR (b:=b) hs him hj hij)
  simp [Cx hs hj] at hz
lemma CC {n K M S g w p} (hg:Good (2*n+2) S g) (hw:w∈S) (hr:CM g w p) (hz:∀ u∈K, ∀ v∈K, val S g (point M u v) p=false):Alias K M S g w:=by
  obtain ⟨W, hf⟩:=CU hr
  obtain ⟨hp, hW⟩:=CD hg hw hf
  cases he:(g w).1
  · refine ⟨W, hW, fun u hu v hv=>?_⟩; simp [Cy hg hw hf, hz u hu v hv, he, bin]
  · refine ⟨p, hp, fun u hu v hv=>?_⟩; simp [Cy hg hw hf, hz u hu v hv, he, bin]
lemma Ct {n S g i w} {K M:Finset ℕ} (hg:Good (2*n+2) S g) (hin:i∈Finset.range n) (hw:w∈S) {b:Bool} (hr:CM g w (CL b i)):Alias (K.erase i) (M.erase i) S g w:=by
  apply CC hg hw hr
  intro u hu v hv; exact (vout (crRaw hg hin b)).trans (CB (Finset.mem_erase.mp hu).1 (Finset.mem_erase.mp hv).1)
lemma CA {S:Finset ℕ} {A:ℕ→Prop} {a b c d:ℕ} (ha:a∈S) (hb:b∈S) (hc:c∈S) (hd:d∈S) (hab:a≠b) (hac:a≠c) (had:a≠d) (hbc:b≠c) (hbd:b≠d) (hcd:c≠d) (aa:A a) (ab:A b) (ac:A c) (ad:A d):∃ F:Finset ℕ, F⊆S∧4≤F.card∧∀ w∈F, A w:=by
  refine ⟨{a,b,c,d}, ?_, ?_, ?_⟩
  · intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> assumption
  · simp [hab, hac, had, hbc, hbd, hcd]
  · intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> assumption
lemma CO {H K M S g t p W} (hg:Good H S g) (ht:t∈S) (hf:((g t).2.1=p∧(g t).2.2=W)∨((g t).2.1=W∧(g t).2.2=p)) (heq:∀ u∈K, ∀ v∈K, val S g (point M u v) p=val S g (point M u v) W):Alias K M S g t:=by
  refine ⟨W, (CD hg ht hf).2, fun u hu v hv=>?_⟩
  rw [Cy hg ht hf, heq u hu v hv]; cases (g t).1 <;> simp [bin]
lemma CK {n K S g t i} {M:Finset ℕ} (hg:Good (2*n+2) S g) (hin:i∈Finset.range n) (ht:t∈S) (hL:CM g t (CL false i)) (hR:CM g t (CL true i)):Alias K (M.erase i) S g t:=by
  obtain ⟨W, hf⟩:=CU hL
  have he:W=CL true i:=by unfold CM at hR; rcases hf with h | h <;> simp [h.1, h.2, crEq] at hR <;> exact hR
  subst W
  apply CO hg ht hf
  intro u hu v hv; rw [vout (crRaw hg hin false), vout (crRaw hg hin true)]
  apply Bool.eq_iff_iff.mpr; constructor <;> intro h <;> exact CE h (Cw _ i)
lemma Cz {n K M S g o i b t} (hg:Good (2*n+2) S g) (hs:AY K M S g o) (hi:i∈M) (him:i∈K) (hin:i∈Finset.range n) (honly:∀ w∈S, CM g w (CL b i)→w=t) {j} (hj:j∈K) (hij:i≠j):val S g (CI M b i j) t=true∧val S g (point ∅ j j) t=false:=by
  have ho:o≠CL b i:=fun e=>crRaw hg hin b (e ▸ CJ hs him hj hij)
  have hh:¬(val S g (CI M b i j) t=true→val S g (point ∅ j j) t=true):=by
    intro h
    have hz:=crCut (B:=fun w=>w=CL b i) hg (fun _ hw _=>Cr hi hw) (fun w hw _ _ hr=>honly w hw hr ▸ h) (Nat.le_refl o) ho (CR (b:=b) hs him hj hij)
    simp [Cx hs hj] at hz
  simpa using hh
lemma CN {n M S g t W i b j} (hg:Good (2*n+2) S g) (hi:i∈M) (honly:∀ w∈S, CM g w (CL b i)→w=t) (hlt:W < t) (hne:W≠CL b i) (hx:val S g (CI M b i j) W=true) (k:ℕ):val S g (CI (M.erase i) b k j) W=true:=by
  apply crCut (B:=fun w=>w=CL b i) hg _ _ (Nat.le_refl W) hne hx
  · intro w hw _ hp
    rw [crHit] at hp ⊢
    simp [CQ, hi, hw] at hp
    simp [CQ]
    grind
  · intro w hw hle _ hr
    have:=honly w hw hr; omega
lemma CH {g:Gates} {S:Finset ℕ} {i w:ℕ} (h:¬∃ w∈S, CM g w (CL false i)∧CM g w (CL true i)) (hw:w∈S) {b:Bool} (hp:CM g w (CL b i)):¬CM g w (CL (!b) i):=by
  intro hq; apply h; refine ⟨w, hw, ?_⟩; cases b <;> simp_all
lemma Cs {n K M S g o i b t W} (hK:K⊆Finset.range n) (hi:i∈M) (him:i∈K) (h3:3≤K.card)
    (hg:Good (2*n+2) S g) (hs:AY K M S g o) (hn:AN K S g)
    (ht:t∈S) (hp:CM g t (CL b i)) (honly:∀ w∈S, CM g w (CL b i)→w=t)
    (hnq:¬CM g t (CL (!b) i))
    (hf:((g t).2.1=CL b i∧(g t).2.2=W)∨((g t).2.1=W∧(g t).2.2=CL b i))
    (hop:(g t).1=true) (hW:W≠CL b i) (hd:val S g (point ∅ i i) W=false):
    ∃ F:Finset ℕ, F⊆S∧4≤F.card∧∀ w∈F, Alias (K.erase i) (M.erase i) S g w:=by
  have hin:=hK him
  have hlt:=(CD hg ht hf).2
  have raw:=crRaw hg hin b
  have qraw:=crRaw hg hin (!b)
  obtain ⟨j, hj, k, hk, hji, hki, hjk⟩:=crTwo him h3
  have hpos (a:ℕ) (ha:a∈K) (hia:i≠a):val S g (CI M b i a) W=true:=by
    have h:=(Cz hg hs hi him hin honly ha hia).1
    rw [Cy hg ht hf, hop] at h; exact (Bool.and_eq_true_iff.mp h).2
  have hgate:W∈S:=by
    by_contra h
    have a:=hpos j hj hji.symm; have c:=hpos k hk hki.symm
    rw [vout h] at a c hd
    have hjd:=(Cu (b:=b)).1 (Cr hi hW a)
    have hkd:=(Cu (b:=b)).1 (Cr hi hW c)
    have h0:W≠0:=fun e=>by simp [e, point] at hd
    rcases hjd with z | z | z <;> rcases hkd with y | y | y <;> first | exact h0 z | exact h0 y | exact hjk (crEq.mp (z.symm.trans y)).2
  have hOne (u:ℕ) (hu:u∈K.erase i) (v:ℕ) (hv:v∈K.erase i):val S g (point (M.erase i) u v) W=true:=by
    obtain ⟨hu', huK⟩:=Finset.mem_erase.mp hu
    obtain ⟨hv', hvK⟩:=Finset.mem_erase.mp hv
    cases b
    · exact CN hg hi honly hlt hW (hpos v hvK hv'.symm) u
    · exact CN hg hi honly hlt hW (hpos u huK hu'.symm) v
  have hAW:Alias (K.erase i) (M.erase i) S g W:=by
    refine ⟨0, ?_, fun u hu v hv=>?_⟩
    · have:=(hg W hgate).1; omega
    · simp [vout (CV hg), point, hOne u hu v hv]
  have hDark:Dark K S g t:=by
    intro a ha; rw [Cy hg ht hf, hop, vout raw]
    by_cases he:a=i
    · subst a; simp [hd, bin]
    · simp [CB he he, bin]
  have hDead (u:ℕ) (hu:u∈K.erase i) (v:ℕ) (hv:v∈K.erase i):val S g (point (M.erase i) u v) t=false:=by
    simp [Cy hg ht hf, hop, bin, vout raw, CB (Finset.mem_erase.mp hu).1 (Finset.mem_erase.mp hv).1]
  have hWq:¬CM g W (CL (!b) i):=by
    intro h; obtain ⟨V, hv⟩:=CU h
    cases he:(g W).1
    · simp [Cy hg hgate hv, he, bin, vout qraw, Cw] at hd
    · have hz:=hpos j hj hji.symm
      simp [Cy hg hgate hv, he, bin, vout qraw, crOff hi hji.symm] at hz
  have ho:o≠t:=by
    intro e; have hz:=hs j hj k hk
    simp [e, hjk, Cy hg ht hf, hop, bin, vout raw, CB hji hki] at hz
  have hor:o≠CL b i:=fun e=>raw (e ▸ CJ hs hj hk hjk)
  have hr:∃ a∈S, CM g a t∧¬CM g a (CL (!b) i):=by
    by_contra! h
    have hnDark (a:ℕ) (ha:a∈S) (hat:CM g a t):Dark K S g a:=by
      apply hn a ha; rcases hat with e | e
      · exact Or.inl (e ▸ hDark)
      · exact Or.inr (e ▸ hDark)
    have hz:=crCut (B:=fun w=>w=CL b i∨w=t) hg
      (fun _ hw _=>Cr hi (fun e=>hw (Or.inl e)))
      (d:=o) (x:=CI M b i j) (y:=point ∅ j j) (by
        intro a ha _ hao hr hx
        have hat:CM g a t:=by
          by_contra H
          have har:CM g a (CL b i):=by unfold CM at H ⊢; tauto
          exact hao (Or.inr (honly a ha har))
        have haq:=h a ha hat
        obtain ⟨V, hv⟩:=CU haq
        cases he:(g a).1
        · have hdi:=hnDark a ha hat i him
          simp [Cy hg ha hv, he, bin, vout qraw, Cw] at hdi
        · simp [Cy hg ha hv, he, bin, vout qraw, crOff hi hji.symm] at hx)
      (Nat.le_refl _) (not_or_intro hor ho) (CR (b:=b) hs him hj hji.symm)
    simp [Cx hs hj] at hz
  obtain ⟨a, ha, hat, haq⟩:=hr
  obtain ⟨d, hdS, hdq⟩:=CP hg hs hi him hin hj hji.symm (!b)
  have hta:t < a:=by obtain ⟨V, hv⟩:=CU hat; exact (CD hg ha hv).1
  exact CA hgate ht ha hdS (by omega) (by omega) (fun e=>hWq (e ▸ hdq)) (by omega) (fun e=>hnq (e ▸ hdq)) (fun e=>haq (e ▸ hdq)) hAW (Ct hg hin ht hp) (CC hg ha hat hDead) (Ct hg hin hdS hdq)
lemma CT {n K M S g o i b t} (hK:K⊆Finset.range n) (hi:i∈M) (him:i∈K) (h3:3≤K.card)
    (hg:Good (2*n+2) S g) (hs:AY K M S g o) (hn:AN K S g)
    (ht:t∈S) (hp:CM g t (CL b i)) (honly:∀ w∈S, CM g w (CL b i)→w=t)
    (hnq:¬CM g t (CL (!b) i)):
    (∃ w∈S, Alias K (M.erase i) S g w)∨∃ F:Finset ℕ, F⊆S∧4≤F.card∧∀ w∈F, Alias (K.erase i) (M.erase i) S g w:=by
  obtain ⟨W, hf⟩:=CU hp
  have hin:=hK him
  have raw:=crRaw hg hin b
  by_cases he:W=CL b i
  · exact Or.inl ⟨t, ht, CO hg ht hf (fun _ _ _ _=>congrArg _ he.symm)⟩
  have hsoft (hd:val S g (point ∅ i i) W=true) (u v:ℕ) (h:val S g (point (M.erase i) u v) (CL b i)=true):val S g (point (M.erase i) u v) W=true:=by
    rw [vout raw] at h; exact CF hg (fun _=>CE h) hd
  cases hop:(g t).1
  · have hnd:¬Dark K S g W:=by
      intro hd
      have hh:Dark K S g t:=by
        apply hn t ht; rcases hf with h | h
        · exact Or.inr (h.2 ▸ hd)
        · exact Or.inl (h.1 ▸ hd)
      have h:=hh i him
      simp [Cy hg ht hf, hop, bin, vout raw, Cw] at h
    unfold Dark at hnd; push Not at hnd
    obtain ⟨a, ha, hwa⟩:=hnd
    have e:a=i:=by
      by_contra h
      have hz:=(Cz hg hs hi him hin honly ha (Ne.symm h)).2
      simp [Cy hg ht hf, hop, bin, hwa] at hz
    subst a
    refine Or.inl ⟨t, ht, W, (CD hg ht hf).2, fun u hu v hv=>?_⟩
    rw [Cy hg ht hf, hop]
    have h:=hsoft (by simpa using hwa) u v
    cases e:val S g (point (M.erase i) u v) (CL b i) <;> simp_all [bin]
  · cases hd:val S g (point ∅ i i) W
    · exact Or.inr (Cs hK hi him h3 hg hs hn ht hp honly hnq hf hop he hd)
    · refine Or.inl ⟨t, ht, CL b i, (CD hg ht hf).1, fun u hu v hv=>?_⟩
      rw [Cy hg ht hf, hop]
      have h:=hsoft hd u v
      cases e:val S g (point (M.erase i) u v) (CL b i) <;> simp_all [bin]
lemma CS {n:ℕ} {K M S:Finset ℕ} {g:Gates} {o i:ℕ} (hK:K⊆Finset.range n) (hM:M⊆K) (hi:i∈M) (h3:3≤K.card) (hg:Good (2*n+2) S g) (hs:AY K M S g o) (hn:AN K S g):(∃ w∈S, Alias K (M.erase i) S g w)∨∃ F:Finset ℕ, F⊆S∧4≤F.card∧∀ w∈F, Alias (K.erase i) (M.erase i) S g w:=by
  have him:=hM hi
  have hin:=hK him
  by_cases hp:∃ w∈S, CM g w (CL false i)∧CM g w (CL true i)
  · obtain ⟨w, hw, hl, hr⟩:=hp
    exact Or.inl ⟨w, hw, CK hg hin hw hl hr⟩
  obtain ⟨j, hj, _, _, hji, _, _⟩:=crTwo him h3
  obtain ⟨a, ha, al⟩:=CP hg hs hi him hin hj hji.symm false
  obtain ⟨c, hc, cr⟩:=CP hg hs hi him hin hj hji.symm true
  by_cases au:∀ w∈S, CM g w (CL false i)→w=a
  · exact CT hK hi him h3 hg hs hn ha al au (CH hp ha al)
  by_cases cu:∀ w∈S, CM g w (CL true i)→w=c
  · exact CT hK hi him h3 hg hs hn hc cr cu (CH hp hc cr)
  push Not at au cu
  obtain ⟨b, hb, bl, hba⟩:=au
  obtain ⟨d, hd, dr, hdc⟩:=cu
  have dis:∀ x∈S, CM g x (CL false i)→∀ y, CM g y (CL true i)→x≠y:=by
    intro x hx hl y hr e; subst y; exact hp ⟨_, hx, hl, hr⟩
  exact Or.inr (CA ha hb hc hd hba.symm (dis a ha al c cr) (dis a ha al d dr) (dis b hb bl c cr) (dis b hb bl d dr) hdc.symm (Ct hg hin ha al) (Ct hg hin hb bl) (Ct hg hin hc cr) (Ct hg hin hd dr))
def BG (F:Finset ℕ) (r:ℕ→ℕ) (w:ℕ):ℕ:=
  if w∈F∧r w < w then BG F r (r w) else w
termination_by w
lemma BH (F:Finset ℕ) (r:ℕ→ℕ) (w:ℕ):BG F r w≤w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    rw [BG]
    split_ifs with hw
    · exact (ih _ hw.2).trans hw.2.le
    · rfl
lemma prune {H:ℕ} {K M S F:Finset ℕ} {g:Gates} {o:ℕ}
    (hg:Good H S g) (hs:AY K M S g o) (_hF:F⊆S) (ha:∀ w∈F, Alias K M S g w):
    ∃ h:Gates, ∃ p:ℕ, Good H (S \ F) h∧AY K M (S \ F) h p:=by
  classical
  let r (w:ℕ):=if hw:w∈F then (ha w hw).choose else w
  have hr w (hw:w∈F):r w < w∧∀ u∈K, ∀ v∈K,
      val S g (point M u v) w=val S g (point M u v) (r w):=by
    simpa only [r, dite_eq_left hw] using (ha w hw).choose_spec
  let d:=BG F r
  let h (w:ℕ):=((g w).1, d (g w).2.1, d (g w).2.2)
  have hh:Good H (S \ F) h:=by
    intro w hw
    have hw':=hg w (Finset.mem_sdiff.mp hw).1
    exact ⟨hw'.1, (BH ..).trans_lt hw'.2.1, (BH ..).trans_lt hw'.2.2⟩
  refine ⟨h, d o, hh, ?_⟩
  intro u hu v hv
  suffices ∀ w, val (S \ F) h (point M u v) (d w)=val S g (point M u v) w by
    rw [this, hs u hu v hv]
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    by_cases hf:w∈F
    · have he:d w=d (r w):=by rw [show d w=BG F r w from rfl, BG, ite_eq_left ⟨hf, (hr w hf).1⟩]
      rw [he, ih _ (hr w hf).1, (hr w hf).2 u hu v hv]
    · have he:d w=w:=by rw [show d w=BG F r w from rfl, BG, ite_eq_right (fun h=>hf h.1)]
      rw [he]
      by_cases hw:w∈S
      · rw [vin hh (Finset.mem_sdiff.mpr ⟨hw, hf⟩), vin hg hw]
        change bin _ (val _ _ _ (d _)) (val _ _ _ (d _))=_
        rw [ih _ (hg w hw).2.1, ih _ (hg w hw).2.2]
      · rw [vout hw, vout (fun (e:w∈S \ F)=>hw (Finset.mem_sdiff.mp e).1)]
lemma Bv {op a b c d:Bool} (ha:a=true→c=true) (hb:b=true→d=true):
    bin op a b=true→bin op c d=true:=by
  cases op <;> simp [bin] <;> tauto
lemma JH {H S g} (hg:Good H S g) {x y:ℕ→Bool} (hxy:∀ w, x w=true→y w=true):
    ∀ w, val S g x w=true→val S g y w=true:=by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    by_cases hw:w∈S
    · rw [vin hg hw, vin hg hw]
      exact Bv (ih _ (hg w hw).2.1) (ih _ (hg w hw).2.2)
    · simpa only [vout hw] using hxy w
lemma Hq {M:Finset ℕ} {i u v w:ℕ} (ht:point M u v w=true):
    point (M.erase i) u v w=true:=by
  simp [point] at ht ⊢
  tauto
lemma Ho (M:Finset ℕ) (i w:ℕ):point M i i w=point ∅ i i w:=by
  unfold point
  rw [decide_eq_decide]
  simp only [Finset.notMem_empty]
  tauto
lemma FY {H K M S g o} (hg:Good H S g) (hs:AY K M S g o) (i:ℕ):
    AY K (M.erase i) S g o:=by
  intro u hu v hv
  have h0:=hs u hu v hv
  by_cases huv:u=v
  · subst v
    simpa only [funext (Ho M u), funext (Ho (M.erase i) u)] using h0
  · simpa only [decide_eq_true huv] using JH hg (fun _=>Hq) o (by simpa [huv] using h0)
lemma Dj {H K M S g o} (hg:Good H S g) (hs:AY K M S g o) (i:ℕ):
    AY (K.erase i) (M.erase i) S g o:=by
  intro u hu v hv
  exact FY hg hs i u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv)
def plug (g:Gates) (z:ℕ) (t:Bool × ℕ × ℕ):Gates:=fun w=>if w=z then t else g w
lemma Hl {S H g} (hg:Good H S g) {z a b:ℕ} (hz:z∉S)
    (hzH:H≤z) (ha:a < z) (hb:b < z) (op:Bool):
    Good H (insert z S) (plug g z (op, a, b)):=by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · simpa [plug] using And.intro hzH (And.intro ha hb)
  · have hne:w≠z:=fun e=>hz (e ▸ hw)
    simpa [plug, hne] using hg w hw
lemma Hn {S H g} (hg:Good H S g) {z a b:ℕ} {op:Bool}
    (hg':Good H (insert z S) (plug g z (op,a,b))) (x:ℕ→Bool) (w:ℕ) (hw:w < z):
    val (insert z S) (plug g z (op,a,b)) x w=val S g x w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    have hn:=Nat.ne_of_lt hw
    by_cases h:w∈S
    · rw [vin hg' (Finset.mem_insert_of_mem h), vin hg h]
      simp only [plug, ite_eq_right hn]
      rw [ih _ (hg w h).2.1 ((hg w h).2.1.trans hw), ih _ (hg w h).2.2 ((hg w h).2.2.trans hw)]
    · rw [vout h, vout (by simp [hn,h]:w∉insert z S)]
lemma Hm {S H g} (hg:Good H S g) {z a b:ℕ} {op:Bool} (ha:a < z) (hb:b < z)
    (hg':Good H (insert z S) (plug g z (op,a,b))) (x:ℕ→Bool):
    val (insert z S) (plug g z (op,a,b)) x z=bin op (val S g x a) (val S g x b):=by
  rw [vin hg' (Finset.mem_insert_self ..)]
  simp only [plug, ite_true]
  rw [Hn hg hg' x a ha, Hn hg hg' x b hb]
lemma Hp (u v w:ℕ):point ∅ u v w=true↔
    w=0∨w=lport u∨w=rport u∨w=lport v∨w=rport v:=by
  simp only [point, decide_eq_true_eq, Finset.notMem_empty]
  tauto
lemma FJ (u v i:ℕ):point ∅ u v (lport i)=true↔i=u∨i=v:=by
  rw [Hp]
  unfold lport rport
  omega
def moved (H i j w:ℕ):=if w < H then
    if w=lport i∨w=rport i then 1 else if w=lport j∨w=rport j then H else w
  else w+1
lemma Gy {H i j w k:ℕ} (_hH:2≤H) (hk:H≤k) (hw:w < k):moved H i j w < k+1:=by
  unfold moved
  split_ifs <;> omega
lemma DI {n:ℕ} {K S:Finset ℕ} {i j o:ℕ} {g:Gates} (hK:K⊆Finset.range n)
    (hi:i∈K) (hj:j∈K) (hij:i≠j) (hg:Good (2*n+2) S g) (hs:AY (K.erase i) ∅ S g o):
    ∃ T:Finset ℕ, ∃ h:Gates, ∃ p:ℕ, Good (2*n+2) T h∧AY K ∅ T h p∧T.card≤S.card+3:=by
  classical
  let H:=2*n+2
  have li:lport i < H:=by have:=Finset.mem_range.mp (hK hi); dsimp [lport,H]; omega
  have lj:lport j < H:=by have:=Finset.mem_range.mp (hK hj); dsimp [lport,H]; omega
  let m:=moved H i j
  let T:=insert H (S.image Nat.succ)
  let h:Gates:=fun w=>if w=H then (false,lport i,lport j) else
    ((g (w-1)).1,m (g (w-1)).2.1,m (g (w-1)).2.2)
  have hp (w:ℕ) (hw:w < H):w∉T:=by
    intro hmem
    rcases Finset.mem_insert.mp hmem with e | hh
    · omega
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hh
    have:H≤k:=(hg k hk).1
    omega
  have hT:Good H T h:=by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simpa [h] using And.intro (le_refl H) (And.intro li lj)
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨hkg,ha,hb⟩:=hg k hk
    change H≤k at hkg
    have hne:k.succ≠H:=by omega
    simp only [h, ite_eq_right hne, Nat.succ_sub_one]
    exact ⟨by omega, Gy (by dsimp [H]; omega) hkg ha, Gy (by dsimp [H]; omega) hkg hb⟩
  let f (k:ℕ):=if k=i then j else k
  have fm {k:ℕ} (hk:k∈K):f k∈K.erase i:=by
    by_cases e:k=i <;> simp [f,e,Finset.mem_erase,hij.symm,hj,hk]
  have sim (u v:ℕ) (hu:u∈K) (hv:v∈K) (w:ℕ):
      val T h (point ∅ u v) (m w)=val S g (point ∅ (f u) (f v)) w:=by
    have un:=Finset.mem_range.mp (hK hu)
    have vn:=Finset.mem_range.mp (hK hv)
    have fun':=Finset.mem_range.mp (hK (Finset.mem_of_mem_erase (fm hu)))
    have fvn:=Finset.mem_range.mp (hK (Finset.mem_of_mem_erase (fm hv)))
    induction w using Nat.strong_induction_on with
    | ind w ih=>
      by_cases hw:w∈S
      · obtain ⟨hkg,ha,hb⟩:=hg w hw
        change H≤w at hkg
        have hm:m w=w+1:=by simp [m,moved, Nat.not_lt.mpr hkg]
        have hws:w+1∈T:=Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
        have hne:w+1≠H:=by omega
        rw [hm,vin hT hws,vin hg hw]
        simp only [h,ite_eq_right hne,Nat.add_sub_cancel]
        rw [ih _ ha, ih _ hb]
      · rw [vout hw]
        by_cases hx:w < H
        · by_cases h1:w=lport i∨w=rport i
          · have hm:m w=1:=by simp [m,moved,hx,h1]
            rw [hm,vout (hp _ (by dsimp [H]; omega)),Bool.eq_iff_iff,Hp,Hp]
            have hfi:=(Finset.mem_erase.mp (fm hu)).1
            have hfj:=(Finset.mem_erase.mp (fm hv)).1
            unfold lport rport at*
            omega
          · by_cases h2:w=lport j∨w=rport j
            · have hm:m w=H:=by simp [m,moved,hx,h1,h2]
              rw [hm,vin hT (Finset.mem_insert_self ..)]
              simp only [h,ite_eq_left rfl,bin,Bool.false_eq_true,ite_false]
              rw [vout (hp _ li),vout (hp _ lj),Bool.eq_iff_iff,Bool.or_eq_true,FJ,FJ,Hp]
              dsimp [f,lport,rport] at*
              split_ifs <;> omega
            · have hm:m w=w:=by simp [m,moved,hx,h1,h2]
              rw [hm,vout (hp _ hx),Bool.eq_iff_iff,Hp,Hp]
              unfold f
              split_ifs <;> grind
        · have hm:m w=w+1:=by simp [m,moved,hx]
          have ht:w+1∉T:=by
            intro he
            rcases Finset.mem_insert.mp he with he | he
            · omega
            obtain ⟨k,hk,hke⟩:=Finset.mem_image.mp he
            exact hw (Nat.succ.inj hke ▸ hk)
          rw [hm,vout ht,Bool.eq_iff_iff,Hp,Hp]
          dsimp [H,lport,rport] at*
          omega
  let z:=max (max (T.sup id) H) (m o)+1
  have zS:z∉T:=fun hz=>by have hle:z≤T.sup id:=Finset.le_sup (f:=id) hz; dsimp [z] at hle; omega
  have zH:H < z:=by dsimp [z]; omega
  have zo:m o < z:=by dsimp [z]; omega
  let h1:=plug h z (true,lport i,lport j)
  have hg1:Good H (insert z T) h1:=Hl hT zS zH.le (li.trans zH) (lj.trans zH) true
  have z1S:z+1∉insert z T:=by
    simp only [Finset.mem_insert,not_or]
    refine ⟨by omega, fun hz=>?_⟩
    have hle:z+1≤T.sup id:=Finset.le_sup (f:=id) hz
    dsimp [z] at hle
    omega
  let h2:=plug h1 (z+1) (false,z,m o)
  have hg2:Good H (insert (z+1) (insert z T)) h2:=Hl hg1 z1S (by omega) (by omega) (by omega) false
  refine ⟨_,h2,z+1,hg2,?_,?_⟩
  · intro u hu v hv
    rw [Hm hg1 (by omega) (by omega) hg2, Hm hT (li.trans zH) (lj.trans zH) hg1,
      vout (hp _ li),vout (hp _ lj),Hn hT hg1 _ _ zo,sim u v hu hv,hs _ (fm hu) _ (fm hv)]
    rw [Bool.eq_iff_iff]
    simp only [bin,ite_true,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.and_eq_true,FJ,decide_eq_true_eq]
    dsimp [f]
    split_ifs <;> omega
  · have ht:=Finset.card_insert_le H (S.image Nat.succ)
    have ht':=Finset.card_image_le (s:=S) (f:=Nat.succ)
    rw [Finset.card_insert_of_notMem z1S, Finset.card_insert_of_notMem zS]
    change (insert H (S.image Nat.succ)).card+1+1≤_
    omega
lemma EM {H S g} (hg:Good H S g) (k:ℕ) (T:Finset ℕ) (hT:∀ w∈T, w∈S→w < k):
    ∃ U:Finset ℕ, U.card≤T.card+((Finset.range k).filter (·∈S)).card∧
      ∀ x y:ℕ→Bool, (∀ w∈U, x w=true→y w=true)→
        ∀ w∈T, val S g x w=true→val S g y w=true:=by
  classical
  induction k generalizing T with
  | zero=>
    refine ⟨T,by simp,?_⟩
    intro x y hxy w hw
    have hn:w∉S:=fun e=>Nat.not_lt_zero _ (hT w hw e)
    simpa only [vout hn] using hxy w hw
  | succ k ih=>
    have step:((Finset.range k).filter (·∈S)).card≤((Finset.range (k+1)).filter (·∈S)).card:=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    by_cases h:k∈T∧k∈S
    · obtain ⟨hkt,hks⟩:=h
      let a:=(g k).2.1
      let b:=(g k).2.2
      let T':=insert a (insert b (T.erase k))
      have ha:a < k:=(hg k hks).2.1
      have hb:b < k:=(hg k hks).2.2
      obtain ⟨U,hU,hs⟩:=ih T' (by
        intro w hw hwS
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ha
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hb
        have h':=Finset.mem_erase.mp hw
        have:=hT w h'.2 hwS
        omega)
      refine ⟨U,?_,?_⟩
      · have c1:=Finset.card_insert_le a (insert b (T.erase k))
        have c2:=Finset.card_insert_le b (T.erase k)
        have c3:=Finset.card_erase_add_one hkt
        change U.card≤(insert a (insert b (T.erase k))).card+_ at hU
        rw [Finset.range_add_one,Finset.filter_insert]
        have eh:k∉(Finset.range k).filter (·∈S):=by simp
        rw [ite_eq_left hks,Finset.card_insert_of_notMem eh]
        omega
      · intro x y hxy w hw
        by_cases he:w=k
        · subst w
          rw [vin hg hks,vin hg hks]
          exact Bv (hs x y hxy a (Finset.mem_insert_self ..))
            (hs x y hxy b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
        · exact hs x y hxy w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hw⟩)))
    · obtain ⟨U,hU,hs⟩:=ih T (by
        intro w hw hws
        have:=hT w hw hws
        have hne:w≠k:=fun e=>h ⟨e ▸ hw, e ▸ hws⟩
        omega)
      exact ⟨U,by omega,hs⟩
lemma Fm {H:ℕ} {K M S:Finset ℕ} {g:Gates} {o:ℕ} (hk:2≤K.card)
    (hm:M⊆K) (hg:Good H S g) (hs:AY K M S g o):
    K.card+M.card≤S.card+1:=by
  classical
  obtain ⟨U,hu,hsup⟩:=EM hg (o+1) {o} (by simp)
  have cc:U.card≤S.card+1:=by
    have:((Finset.range (o+1)).filter (·∈S)).card≤S.card:=
      Finset.card_le_card fun k h=>(Finset.mem_filter.mp h).2
    simp only [Finset.card_singleton] at hu
    omega
  have wit (i j:ℕ) (hi:i∈K) (hj:j∈K) (hne:i≠j):
      (∃ w∈U, w=lport i∨(i∉M∧w=rport i))∧
      (∃ w∈U, w=rport i∨(i∉M∧w=lport i)):=by
    have left_bad (a b:ℕ) (ha:a∈K) (hb:b∈K) (hab:a≠b):
        ∃ w∈U, point M a b w=true∧point M j j w=false:=by
      by_contra! hn
      have ff:=hsup (point M a b) (point M j j) (by
        intro w hw ht
        simpa using hn w hw ht) o (Finset.mem_singleton_self o) (by rw [hs a ha b hb]; simp [hab])
      simp [hs j hj j hj] at ff
    constructor
    · obtain ⟨w,hw,h1,h2⟩:=left_bad i j hi hj hne
      refine ⟨w,hw,?_⟩
      simp [point] at h1 h2
      tauto
    · obtain ⟨w,hw,h1,h2⟩:=left_bad j i hj hi hne.symm
      refine ⟨w,hw,?_⟩
      simp [point] at h1 h2
      tauto
  let f (i:ℕ):=if lport i∈U then lport i else rport i
  have grab (i:ℕ) (hi:i∈K):f i∈U∧(i∈M→lport i∈U∧rport i∈U):=by
    obtain ⟨j,hj⟩:=Finset.card_pos.mp (show 0 < (K.erase i).card by have:=Finset.card_erase_add_one hi; omega)
    obtain ⟨h1,h2⟩:=wit i j hi (Finset.mem_of_mem_erase hj) (Finset.mem_erase.mp hj).1.symm
    obtain ⟨a,ha,ha'⟩:=h1
    obtain ⟨b,hb,hb'⟩:=h2
    dsimp only [f]
    split_ifs <;> grind
  have fits:K.image f∪M.image rport⊆U:=by
    intro w hw
    rcases Finset.mem_union.mp hw with hl | hr
    · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hl
      exact (grab i hi).1
    · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hr
      exact ((grab i (hm hi)).2 hi).2
  have dis:Disjoint (K.image f) (M.image rport):=by
    rw [Finset.disjoint_left]
    rintro _ hw hl
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨j,hj,he⟩:=Finset.mem_image.mp hl
    have hj':=((grab j (hm hj)).2 hj).1
    dsimp only [f] at he
    split_ifs at he with h
    · unfold lport rport at he
      omega
    · have:j=i:=by unfold rport at he; omega
      subst j
      exact h hj'
  have inj:Function.Injective f:=by
    intro i j he
    dsimp only [f] at he
    split_ifs at he <;> unfold lport rport at*<;> omega
  have inj':Function.Injective rport:=by intro i j he; unfold rport at he; omega
  have ct:=Finset.card_le_card fits
  rw [Finset.card_union_of_disjoint dis, Finset.card_image_of_injective _ inj,Finset.card_image_of_injective _ inj'] at ct
  omega
lemma Bs {n:ℕ} {K M S:Finset ℕ} {g:Gates} {o:ℕ}
    (hK:K⊆Finset.range n) (hm:M⊆K) (hk:K.card=2)
    (hg:Good (2*n+2) S g) (hs:AY K M S g o):
    ∃ T:Finset ℕ, ∃ h:Gates, ∃ p:ℕ, Good (2*n+2) T h∧AY K ∅ T h p∧T.card+M.card≤S.card:=by
  have cb:=Fm (by omega:2≤K.card) hm hg hs
  obtain ⟨i,j,hij,hpair⟩:=Finset.card_eq_two.mp hk
  have hi:i < n:=Finset.mem_range.mp (hK (by simp [hpair]))
  have hj:j < n:=Finset.mem_range.mp (hK (by simp [hpair]))
  let H:=2*n+2
  let h:Gates:=fun _=>(true,lport i,lport j)
  have li:lport i < H:=by dsimp [lport,H]; omega
  have lj:lport j < H:=by dsimp [lport,H]; omega
  have hgood:Good H {H} h:=by
    intro w hw
    obtain rfl:=Finset.mem_singleton.mp hw
    exact ⟨le_rfl,li,lj⟩
  refine ⟨{H},h,H,hgood,?_,by simp only [Finset.card_singleton]; omega⟩
  intro u hu v hv
  rw [vin hgood (Finset.mem_singleton_self H)]
  change bin true (val {H} h _ (lport i)) (val {H} h _ (lport j))=_
  rw [vout (by simpa using li.ne:lport i∉({H}:Finset ℕ)), vout (by simpa using lj.ne:lport j∉({H}:Finset ℕ)),Bool.eq_iff_iff]
  simp only [bin,ite_true,Bool.and_eq_true,FJ,decide_eq_true_eq]
  simp only [hpair,Finset.mem_insert,Finset.mem_singleton] at hu hv
  omega
lemma Dk {n:ℕ} {K M S:Finset ℕ} {g:Gates} {o:ℕ}
    (hK:K⊆Finset.range n) (hm:M⊆K) (hk:2≤K.card)
    (hg:Good (2*n+2) S g) (hs:AY K M S g o):
    ∃ T:Finset ℕ, ∃ h:Gates, ∃ p:ℕ, Good (2*n+2) T h∧AY K ∅ T h p∧T.card+M.card≤S.card:=by
  classical
  generalize hc:M.card=c
  induction c using Nat.strong_induction_on generalizing K M S g o with
  | ind c ih=>
    by_cases h0:M=∅
    · subst M
      exact ⟨S,g,o,hg,hs,by simp [← hc]⟩
    by_cases hk2:K.card=2
    · simpa only [← hc] using Bs hK hm hk2 hg hs
    have hk3:3≤K.card:=by omega
    obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr h0
    have cm:=Finset.card_erase_add_one hi
    have ck:=Finset.card_erase_add_one (hm hi)
    have clt:(M.erase i).card < c:=by omega
    obtain ⟨N,d,q,hd,hq,hn,cs⟩:=GQ hg hs
    rcases CS hK hm hi hk3 hd hq hn with ⟨w,hw,ha⟩ | ⟨F,hF,cf,ha⟩
    · have hf:{w}⊆N:=Finset.singleton_subset_iff.mpr hw
      obtain ⟨d',q',hd',hq'⟩:=prune hd (FY hd hq i) hf (by simpa using ha)
      obtain ⟨T,h,p,ht,hp,ct⟩:=ih _ clt hK ((Finset.erase_subset i M).trans hm) hk hd' hq' rfl
      have ce:=Finset.card_sdiff_add_card_eq_card hf
      simp only [Finset.card_singleton] at ce
      exact ⟨T,h,p,ht,hp,by omega⟩
    · obtain ⟨d',q',hd',hq'⟩:=prune hd (Dj hd hq i) hF ha
      have hkm:K.erase i⊆Finset.range n:=(Finset.erase_subset i K).trans hK
      have hmm:M.erase i⊆K.erase i:=Finset.erase_subset_erase i hm
      obtain ⟨T,h,p,ht,hp,ct⟩:=ih _ clt hkm hmm (by omega) hd' hq' rfl
      obtain ⟨j,hj⟩:=Finset.card_pos.mp (show 0 < (K.erase i).card by omega)
      obtain ⟨T',h',p',ht',hp',ct'⟩:=DI hK (hm hi) (Finset.mem_of_mem_erase hj) (Finset.mem_erase.mp hj).1.symm ht hp
      have ce:=Finset.card_sdiff_add_card_eq_card hF
      exact ⟨T',h',p',ht',hp',by omega⟩
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def ioRun (gs:List Gate) (x:List Bool):List Bool:=
  gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) x
lemma FD (gs:List Gate) (g:Gate) (x:List Bool):
    ioRun (gs++[g]) x=ioRun gs x++[g.op.eval (g.inputs.map fun i=>(ioRun gs x).getD i false)]:=by
  simp [ioRun, List.foldl_append]
lemma ioLen (gs:List Gate) (x:List Bool):(ioRun gs x).length=x.length+gs.length:=by
  induction gs using List.reverseRecOn with
  | nil=>simp [ioRun]
  | append_singleton gs g ih=>rw [FD]; simp [ih]; omega
lemma ioGet (l:List Bool) (b:Bool) (t:ℕ) (h:t < l.length):
    (l++[b]).getD t false=l.getD t false:=by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
lemma Fv (l:List Bool) (b:Bool):(l++[b]).getD l.length false=b:=by
  simp [List.getD_eq_getElem?_getD]
lemma FB (gs hs:List Gate) (x:List Bool) (i:ℕ) (hi:i < x.length+gs.length):
    (ioRun (gs++hs) x).getD i false=(ioRun gs x).getD i false:=by
  induction hs using List.reverseRecOn with
  | nil=>simp
  | append_singleton hs g ih=>
    rw [← List.append_assoc, FD, ioGet _ _ _ (by rw [ioLen, List.length_append]; omega), ih]
lemma Fu (gs:List Gate) (x:List Bool) (i:ℕ) (hi:i < x.length):
    (ioRun gs x).getD i false=x.getD i false:=by
  simpa [ioRun] using FB [] gs x i (by simpa using hi)
lemma Ft (gs:List Gate) (x:List Bool):∀ (j:ℕ) (hj:j < gs.length),
    (ioRun gs x).getD (x.length+j) false=gs[j].op.eval (gs[j].inputs.map fun i=>
      if i < x.length+j then (ioRun gs x).getD i false else false):=by
  induction gs using List.reverseRecOn with
  | nil=>intro j hj; simp at hj
  | append_singleton gs g ih=>
    intro j hj
    have hlen:=ioLen gs x
    have same (k:ℕ) (hk:k≤gs.length) (l:List ℕ):
        (l.map fun i=>if i < x.length+k then (ioRun (gs++[g]) x).getD i false else false)=
        l.map fun i=>if i < x.length+k then (ioRun gs x).getD i false else false:=by
      refine List.map_congr_left fun i _=>?_
      split_ifs with h
      · exact FB gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), FB gs [g] x _ (by omega)]
      exact ih j h
    · have hjj:j=gs.length:=by simp at hj; omega
      subst hjj
      have hg:(gs++[g])[gs.length]=g:=by simp
      rw [hg, same _ le_rfl, FD, ← hlen, Fv]
      congr 1
      refine List.map_congr_left fun i _=>?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
def FE (n j i:ℕ):=if i < n then lport i else if i < 2*n then rport (i-n)
  else if i < 2*n+j then i+2 else 1
lemma FF (n j i:ℕ):FE n j i < 2*n+2+j:=by
  unfold FE lport rport; split_ifs <;> omega
def ioArg (n j k:ℕ) (b:Bool) (l:List ℕ):=
  (l[k]?.map (FE n j)).getD (if b then 0 else 1)
lemma Fn (n j k:ℕ) (b:Bool) (l:List ℕ):ioArg n j k b l < 2*n+2+j:=by
  unfold ioArg
  cases l[k]? with
  | none=>cases b <;> simp; omega
  | some i=>exact FF n j i
def FA (n j:ℕ) (q:Gate):Bool × ℕ × ℕ:=
  let b:=match q.op with | .and=>true | _=>false
  (b, ioArg n j 0 b q.inputs, ioArg n j 1 b q.inputs)
lemma Fz (n j:ℕ) (q:Gate) (V R:ℕ→Bool) (h0:V 0=true) (h1:V 1=false)
    (hv:∀ i, V (FE n j i)=R i) (hop:q.op=GateOp.and∨q.op=GateOp.or)
    (hq:q.inputs.length≤2):
    bin (FA n j q).1 (V (FA n j q).2.1) (V (FA n j q).2.2)=q.op.eval (q.inputs.map R):=by
  rcases q with ⟨op,l⟩
  change op=_∨op=_ at hop
  change l.length≤2 at hq
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> rcases hop with rfl | rfl <;>
    simp_all [FA, ioArg, bin, GateOp.eval]
lemma Fs {n s:ℕ} (hn:2≤n)
    (hr:RepSizeAtMost (fun u v:Fin n=>decide (u≠v)) s):
    ∃ S:Finset ℕ, ∃ g:Gates, ∃ o:ℕ, Good (2*n+2) S g∧
      AY (Finset.range n) (Finset.range n) S g o∧S.card≤ s:=by
  obtain ⟨C, hC, hc, hrep⟩:=hr
  let H:=2*n+2
  let S:=Finset.Ico H (H+C.gates.length)
  let g:Gates:=fun w=>if h:w-H < C.gates.length then FA n (w-H) C.gates[w-H] else (false,0,0)
  have good:Good H S g:=by
    intro w hw
    obtain ⟨ha,hb⟩:=Finset.mem_Ico.mp hw
    have hj:w-H < C.gates.length:=by omega
    simp only [g, dite_eq_left hj, FA]
    have h:2*n+2+(w-H)=w:=by dsimp [H] at ha ⊢; omega
    exact ⟨ha, (Fn _ _ _ _ _).trans_le h.le, (Fn _ _ _ _ _).trans_le h.le⟩
  refine ⟨S, g, FE n C.gates.length C.output, good, ?_, by simpa [S, Circuit.size] using hc⟩
  intro u hu v hv
  have hu':=Finset.mem_range.mp hu
  have hv':=Finset.mem_range.mp hv
  let U:Fin n:=⟨u,hu'⟩
  let V:Fin n:=⟨v,hv'⟩
  let x:=oneEach U V
  let p:=point (Finset.range n) u v
  have px (w:ℕ):p w=decide (w=0∨w=lport u∨w=rport v):=by simp [p,point,hu,hv]
  have xl:x.length=2*n:=by simp [x,oneEach]; omega
  have lower (w:ℕ) (hw:w < H):val S g p w=p w:=vout (by simp [S, not_le.mpr hw])
  have h0:val S g p 0=true:=by rw [lower 0 (by dsimp [H]; omega),px]; simp
  have h1:val S g p 1=false:=by rw [lower 1 (by dsimp [H]; omega),px]; simp [lport,rport]
  have simw:∀ w, val S g p (FE n C.gates.length w)=(ioRun C.gates x).getD w false:=by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih=>
      by_cases hin:w < 2*n
      · have hwin:w < x.length:=by omega
        rw [Fu C.gates x w hwin]
        simp only [x,oneEach] at hwin ⊢
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwin]
        simp only [Option.getD_some]
        by_cases hl:w < n
        · rw [FE, ite_eq_left hl, lower _ (by dsimp [H,lport]; omega), px]
          have hw':w < (List.ofFn fun i:Fin n=>decide (i=U)).length:=by simpa using hl
          rw [List.getElem_append_left hw']
          simp only [List.getElem_ofFn]
          rw [decide_eq_decide]
          simp only [lport,rport,Fin.ext_iff,U]
          omega
        · rw [FE, ite_eq_right hl, ite_eq_left hin, lower _ (by dsimp [H,rport]; omega), px]
          have hw':¬ w < (List.ofFn fun i:Fin n=>decide (i=U)).length:=by simpa using hl
          rw [List.getElem_append_right (Nat.le_of_not_gt hw')]
          simp only [List.getElem_ofFn]
          rw [decide_eq_decide]
          simp only [List.length_ofFn,lport,rport,Fin.ext_iff,V]
          omega
      · by_cases hw:w < 2*n+C.gates.length
        · let j:=w-2*n
          have hj:j < C.gates.length:=by dsimp [j]; omega
          have hwj:2*n+j=w:=by dsimp [j]; omega
          have hsub:w+2-H=j:=by dsimp [H,j]; omega
          have hgp:g (w+2)=FA n j C.gates[j]:=by simp [g,hsub,hj]
          have hwm:w+2∈S:=by simp [S,H]; omega
          rw [FE, ite_eq_right (by omega), ite_eq_right hin, ite_eq_left hw, vin good hwm, hgp]
          have hg:=Ft C.gates x j hj
          rw [xl, hwj] at hg
          rw [hg]
          apply Fz _ _ _ _ _ h0 h1 _ (by simpa using (hC _ (List.getElem_mem hj)).1) (hC _ (List.getElem_mem hj)).2
          intro i
          split_ifs with h
          · rw [← ih i h]; congr 1; unfold FE; split_ifs <;> omega
          · have e:FE n j i=1:=by unfold FE; split_ifs <;> omega
            rw [e,h1]
        · rw [FE, ite_eq_right (by omega), ite_eq_right hin, ite_eq_right hw, h1,
            List.getD_eq_default _ _ (by rw [ioLen,xl]; omega)]
  rw [simw]
  change C.eval (oneEach U V)=_
  simpa [U,V,Fin.ext_iff] using hrep U V
def ioRv (x:List Bool):Bool ⊕ ℕ→Bool
  | .inl b=>b
  | .inr i=>x.getD i false
def FC (n w:ℕ):Bool ⊕ ℕ:=
  if w=0 then .inl true else if 2≤w∧(w-2)/2 < n then .inr ((w-2)/2) else .inl false
def Fo {n:ℕ} (x:Fin n→Bool) (w:ℕ):=ioRv (List.ofFn x) (FC n w)
def ioOK (q:Gate):=(q.op=GateOp.and∨q.op=GateOp.or)∧q.inputs.length≤2
lemma Fr (n:ℕ) (hs:List Gate) (op:Bool) (a b:Bool ⊕ ℕ):
    ∃ (e:List Gate) (r:Bool ⊕ ℕ), (∀ q∈e, ioOK q)∧e.length≤1∧
      ((∀ t, a=.inr t→t < n+hs.length)→(∀ t, b=.inr t→t < n+hs.length)→
        ∀ t, r=.inr t→t < n+hs.length+e.length)∧
      ∀ x:Fin n→Bool, ioRv (ioRun (hs++e) (List.ofFn x)) r=
        bin op (ioRv (ioRun hs (List.ofFn x)) a) (ioRv (ioRun hs (List.ofFn x)) b):=by
  rcases a with c | i
  · refine ⟨[], if c=op then b else .inl c, by simp, by simp, ?_, ?_⟩
    · cases op <;> cases c <;> simp
    · cases op <;> cases c <;> simp [ioRv,bin]
  · rcases b with d | j
    · refine ⟨[], if d=op then .inr i else .inl d, by simp, by simp, ?_, ?_⟩
      · cases op <;> cases d <;> simp
      · cases op <;> cases d <;> simp [ioRv,bin]
    · let q:Gate:=⟨if op then GateOp.and else GateOp.or, [i,j]⟩
      refine ⟨[q], .inr (n+hs.length), by cases op <;> simp [q,ioOK], by simp, by simp, ?_⟩
      intro x
      have hl:(ioRun hs (List.ofFn x)).length=n+hs.length:=by simp [ioLen]
      simp only [ioRv]
      rw [FD, ← hl, Fv]
      cases op <;> simp [q,bin,GateOp.eval]
lemma Fq {n H:ℕ} {S:Finset ℕ} {g:Gates} (hg:Good H S g) (k:ℕ):
    ∃ (hs:List Gate) (m:ℕ→Bool ⊕ ℕ), (∀ q∈hs, ioOK q)∧
      hs.length≤(S.filter (· < k)).card∧
      (∀ w < k, ∀ t, m w=.inr t→t < n+hs.length)∧
      ∀ w < k, ∀ x:Fin n→Bool, ioRv (ioRun hs (List.ofFn x)) (m w)=val S g (Fo x) w:=by
  induction k with
  | zero=>exact ⟨[], fun _=>.inl false, by simp, by simp, by simp, by simp⟩
  | succ k ih=>
    obtain ⟨hs,m,hok,hlen,hb,he⟩:=ih
    have step:∃ (e:List Gate) (r:Bool ⊕ ℕ), (∀ q∈e, ioOK q)∧
        hs.length+e.length≤(S.filter (· < k+1)).card∧
        (∀ t, r=.inr t→t < n+hs.length+e.length)∧
        ∀ x:Fin n→Bool, ioRv (ioRun (hs++e) (List.ofFn x)) r=val S g (Fo x) k:=by
      by_cases hk:k∈S
      · have ha:=(hg k hk).2
        obtain ⟨e,r,h1,h2,h3,h4⟩:=Fr n hs (g k).1 (m (g k).2.1) (m (g k).2.2)
        have hf:S.filter (· < k+1)=insert k (S.filter (· < k)):=by
          ext i
          by_cases heq:i=k
          · subst i; simp [hk]
          · simp only [Finset.mem_filter, Finset.mem_insert, heq, false_or]
            rw [show i < k+1↔i < k by omega]
        refine ⟨e,r,h1,?_, h3 (hb _ ha.1) (hb _ ha.2), ?_⟩
        · rw [hf,Finset.card_insert_of_notMem (by simp)]; omega
        · intro x; rw [h4,he _ ha.1,he _ ha.2,vin hg hk]
      · refine ⟨[], FC n k, by simp, ?_, ?_, ?_⟩
        · simp only [List.length_nil,Nat.add_zero]
          apply hlen.trans (Finset.card_le_card ?_)
          intro i hi
          obtain ⟨him,hik⟩:=Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨him, by omega⟩
        · intro t ht
          unfold FC at ht
          split_ifs at ht with h z
          cases ht; simp; omega
        · intro x
          rw [List.append_nil,vout hk]
          unfold Fo FC
          split_ifs with h z
          · rfl
          · exact Fu _ _ _ (by simpa using z.2)
          · rfl
    obtain ⟨e,r,hq,hl,hr,hev⟩:=step
    refine ⟨hs++e,Function.update m k r,fun q h=>(List.mem_append.mp h).elim (hok q) (hq q),
      by simpa using hl, ?_, ?_⟩
    · intro w hw t ht
      by_cases h:w=k
      · subst w; simpa [Function.update_self,List.length_append,Nat.add_assoc] using hr t (by simpa using ht)
      · rw [Function.update_of_ne h] at ht
        have:=hb w (by omega) t ht
        rw [List.length_append]; omega
    · intro w hw x
      by_cases h:w=k
      · subst w; simpa using hev x
      · rw [Function.update_of_ne h, ← he w (by omega) x]
        cases hmw:m w with
        | inl b=>rfl
        | inr t=>exact FB _ _ _ _ (by simpa using hb w (by omega) t hmw)
lemma Fx {a b c d:Bool} (op:Bool) (h1:a≤c) (h2:b≤d):
    bin op a b≤bin op c d:=by
  cases op <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [bin]
lemma Fw {H:ℕ} {S:Finset ℕ} {g:Gates} (hg:Good H S g) {a b:ℕ→Bool}
    (h:∀ i, a i≤b i) (w:ℕ):val S g a w≤val S g b w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    by_cases hw:w∈S
    · rw [vin hg hw,vin hg hw]
      exact Fx _ (ih _ (hg _ hw).2.1) (ih _ (hg _ hw).2.2)
    · simpa [vout hw] using h w
def ioPt {n:ℕ} (a b i:Fin n):=decide (i=a∨i=b)
lemma Fy {n:ℕ} (a b:Fin n):Fo (ioPt a b)=point ∅ a b:=by
  funext w
  unfold Fo FC
  split_ifs with h h
  · simp [ioRv,point,h]
  · have hi:(w-2)/2 < (List.ofFn (ioPt a b)).length:=by simpa using h.2
    simp only [ioRv,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,
      List.getElem_ofFn,ioPt,Fin.ext_iff,point,Finset.notMem_empty,not_false_eq_true,true_and,decide_eq_decide,lport,rport]
    omega
  · simp only [ioRv,point,lport,rport,Finset.notMem_empty,not_false_eq_true,true_and]
    symm
    apply decide_eq_false
    have:=a.isLt; have:=b.isLt; omega
lemma Fp {n:ℕ} {x y:Fin n→Bool} (h:∀ i, x i≤y i) (w:ℕ):Fo x w≤Fo y w:=by
  unfold Fo FC
  split_ifs with h0 hi
  · exact le_rfl
  · have h₁:(w-2)/2 < (List.ofFn x).length:=by simpa using hi.2
    have h₂:(w-2)/2 < (List.ofFn y).length:=by simpa using hi.2
    simpa only [ioRv,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h₁,List.getElem?_eq_getElem h₂,
      Option.getD_some,List.getElem_ofFn] using h ⟨(w-2)/2,hi.2⟩
  · exact le_rfl
lemma ioTo {n:ℕ} (hn:2≤n) {S:Finset ℕ} {g:Gates} {o:ℕ}
    (hg:Good (2*n+2) S g) (hs:AY (Finset.range n) ∅ S g o):
    ∃ C:Circuit, Monotone2 C∧C.size≤S.card∧
      (∀ x:Fin n→Bool, (List.ofFn x).count true=2→C.eval (List.ofFn x)=true)∧
      (∀ x:Fin n→Bool, (List.ofFn x).count true≤1→C.eval (List.ofFn x)=false):=by
  classical
  have pair (a b:Fin n):val S g (Fo (ioPt a b)) o=decide (a≠b):=by
    rw [Fy]
    simpa [Fin.ext_iff] using hs a (Finset.mem_range.mpr a.isLt) b (Finset.mem_range.mpr b.isLt)
  obtain ⟨qs,m,hok,hlen,_,he⟩:=Fq (n:=n) hg (o+1)
  have ev:=he o (by omega)
  let a:Fin n:=⟨0,by omega⟩
  let b:Fin n:=⟨1,by omega⟩
  have ab:a≠b:=by simp [a,b]
  cases hm:m o with
  | inl c=>
    have v0:=ev (ioPt a a)
    have v1:=ev (ioPt a b)
    simp [hm,ioRv,pair,ab] at v0 v1
    simp_all
  | inr t=>
    let C:Circuit:=⟨qs,t⟩
    have hval (x:Fin n→Bool):C.eval (List.ofFn x)=val S g (Fo x) o:=by
      simpa [hm,ioRv,C,Circuit.eval,Circuit.wires,ioRun] using ev x
    refine ⟨C,fun q hq=>⟨by simpa using (hok q hq).1,(hok q hq).2⟩,
      hlen.trans (Finset.card_le_card (Finset.filter_subset _ _)), ?_, ?_⟩
    · intro x hx
      rw [List.count_ofFn] at hx
      obtain ⟨i,j,hij,heq⟩:=Finset.card_eq_two.mp hx
      have ex:x=ioPt i j:=by
        funext k
        have hk:=Finset.ext_iff.mp heq k
        simp at hk
        cases hb:x k <;> simp_all [ioPt]
      rw [ex,hval,pair]; simp [hij]
    · intro x hx
      rw [List.count_ofFn] at hx
      let _:Nonempty (Fin n):=⟨a⟩
      obtain ⟨i,hi⟩:=Finset.card_le_one_iff_subset_singleton.mp hx
      have bound (j:Fin n):x j≤ ioPt i i j:=by
        cases hj:x j
        · simp
        · have eq:j=i:=by simpa using hi (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
          simp [ioPt,eq]
      have h:=Fw hg (Fp bound) o
      rw [pair] at h
      rw [hval]
      exact le_antisymm (by simpa using h) (Bool.false_le _)
end Ae
lemma Ae:∀ n s:ℕ, 2≤n→PEqualNP.Represents.RepSizeAtMost (fun u v:Fin n=>decide (u≠v)) s→∃ C:PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C∧C.size+n≤ s∧(∀ x:Fin n→Bool, (List.ofFn x).count true=2→C.eval (List.ofFn x)=true)∧(∀ x:Fin n→Bool, (List.ofFn x).count true≤1→C.eval (List.ofFn x)=false):=by
  intro n s hn hr
  obtain ⟨S,g,o,hg,hs,cs⟩:=Ae.Fs hn hr
  obtain ⟨T,h,p,ht,hp,ct⟩:=Ae.Dk (n:=n)
    (K:=Finset.range n) (M:=Finset.range n) (fun _ h=>h) (fun _ h=>h) (by simpa using hn) hg hs
  obtain ⟨C,hC,hsize,hpos,hneg⟩:=Ae.ioTo hn ht hp
  simp only [Finset.card_range] at ct
  exact ⟨C,hC,by omega,hpos,hneg⟩
namespace Aj
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def run (gs:List Gate) (x:List Bool):List Bool:=
  gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) x
lemma Il (gs:List Gate) (g:Gate) (x:List Bool):
    run (gs++[g]) x=run gs x++[g.op.eval (g.inputs.map fun i=>(run gs x).getD i false)]:=by
  simp [run, List.foldl_append]
lemma run_length (gs:List Gate) (x:List Bool):(run gs x).length=x.length+gs.length:=by
  induction gs using List.reverseRecOn with
  | nil=>simp [run]
  | append_singleton gs g ih=>rw [Il]; simp [ih]; omega
lemma Fh (l:List Bool) (b:Bool) (t:ℕ) (h:t < l.length):
    (l++[b]).getD t false=l.getD t false:=by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
lemma Ff (l:List Bool) (b:Bool):(l++[b]).getD l.length false=b:=by
  simp [List.getD_eq_getElem?_getD]
lemma Fi {α:Type} (z:α) (l:List α) (b:α) (t:ℕ) (h:t < l.length):
    (l++[b]).getD t z=l.getD t z:=by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
lemma Fg {α:Type} (z:α) (l:List α) (b:α):(l++[b]).getD l.length z=b:=by
  simp [List.getD_eq_getElem?_getD]
lemma Ij (gs hs:List Gate) (x:List Bool) (i:ℕ) (hi:i < x.length+gs.length):
    (run (gs++hs) x).getD i false=(run gs x).getD i false:=by
  induction hs using List.reverseRecOn with
  | nil=>simp
  | append_singleton hs g ih=>
    rw [← List.append_assoc, Il, Fi false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]
lemma Ig (gs:List Gate) (x:List Bool) (i:ℕ) (hi:i < x.length):
    (run gs x).getD i false=x.getD i false:=by
  have:=Ij [] gs x i (by simpa using hi)
  simpa [run] using this
lemma If (gs:List Gate) (x:List Bool):∀ (j:ℕ) (hj:j < gs.length),
    (run gs x).getD (x.length+j) false=gs[j].op.eval (gs[j].inputs.map fun i=>
      if i < x.length+j then (run gs x).getD i false else false):=by
  induction gs using List.reverseRecOn with
  | nil=>intro j hj; simp at hj
  | append_singleton gs g ih=>
    intro j hj
    have hlen:(run gs x).length=x.length+gs.length:=run_length gs x
    have same:∀ (k:ℕ), k≤gs.length→∀ l:List ℕ,
        (l.map fun i=>if i < x.length+k then (run (gs++[g]) x).getD i false else false)=
        l.map fun i=>if i < x.length+k then (run gs x).getD i false else false:=by
      intro k hk l
      refine List.map_congr_left fun i _=>?_
      split_ifs with h
      · exact Ij gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), Ij gs [g] x _ (by omega)]
      exact ih j h
    · have hjj:j=gs.length:=by simp at hj; omega
      subst hjj
      have hg:(gs++[g])[gs.length]=g:=by simp
      rw [hg, same _ le_rfl, Il, ← hlen, Fg]
      congr 1
      refine List.map_congr_left fun i _=>?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
lemma mono (gs:List Gate) (x y:List Bool) (hl:x.length=y.length)
    (h:∀ i, x.getD i false=true→y.getD i false=true)
    (hg:∀ g∈gs, g.op=GateOp.and∨g.op=GateOp.or):
    ∀ i, (run gs x).getD i false=true→(run gs y).getD i false=true:=by
  induction gs using List.reverseRecOn with
  | nil=>intro i hi; exact h i hi
  | append_singleton gs g ih=>
    intro i hi
    have ih':=ih (fun g hg'=>hg g (by simp [hg']))
    have l1:=run_length gs x
    have l2:=run_length gs y
    rw [Il] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length+gs.length) with hlt | heq | hgt
    · rw [Fh _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1:i=(run gs x).length:=by omega
      have e2:i=(run gs y).length:=by omega
      have hi':g.op.eval (g.inputs.map fun i=>(run gs x).getD i false)=true:=by
        rw [← Ff (run gs x) (g.op.eval (g.inputs.map fun i=>(run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, Ff]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq=>ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩:=hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi
def rv (w:List Bool):Bool ⊕ ℕ→Bool
  | .inl b=>b
  | .inr t=>w.getD t false
def fok (g:Gate):Prop:=(g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤2
lemma Io (hs e:List Gate) (y:List Bool) (r:Bool ⊕ ℕ) (h:∀ t, r=.inr t→t < y.length+hs.length):
    rv (run (hs++e) y) r=rv (run hs y) r:=by
  rcases r with b | t
  · rfl
  · exact Ij _ _ _ _ (h t rfl)
lemma emit (N:ℕ) (hs:List Gate) (op:GateOp) (hop:op=GateOp.and∨op=GateOp.or)
    (rs:List (Bool ⊕ ℕ)) (hl:rs.length≤2) (hv:∀ r∈rs, ∀ t, r=.inr t→t < N+hs.length):
    ∃ (r:Bool ⊕ ℕ) (e:List Gate), e.length≤1∧(∀ g∈e, fok g)∧(∀ t, r=.inr t→t < N+hs.length+e.length)∧
      ∀ y:List Bool, y.length=N→ rv (run (hs++e) y) r=op.eval (rs.map (rv (run hs y))):=by
  have keep:∀ r:Bool ⊕ ℕ, (∀ t, r=.inr t→t < N+hs.length)→(∀ y:List Bool, y.length=N→ rv (run hs y) r=op.eval (rs.map (rv (run hs y))))→
      ∃ (r:Bool ⊕ ℕ) (e:List Gate), e.length≤1∧(∀ g∈e, fok g)∧(∀ t, r=.inr t→t < N+hs.length+e.length)∧
        ∀ y:List Bool, y.length=N→ rv (run (hs++e) y) r=op.eval (rs.map (rv (run hs y))):=by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy=>by rw [List.append_nil]; exact h2 y hy⟩
  have add:∀ g:Gate, fok g→(∀ y:List Bool, y.length=N→ g.op.eval (g.inputs.map fun i=>(run hs y).getD i false)=op.eval (rs.map (rv (run hs y))))→
      ∃ (r:Bool ⊕ ℕ) (e:List Gate), e.length≤1∧(∀ g∈e, fok g)∧(∀ t, r=.inr t→t < N+hs.length+e.length)∧
        ∀ y:List Bool, y.length=N→ rv (run (hs++e) y) r=op.eval (rs.map (rv (run hs y))):=by
    intro g h1 h2
    refine ⟨.inr (N+hs.length), [g], by simp, by simpa using h1, ?_, fun y hy=>?_⟩
    · intro t ht
      cases ht
      simp
    · have:N+hs.length=(run hs y).length:=by rw [run_length, hy]
      simp only [rv]
      rw [Il, this, Ff]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr:=hv r (by simp)
    rcases hop with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr:=hv r (by simp)
    have hs':=hv s (by simp)
    rcases hop with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl
lemma Dq {X:Type} (n M:ℕ) (C:Circuit) (src tgt:X→List Bool) (hsrc:∀ x, (src x).length=n) (htgt:∀ x, (tgt x).length=M) (F:Finset ℕ)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (h0:∀ w < n, (∃ b, ∀ x, (src x).getD w false=b)∨∃ t, t < M∧∀ x, (src x).getD w false=(tgt x).getD t false)
    (hne:¬∃ b, ∀ x, C.eval (src x)=b)
    (hF:∀ j∈F, j < C.gates.length∧((∃ b, ∀ x, (run C.gates (src x)).getD (n+j) false=b)∨
      ∃ w < n+j, ∀ x, (run C.gates (src x)).getD (n+j) false=(run C.gates (src x)).getD w false)):
    ∃ D:Circuit, PEqualNP.MetaComplexity.Monotone2 D∧D.size+F.card≤C.size∧∀ x, D.eval (tgt x)=C.eval (src x):=by
  classical
  have key:∀ k, k≤C.gates.length→∃ (hs:List Gate) (m:ℕ→Bool ⊕ ℕ), (∀ g∈hs, fok g)∧hs.length+(F.filter fun j=>j < k).card≤k∧
      (∀ w t, w < n+k→m w=.inr t→t < M+hs.length)∧
      ∀ x:X, ∀ w < n+k, (run C.gates (src x)).getD w false=rv (run hs (tgt x)) (m w):=by
    intro k
    induction k with
    | zero=>
      intro _
      refine ⟨[], fun w=>if h:∃ t, t < M∧∀ x, (src x).getD w false=(tgt x).getD t false then .inr h.choose else if hb:∃ b, ∀ x, (src x).getD w false=b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [Ig _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih=>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩:=ih (by omega)
      have hk':k < C.gates.length:=by omega
      have fin:∀ (r:Bool ⊕ ℕ) (e:List Gate), (∀ g∈e, fok g)→(∀ t, r=.inr t→t < M+hs.length+e.length)→e.length+(if k∈F then 1 else 0)≤1→
          (∀ x:X, (run C.gates (src x)).getD (n+k) false=rv (run (hs++e) (tgt x)) r)→
          ∃ (hs:List Gate) (m:ℕ→Bool ⊕ ℕ), (∀ g∈hs, fok g)∧hs.length+(F.filter fun j=>j < k+1).card≤k+1∧
      (∀ w t, w < n+(k+1)→m w=.inr t→t < M+hs.length)∧
      ∀ x:X, ∀ w < n+(k+1), (run C.gates (src x)).getD w false=rv (run hs (tgt x)) (m w):=by
        intro r e he hr hlen hval
        refine ⟨hs++e, Function.update m (n+k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1:(F.filter fun j=>j < k+1)⊆(F.filter fun j=>j < k)∪(if k∈F then {k} else ∅):=by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have:j=k:=by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2:=(Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF:k∈F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe:w=n+k
          · subst hwe; rw [Function.update_self] at ht
            have:=hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have:=h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe:w=n+k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (Io hs e (tgt x) (m w) fun t ht=>?_).symm
            have:=h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF:k∈F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x=>hb x)
        · refine fin (m w) [] (by simp) (fun t ht=>by simpa using h3 w t hw ht) (by simp [hkF]) (fun x=>?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg:=hC _ (List.getElem_mem hk')
        have hop:C.gates[k].op=GateOp.and∨C.gates[k].op=GateOp.or:=by simpa using hg.1
        let m':ℕ→Bool ⊕ ℕ:=fun i=>if i < n+k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩:=emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩:=List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x=>?_)
        rw [e4 _ (htgt x)]
        have rg:=If C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _=>?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩:=key C.gates.length le_rfl
  have hFc:(F.filter fun j=>j < C.gates.length)=F:=Finset.filter_true_of_mem fun j hj=>(hF j hj).1
  rw [hFc] at h2
  have hout:C.output < n+C.gates.length:=by
    by_contra h
    refine hne ⟨false, fun x=>?_⟩
    change (run C.gates (src x)).getD C.output false=false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev:∀ x, C.eval (src x)=rv (run hs (tgt x)) (m C.output):=fun x=>h4 x _ hout
  rcases hm:m C.output with b | t
  · exact absurd ⟨b, fun x=>by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x=>?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have:=hev x
      rw [hm] at this
      exact this.symm
lemma run_append (pre post:List Gate) (x:List Bool):
    run (pre++post) x=run post (run pre x):=by
  simp [run, List.foldl_append]
lemma run_cons (g:Gate) (post:List Gate) (x:List Bool):
    run (g::post) x=run post (x++[g.op.eval (g.inputs.map fun i=>x.getD i false)]):=rfl
def IW (n:ℕ) (C:Circuit):Prop:=
  ∀ x:Fin n→Bool,
    C.eval (List.ofFn x)=decide (2≤(List.ofFn x).count true)
def HM (pre post:List Gate) (a out:ℕ):Circuit:=
  ⟨pre++⟨GateOp.or, [a]⟩::post, out⟩
lemma Jb (n:ℕ) (hn:2≤n) (C:Circuit)
    (ht:IW n C):¬∃ b, ∀ x:Fin n→Bool, C.eval (List.ofFn x)=b:=by
  rintro ⟨b, hb⟩
  have hzero:=ht (fun _=>false)
  have hone:=ht (fun _=>true)
  rw [hb] at hzero hone
  simp [List.ofFn_const, List.count_replicate] at hzero
  simp [List.ofFn_const, List.count_replicate, hn] at hone
  exact Bool.false_ne_true (hzero.symm.trans hone)
end Aj
namespace Ak
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def step (w:List Bool) (g:Gate):List Bool:=
  w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
def run (gs:List Gate) (x:List Bool):List Bool:=gs.foldl step x
lemma run_cons (g:Gate) (gs:List Gate) (x:List Bool):
    run (g::gs) x=run gs (step x g):=rfl
lemma run_length (gs:List Gate) (x:List Bool):
    (run gs x).length=x.length+gs.length:=by
  induction gs generalizing x with
  | nil=>simp [run]
  | cons g gs ih=>simp [run_cons, ih, step, Nat.add_comm, Nat.add_left_comm]
lemma run_append (gs hs:List Gate) (x:List Bool):
    run (gs++hs) x=run hs (run gs x):=by
  exact List.foldl_append
lemma Ik (gs:List Gate) (x:List Bool) (i:ℕ) (hi:i < x.length):
    (run gs x).getD i false=x.getD i false:=by
  induction gs generalizing x with
  | nil=>rfl
  | cons g gs ih=>
    rw [run_cons, ih (step x g) (by simp [step]; omega)]
    exact List.getD_append x _ false i hi
lemma IK (i:ℕ) (x y:List Bool)
    (hlen:x.length=y.length)
    (hxy:∀ k, k≠i→x.getD k false=y.getD k false) (v:Bool):
    ∀ k, k≠i→(x++[v]).getD k false=(y++[v]).getD k false:=by
  intro k hk
  by_cases hlt:k < x.length
  · rw [List.getD_append x _ false k hlt,
      List.getD_append y _ false k (by omega)]
    exact hxy k hk
  · have hx:x.length≤k:=by omega
    have hy:y.length≤k:=by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hx,
      List.getElem?_append_right hy, hlen]
lemma HY (gs:List Gate) (i:ℕ) (x y:List Bool)
    (hlen:x.length=y.length)
    (hxy:∀ k, k≠i→x.getD k false=y.getD k false)
    (havoid:∀ g∈gs, i∉g.inputs):
    ∀ k, k≠i→(run gs x).getD k false=(run gs y).getD k false:=by
  induction gs generalizing x y with
  | nil=>exact hxy
  | cons g gs ih=>
    have hg:i∉g.inputs:=havoid g (by simp)
    have hv:g.op.eval (g.inputs.map fun k=>x.getD k false)=
        g.op.eval (g.inputs.map fun k=>y.getD k false):=by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact hxy k (by intro heq; exact hg (heq ▸ hk))
    rw [run_cons, run_cons]
    apply ih (step x g) (step y g) (by simp [step, hlen])
    · unfold step
      rw [hv]
      exact IK i x y hlen hxy _
    · intro d hd
      exact havoid d (by simp [hd])
lemma Ju (C:Circuit) (pre post:List Gate) (g:Gate)
    (hsplit:C.gates=pre++g::post) (i:ℕ) (x y:List Bool)
    (hlen:x.length=y.length)
    (hxy:∀ k, k≠i→x.getD k false=y.getD k false)
    (hpre:∀ d∈pre, i∉d.inputs)
    (hpost:∀ d∈post, i∉d.inputs)
    (hgate:g.op.eval (g.inputs.map fun k=>(run pre x).getD k false)=
      g.op.eval (g.inputs.map fun k=>(run pre y).getD k false))
    (hout:C.output≠i):C.eval x=C.eval y:=by
  have hp:=HY pre i x y hlen hxy hpre
  change (run C.gates x).getD C.output false=(run C.gates y).getD C.output false
  rw [hsplit, run_append, run_append, run_cons, run_cons]
  unfold step
  rw [hgate]
  exact HY post i _ _ (by simp [run_length, hlen])
    (IK i (run pre x) (run pre y)
      (by simp [run_length, hlen]) hp _) hpost C.output hout
lemma GS {n:ℕ} (i:Fin n) (x y:Fin n→Bool)
    (hxy:∀ k, k≠i→x k=y k):
    ∀ k, k≠i.val→(List.ofFn x).getD k false=(List.ofFn y).getD k false:=by
  intro k hk
  by_cases hkn:k < n
  · have hne:(⟨k, hkn⟩:Fin n)≠i:=by
      intro heq
      exact hk (congrArg Fin.val heq)
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hkn,
      ↓reduceDIte, Option.getD_some] using hxy ⟨k, hkn⟩ hne
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hkn,
      ↓reduceDIte, Option.getD_none]
def singleton {n:ℕ} (k:Fin n):Fin n→Bool:=fun t=>decide (t=k)
def pair {n:ℕ} (i k:Fin n):Fin n→Bool:=fun t=>decide (t=i∨t=k)
lemma IE {n:ℕ} (i k:Fin n):
    ∀ t, t≠i.val→
      (List.ofFn (singleton k)).getD t false=(List.ofFn (pair i k)).getD t false:=by
  apply GS
  intro t hti
  simp [singleton, pair, hti]
lemma HH (x:Fin n→Bool) (i:Fin n):
    (List.ofFn x).getD i.val false=x i:=by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
    ↓reduceDIte, Option.getD_some]
lemma Ck {n:ℕ}
    (C:Circuit) (pre post:List Gate) (g:Gate)
    (hsplit:C.gates=pre++g::post) (i k:Fin n) (hik:i≠k)
    (a:ℕ) (hai:a≠i.val)
    (hports:g.inputs=[i.val, a]∨g.inputs=[a, i.val])
    (hpre:∀ d∈pre, i.val∉d.inputs)
    (hpost:∀ d∈post, i.val∉d.inputs)
    (hout:C.output≠i.val)
    (hsingle:C.eval (List.ofFn (singleton k))=false)
    (hpair:C.eval (List.ofFn (pair i k))=true)
    (isAnd:Bool) (hop:g.op=if isAnd then .and else .or):
    (run pre (List.ofFn (singleton k))).getD a false=isAnd:=by
  have hp:=HY pre i.val
    (List.ofFn (singleton k)) (List.ofFn (pair i k)) (by simp)
    (IE i k) hpre
  have ha:=hp a hai
  have hi0:(run pre (List.ofFn (singleton k))).getD i.val false=false:=by
    rw [Ik pre _ _ (by simp), HH]
    simp [singleton, hik]
  have hi1:(run pre (List.ofFn (pair i k))).getD i.val false=true:=by
    rw [Ik pre _ _ (by simp), HH]
    simp [pair]
  cases hc:(run pre (List.ofFn (singleton k))).getD a false <;>
    cases isAnd
  · rfl
  · exfalso
    have hgate:g.op.eval (g.inputs.map fun t=>
        (run pre (List.ofFn (singleton k))).getD t false)=
        g.op.eval (g.inputs.map fun t=>
        (run pre (List.ofFn (pair i k))).getD t false):=by
      have hca:=ha.symm.trans hc
      rcases hports with hports | hports <;>
        simp only [hports, hop, ↓reduceIte,
          List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
          id_eq, hi0, hi1, hc, hca] <;> rfl
    have heq:=Ju C pre post g hsplit i.val _ _ (by simp)
      (IE i k) hpre hpost hgate hout
    rw [hsingle, hpair] at heq
    exact Bool.false_ne_true heq
  · exfalso
    have hgate:g.op.eval (g.inputs.map fun t=>
        (run pre (List.ofFn (singleton k))).getD t false)=
        g.op.eval (g.inputs.map fun t=>
        (run pre (List.ofFn (pair i k))).getD t false):=by
      have hca:=ha.symm.trans hc
      rcases hports with hports | hports <;>
        simp only [hports, hop, List.map_cons, List.map_nil, GateOp.eval,
          hi0, hi1, hc, hca] <;> rfl
    have heq:=Ju C pre post g hsplit i.val _ _ (by simp)
      (IE i k) hpre hpost hgate hout
    rw [hsingle, hpair] at heq
    exact Bool.false_ne_true heq
  · rfl
lemma Im (gs:List Gate) (x:List Bool) (j a:ℕ)
    (ha:a < x.length+(gs.take j).length):
    (run gs x).getD a false=(run (gs.take j) x).getD a false:=by
  conv_lhs=>rw [← List.take_append_drop j gs, run_append]
  exact Ik (gs.drop j) (run (gs.take j) x) a
    (by simpa [run_length] using ha)
lemma BR {n:ℕ}
    (C:Circuit) (j:ℕ) (hj:j < C.gates.length)
    (i k:Fin n) (hik:i≠k) (a:ℕ) (hai:a≠i.val) (ha:a < n+j)
    (hports:C.gates[j].inputs=[i.val, a]∨C.gates[j].inputs=[a, i.val])
    (hunique:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j)
    (hout:C.output≠i.val)
    (hsingle:C.eval (List.ofFn (singleton k))=false)
    (hpair:C.eval (List.ofFn (pair i k))=true)
    (isAnd:Bool) (hop:C.gates[j].op=if isAnd then .and else .or):
    (C.wires (List.ofFn (singleton k))).getD a false=isAnd:=by
  have hpre:∀ d∈C.gates.take j, i.val∉d.inputs:=by
    intro d hd hi
    obtain ⟨t, ht, htd⟩:=List.mem_iff_getElem.mp hd
    have htc:t < C.gates.length:=by
      have hh:t < min j C.gates.length:=by simpa only [List.length_take] using ht
      omega
    have htj:t < j:=by
      have hh:t < min j C.gates.length:=by simpa only [List.length_take] using ht
      omega
    have hdroot:C.gates[t]=d:=by simpa only [List.getElem_take] using htd
    have heq:=hunique t htc (by simpa only [hdroot] using hi)
    omega
  have hpost:∀ d∈C.gates.drop (j+1), i.val∉d.inputs:=by
    intro d hd hi
    obtain ⟨t, ht, htd⟩:=List.mem_iff_getElem.mp hd
    have htc:j+1+t < C.gates.length:=by
      have hh:t < C.gates.length - (j+1):=by simpa only [List.length_drop] using ht
      omega
    have hdroot:C.gates[j+1+t]=d:=by
      simpa only [List.getElem_drop] using htd
    have heq:=hunique (j+1+t) htc (by simpa only [hdroot] using hi)
    omega
  have hsplit:C.gates=C.gates.take j++C.gates[j]::C.gates.drop (j+1):=by
    conv_lhs=>rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj]
  have hp:=Ck C (C.gates.take j) (C.gates.drop (j+1))
    C.gates[j] hsplit i k hik a hai hports hpre hpost hout hsingle hpair isAnd hop
  change (run C.gates (List.ofFn (singleton k))).getD a false=isAnd
  rw [Im C.gates _ j a (by simp only [List.length_ofFn, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hj)]; exact ha)]
  exact hp
lemma Fd (g:Gate) (x y:List Bool)
    (hop:g.op=.and∨g.op=.or)
    (hxy:∀ a, x.getD a false=true→y.getD a false=true):
    g.op.eval (g.inputs.map fun a=>x.getD a false)=true→
      g.op.eval (g.inputs.map fun a=>y.getD a false)=true:=by
  intro ht
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true] at ht ⊢
    intro b hb
    obtain ⟨a, ha, rfl⟩:=List.mem_map.mp hb
    exact hxy a (ht _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true] at ht ⊢
    obtain ⟨b, hb, hbt⟩:=ht
    obtain ⟨a, ha, rfl⟩:=List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, hxy a hbt⟩
lemma IL (x y:List Bool) (hlen:x.length=y.length)
    (hxy:∀ a, x.getD a false=true→y.getD a false=true)
    (v w:Bool) (hvw:v=true→w=true):
    ∀ a, (x++[v]).getD a false=true→(y++[w]).getD a false=true:=by
  intro a ha
  by_cases hlt:a < x.length
  · rw [List.getD_append x _ false a hlt] at ha
    rw [List.getD_append y _ false a (by omega)]
    exact hxy a ha
  · have hx:x.length≤a:=by omega
    have hy:y.length≤a:=by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hx,
      List.getElem?_append_right hy, hlen] at ha ⊢
    by_cases heq:a - y.length=0
    · simp only [heq, List.getElem?_cons_zero, Option.getD_some] at ha ⊢
      exact hvw ha
    · have hpos:0 < a - y.length:=by omega
      have hnone:([v]:List Bool)[a - y.length]?=none:=
        List.getElem?_eq_none (by simp only [List.length_singleton]; omega)
      simp only [hnone, Option.getD_none] at ha
      exact False.elim (Bool.false_ne_true ha)
lemma run_true_mono (gs:List Gate) (x y:List Bool)
    (hlen:x.length=y.length)
    (hgs:∀ g∈gs, g.op=.and∨g.op=.or)
    (hxy:∀ a, x.getD a false=true→y.getD a false=true):
    ∀ a, (run gs x).getD a false=true→(run gs y).getD a false=true:=by
  induction gs generalizing x y with
  | nil=>exact hxy
  | cons g gs ih=>
    rw [run_cons, run_cons]
    apply ih (step x g) (step y g) (by simp [step, hlen])
    · intro d hd
      exact hgs d (by simp [hd])
    · exact IL x y hlen hxy _ _
        (Fd g x y (hgs g (by simp)) hxy)
lemma Kx {n:ℕ} (a:ℕ):
    (List.ofFn (fun _:Fin n=>false)).getD a false=false:=by
  by_cases ha:a < n <;>
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, ha,
      ↓reduceDIte, Option.getD_some, Option.getD_none]
lemma Cc {n:ℕ} (C:Circuit) (hC:Monotone2 C)
    (a:ℕ) (k:Fin n)
    (hk:(C.wires (List.ofFn (singleton k))).getD a false=false):
    (C.wires (List.ofFn (fun _:Fin n=>false))).getD a false=false:=by
  cases hh:(C.wires (List.ofFn (fun _:Fin n=>false))).getD a false with
  | false=>rfl
  | true=>
    have hm:=run_true_mono C.gates (List.ofFn (fun _:Fin n=>false))
      (List.ofFn (singleton k)) (by simp) (fun g hg=>(hC g hg).1)
      (fun t ht=>False.elim (Bool.false_ne_true ((Kx t).symm.trans ht))) a hh
    change (C.wires (List.ofFn (singleton k))).getD a false=true at hm
    rw [hk] at hm
    exact False.elim (Bool.false_ne_true hm)
lemma BS {n:ℕ}
    (C:Circuit) (j:ℕ) (hj:j < C.gates.length)
    (i:Fin n) (a:ℕ) (hai:a≠i.val) (ha:a < n+j)
    (hunique:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j)
    (x y:Fin n→Bool) (hxy:∀ k, k≠i→x k=y k):
    (C.wires (List.ofFn x)).getD a false=(C.wires (List.ofFn y)).getD a false:=by
  have hpre:∀ d∈C.gates.take j, i.val∉d.inputs:=by
    intro d hd hi
    obtain ⟨t, ht, htd⟩:=List.mem_iff_getElem.mp hd
    have hbounds:t < min j C.gates.length:=by
      simpa only [List.length_take] using ht
    have htc:t < C.gates.length:=by omega
    have hdroot:C.gates[t]=d:=by simpa only [List.getElem_take] using htd
    have heq:=hunique t htc (by simpa only [hdroot] using hi)
    omega
  have hp:=HY (C.gates.take j) i.val (List.ofFn x) (List.ofFn y)
    (by simp) (GS i x y hxy) hpre a hai
  change (run C.gates (List.ofFn x)).getD a false=(run C.gates (List.ofFn y)).getD a false
  rw [Im C.gates _ j a (by simp only [List.length_ofFn, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hj)]; exact ha),
    Im C.gates _ j a (by simp only [List.length_ofFn, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hj)]; exact ha)]
  exact hp
lemma IZ {n:ℕ}
    (C:Circuit) (j:ℕ) (hj:j < C.gates.length)
    (i k:Fin n) (hik:i≠k) (a:ℕ) (hai:a≠i.val) (ha:a < n+j)
    (hports:C.gates[j].inputs=[i.val, a]∨C.gates[j].inputs=[a, i.val])
    (hunique:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j)
    (hout:C.output≠i.val)
    (hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card))
    (isAnd:Bool) (hop:C.gates[j].op=if isAnd then .and else .or):
    (C.wires (List.ofFn (singleton k))).getD a false=isAnd:=by
  apply BR C j hj i k hik a hai ha hports hunique hout
  · change C.eval (List.ofFn (fun t:Fin n=>decide (t=k)))=false
    simpa using hcorrect {k}
  · change C.eval (List.ofFn (fun t:Fin n=>decide (t=i∨t=k)))=true
    simpa [hik] using hcorrect {i, k}
  · exact hop
lemma IX {n:ℕ}
    (C:Circuit) (j:ℕ) (hj:j < C.gates.length)
    (i:Fin n) (a:ℕ) (hai:a≠i.val) (ha:a < n+j)
    (hports:C.gates[j].inputs=[i.val, a]∨C.gates[j].inputs=[a, i.val])
    (hunique:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j)
    (hout:C.output≠i.val)
    (hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card))
    (hop:C.gates[j].op=.and):
    ∀ k:Fin n, k≠i→(C.wires (List.ofFn (singleton k))).getD a false=true:=by
  intro k hki
  exact IZ C j hj i k (Ne.symm hki) a hai ha hports
    hunique hout hcorrect true hop
lemma Jc {n:ℕ} (hn:2≤n)
    (C:Circuit) (hC:Monotone2 C) (j:ℕ) (hj:j < C.gates.length)
    (i:Fin n) (a:ℕ) (hai:a≠i.val) (ha:a < n+j)
    (hports:C.gates[j].inputs=[i.val, a]∨C.gates[j].inputs=[a, i.val])
    (hunique:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j)
    (hout:C.output≠i.val)
    (hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card))
    (hop:C.gates[j].op=.or):
    (C.wires (List.ofFn (fun _:Fin n=>false))).getD a false=false∧
      ∀ k:Fin n, (C.wires (List.ofFn (singleton k))).getD a false=false:=by
  have hother:∃ k:Fin n, i≠k:=by
    let z:Fin n:=⟨0, by omega⟩
    by_cases hiz:i=z
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro heq
      have hv:=congrArg Fin.val heq
      simp [hiz, z] at hv
    · exact ⟨z, hiz⟩
  obtain ⟨k, hik⟩:=hother
  have hk:=IZ C j hj i k hik a hai ha hports
    hunique hout hcorrect false hop
  have hzero:=Cc C hC a k hk
  refine ⟨hzero, ?_⟩
  intro t
  by_cases hti:t=i
  · subst t
    have heq:=BS C j hj i a hai ha hunique
      (singleton i) (fun _=>false) (by intro t ht; simp [singleton, ht])
    exact heq.trans hzero
  · exact IZ C j hj i t (Ne.symm hti) a hai ha hports
      hunique hout hcorrect false hop
end Ak
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Bg (n j x w:ℕ):ℕ:=
  if w=n+j then x else if n+j < w then w-1 else w
def Bf (n j x:ℕ) (g:Gate):Gate:=
  ⟨g.op, g.inputs.map (Bg n j x)⟩
def DJ (n x h:ℕ) (pre post:List Gate) (out:ℕ):Circuit:=
  ⟨(pre++post).map (Bf n pre.length x)++
    [⟨GateOp.or, [Bg n pre.length x h, Bg n pre.length x out]⟩],
    n+pre.length+post.length⟩
lemma DN (n x h:ℕ) (pre post:List Gate) (out:ℕ):
    (DJ n x h pre post out).size=
      (⟨pre++⟨GateOp.or, [x,h]⟩::post, out⟩:Circuit).size:=by
  simp [DJ, Circuit.size]
end Aw
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma DM (n x h:ℕ) (pre post:List Gate) (out:ℕ)
    (hC:Monotone2 (⟨pre++⟨GateOp.or, [x,h]⟩::post, out⟩:Circuit)):
    Monotone2 (DJ n x h pre post out):=by
  intro g hg
  change g∈(pre++post).map (Bf n pre.length x)++
    [⟨GateOp.or, [Bg n pre.length x h, Bg n pre.length x out]⟩] at hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨d, hd, rfl⟩:=List.mem_map.mp hg
    have hd':d∈pre++⟨GateOp.or, [x,h]⟩::post:=by
      rcases List.mem_append.mp hd with hd | hd <;> simp [hd]
    have hc:=hC d hd'
    exact ⟨hc.1, by simpa [Bf] using hc.2⟩
  · have he:=List.mem_singleton.mp hg
    subst g
    simp
lemma Bh (n j x w L:ℕ) (hx:x < n) (hk:n+j < L) (hw:w < L):
    Bg n j x w < L-1:=by
  unfold Bg
  split_ifs <;> omega
lemma Bj (n j x:ℕ) (hx:x < n) (w:List Bool)
    (hw:w.length=n+j):
    ∀ i, (w++[w.getD x false]).getD i false=w.getD (Bg n j x i) false:=by
  intro i
  rcases Nat.lt_trichotomy i (n+j) with hi | rfl | hi
  · have ha:Bg n j x i=i:=by unfold Bg; split_ifs <;> omega
    rw [ha, Fh _ _ _ (by omega)]
  · have ha:Bg n j x (n+j)=x:=by simp [Bg]
    rw [ha, ← hw, Ff]
  · have ha:Bg n j x i=i-1:=by unfold Bg; split_ifs <;> omega
    rw [ha, List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]
lemma Bi (n j x:ℕ) (hx:x < n) (old new:List Bool)
    (hlen:old.length=new.length+1) (hk:n+j < old.length)
    (hrel:∀ i, old.getD i false=new.getD (Bg n j x i) false) (b:Bool):
    ∀ i, (old++[b]).getD i false=(new++[b]).getD (Bg n j x i) false:=by
  intro i
  rcases Nat.lt_trichotomy i old.length with hi | rfl | hi
  · have ha:=Bh n j x i old.length hx hk hi
    rw [Fh _ _ _ hi, Fh _ _ _ (by omega)]
    exact hrel i
  · have ha:Bg n j x old.length=new.length:=by
      unfold Bg
      split_ifs <;> omega
    rw [ha, Ff, Ff]
  · have ha:Bg n j x i=i-1:=by unfold Bg; split_ifs <;> omega
    rw [ha, List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
lemma HZ (n j x:ℕ) (hx:x < n) (gs:List Gate)
    (old new:List Bool) (hlen:old.length=new.length+1) (hk:n+j < old.length)
    (hrel:∀ i, old.getD i false=new.getD (Bg n j x i) false):
    ∀ i, (run gs old).getD i false=
      (run (gs.map (Bf n j x)) new).getD (Bg n j x i) false:=by
  induction gs generalizing old new with
  | nil=>exact hrel
  | cons g gs ih=>
    have he:g.op.eval (g.inputs.map fun i=>old.getD i false)=
        (Bf n j x g).op.eval
          ((Bf n j x g).inputs.map fun i=>new.getD i false):=by
      simp only [Bf, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _=>hrel i)
    rw [List.map_cons, run_cons, run_cons, ← he]
    exact ih _ _ (by simp; omega) (by simp; omega)
      (Bi n j x hx old new hlen hk hrel _)
lemma Bk (n x:ℕ) (pre:List Gate)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length):
    pre.map (Bf n pre.length x)=pre:=by
  calc
    pre.map (Bf n pre.length x)=pre.map id:=by
      apply List.map_congr_left
      intro g hg
      cases g with
      | mk op inputs=>
        change Gate.mk op (inputs.map (Bg n pre.length x))=Gate.mk op inputs
        congr 1
        calc
          inputs.map (Bg n pre.length x)=inputs.map id:=by
            apply List.map_congr_left
            intro w hw
            have hlt:=hpre ⟨op,inputs⟩ hg w hw
            change Bg n pre.length x w=w
            unfold Bg
            split_ifs <;> omega
          _=inputs:=List.map_id inputs
    _=pre:=List.map_id pre
lemma DK (n x h:ℕ) (pre post:List Gate) (out:ℕ)
    (hx:x < n) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (z:List Bool) (hz:z.length=n):
    (DJ n x h pre post out).eval z=
      ((run pre z).getD h false || (HM pre post x out).eval z):=by
  let w:=run pre z
  have hw:w.length=n+pre.length:=by simp [w, run_length, hz]
  have hs:=HZ n pre.length x hx post
    (w++[w.getD x false]) w (by simp) (by simp; omega)
    (Bj n pre.length x hx w hw)
  have hcopy:run (pre++⟨GateOp.or, [x]⟩::post) z=
      run post (w++[w.getD x false]):=by
    rw [run_append, run_cons]
    simp [w, GateOp.eval]
  have hbase:run ((pre++post).map (Bf n pre.length x)) z=
      run (post.map (Bf n pre.length x)) w:=by
    rw [List.map_append, Bk n x pre hpre, run_append]
  have hbase_len:(run ((pre++post).map (Bf n pre.length x)) z).length=
      n+pre.length+post.length:=by simp [run_length, hz]; omega
  have hhval:(run post (w++[w.getD x false])).getD h false=w.getD h false:=by
    have hh':h < w.length:=by omega
    rw [Ig post (w++[w.getD x false]) h (by simp; omega)]
    exact Fh w (w.getD x false) h hh'
  change (run (((pre++post).map (Bf n pre.length x))++
    [⟨GateOp.or, [Bg n pre.length x h, Bg n pre.length x out]⟩]) z).getD
      (n+pre.length+post.length) false=_
  rw [Il, ← hbase_len, Ff]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    id, Bool.or_false]
  rw [hbase, ← hs h, ← hs out, hhval]
  change (w.getD h false || _)=(w.getD h false || _)
  congr 1
  change _=(run (pre++⟨GateOp.or, [x]⟩::post) z).getD out false
  rw [hcopy]
lemma HN (pre post:List Gate) (x h out:ℕ)
    (z:List Bool) (hh:(run pre z).getD h false=false):
    (HM pre post x out).eval z=
      (⟨pre++⟨GateOp.or, [x,h]⟩::post, out⟩:Circuit).eval z:=by
  change (run (pre++⟨GateOp.or, [x]⟩::post) z).getD out false=
    (run (pre++⟨GateOp.or, [x,h]⟩::post) z).getD out false
  rw [run_append, run_append, run_cons, run_cons]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
    List.any_nil, id, Bool.or_false, hh]
lemma DL (n x h:ℕ) (pre post:List Gate) (out:ℕ)
    (hx:x < n) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (z:List Bool) (hz:z.length=n)
    (hdom:(run pre z).getD h false=true→
      (⟨pre++⟨GateOp.or, [x,h]⟩::post, out⟩:Circuit).eval z=true):
    (DJ n x h pre post out).eval z=
      (⟨pre++⟨GateOp.or, [x,h]⟩::post, out⟩:Circuit).eval z:=by
  rw [DK n x h pre post out hx hh hpre z hz]
  cases hv:(run pre z).getD h false with
  | false=>
    simp only [Bool.false_or]
    exact HN pre post x h out z hv
  | true=>simp [hdom hv]
lemma DO (n x h:ℕ) (pre post:List Gate) (out:ℕ)
    (hx:x < n) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (ht:IW n ⟨pre++⟨GateOp.or, [x,h]⟩::post, out⟩)
    (hsparse:∀ z:Fin n→Bool, (List.ofFn z).count true≤1→
      (run pre (List.ofFn z)).getD h false=false):
    IW n (DJ n x h pre post out):=by
  intro z
  rw [DL n x h pre post out hx hh hpre
    (List.ofFn z) (by simp) (by
      intro htrue
      have hc:2≤(List.ofFn z).count true:=by
        by_contra hnot
        have hf:=hsparse z (by omega)
        rw [hf] at htrue
        contradiction
      simpa only [hc, decide_true] using ht z)]
  exact ht z
end Aw
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma ID (n:ℕ) (hn:1≤n) (C:Circuit)
    (hC:Monotone2 C) (a:ℕ)
    (hsingle:∀ k:Fin n,
      (C.wires (List.ofFn (Ak.singleton k))).getD a false=false)
    (z:Fin n→Bool) (hz:(List.ofFn z).count true≤1):
    (C.wires (List.ofFn z)).getD a false=false:=by
  letI:Nonempty (Fin n):=⟨⟨0, by omega⟩⟩
  rw [List.count_ofFn] at hz
  obtain ⟨k, hk⟩:=Finset.card_le_one_iff_subset_singleton.mp hz
  have hpoint:∀ i:Fin n, z i=true→Ak.singleton k i=true:=by
    intro i hi
    have himem:i∈(Finset.univ.filter fun t=>z t=true):=by simp [hi]
    have hik:=Finset.mem_singleton.mp (hk himem)
    simp [Ak.singleton, hik]
  have hbits:∀ w, (List.ofFn z).getD w false=true→
      (List.ofFn (Ak.singleton k)).getD w false=true:=by
    intro w hw
    by_cases hwn:w < n
    · have hx:(List.ofFn z).getD w false=z ⟨w,hwn⟩:=by
        simp [List.getD_eq_getElem?_getD, hwn]
      have hy:(List.ofFn (Ak.singleton k)).getD w false=
          Ak.singleton k ⟨w,hwn⟩:=by
        simp [List.getD_eq_getElem?_getD, hwn]
      rw [hy]
      exact hpoint _ (hx.symm.trans hw)
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hw
      contradiction
  cases he:(C.wires (List.ofFn z)).getD a false with
  | false=>rfl
  | true=>
    have hm:=mono C.gates (List.ofFn z)
      (List.ofFn (Ak.singleton k)) (by simp) hbits
      (fun g hg=>(hC g hg).1) a he
    change (C.wires (List.ofFn (Ak.singleton k))).getD a false=true at hm
    rw [hsingle k] at hm
    contradiction
lemma DP (n:ℕ) (hn:2≤n) (i:Fin n) (h:ℕ)
    (pre post:List Gate) (out:ℕ)
    (hhi:h≠i.val) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (hout:out≠i.val)
    (hC:Monotone2 (⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:Circuit))
    (ht:IW n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩)
    (hunique:∀ (t:ℕ) (ht:t < (pre++⟨GateOp.or, [i.val,h]⟩::post).length),
      i.val∈(pre++⟨GateOp.or, [i.val,h]⟩::post)[t].inputs→t=pre.length):
    IW n (DJ n i.val h pre post out):=by
  let C:Circuit:=⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩
  have hj:pre.length < C.gates.length:=by simp [C]
  have hgate:C.gates[pre.length]=⟨GateOp.or, [i.val,h]⟩:=by simp [C]
  have hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card):=by
    intro S
    simpa using ht (fun t=>decide (t∈S))
  have hcomp:=Ak.Jc hn C hC pre.length hj i h
    hhi hh (by rw [hgate]; exact Or.inl rfl) hunique hout hcorrect (by rw [hgate])
  apply DO n i.val h pre post out i.isLt hh hpre ht
  intro z hz
  have hs:=ID n (by omega) C hC h hcomp.2 z hz
  have hp:=Ij pre (⟨GateOp.or, [i.val,h]⟩::post) (List.ofFn z) h (by simpa using hh)
  change (run (pre++⟨GateOp.or, [i.val,h]⟩::post) (List.ofFn z)).getD h false=false at hs
  rw [hp] at hs
  exact hs
end Aw
namespace Ar
open PEqualNP.CircuitLowerBounds
open scoped BigOperators
def IB (n:ℕ) (C:Circuit):ℕ:=
  ∑ i:Fin n, (C.wires (List.ofFn fun k:Fin n=>decide (k=i))).count true
end Ar
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Ia (n j x:ℕ) (hx:x < n) (gs:List Gate)
    (old new:List Bool) (hlen:old.length=new.length+1) (hk:n+j < old.length)
    (hrel:∀ i, old.getD i false=new.getD (Bg n j x i) false)
    (d:ℕ) (hcount:old.count true=new.count true+d):
    (run gs old).count true=
      (run (gs.map (Bf n j x)) new).count true+d:=by
  induction gs generalizing old new with
  | nil=>exact hcount
  | cons g gs ih=>
    have he:g.op.eval (g.inputs.map fun i=>old.getD i false)=
        (Bf n j x g).op.eval
          ((Bf n j x g).inputs.map fun i=>new.getD i false):=by
      simp only [Bf, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _=>hrel i)
    rw [List.map_cons, run_cons, run_cons, ← he]
    apply ih _ _ (by simp; omega) (by simp; omega)
      (Bi n j x hx old new hlen hk hrel _)
    simp only [List.count_append]
    omega
lemma Ib (n j x:ℕ) (hx:x < n)
    (gs:List Gate) (w:List Bool) (hw:w.length=n+j):
    (run gs (w++[w.getD x false])).count true=
      (run (gs.map (Bf n j x)) w).count true+
        (if w.getD x false then 1 else 0):=by
  apply Ia n j x hx gs (w++[w.getD x false]) w
    (by simp) (by simp; omega) (Bj n j x hx w hw)
  cases w.getD x false <;> simp
end Aw
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Ar
open scoped BigOperators
lemma DQ (n x h:ℕ) (pre post:List Gate) (out:ℕ)
    (hx:x < n)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (z:List Bool) (hz:z.length=n)
    (hhfalse:(run pre z).getD h false=false)
    (houtfalse:(DJ n x h pre post out).eval z=false):
    ((⟨pre++⟨GateOp.or, [x,h]⟩::post, out⟩:Circuit).wires z).count true=
      ((DJ n x h pre post out).wires z).count true+
        (if z.getD x false then 1 else 0):=by
  let w:=run pre z
  have hw:w.length=n+pre.length:=by simp [w, run_length, hz]
  have hraw:w.getD x false=z.getD x false:=
    Ig pre z x (by rw [hz]; exact hx)
  have hcount:=Ib n pre.length x hx post w hw
  rw [hraw] at hcount
  have hold:run (pre++⟨GateOp.or, [x,h]⟩::post) z=
      run post (w++[w.getD x false]):=by
    rw [run_append, run_cons]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
      List.any_nil, id, Bool.or_false, hhfalse]
    rfl
  have hbase:run ((pre++post).map (Bf n pre.length x)) z=
      run (post.map (Bf n pre.length x)) w:=by
    rw [List.map_append, Bk n x pre hpre, run_append]
  have hbase_len:(run ((pre++post).map (Bf n pre.length x)) z).length=
      n+pre.length+post.length:=by simp [run_length, hz]; omega
  let g:Gate:=⟨GateOp.or, [Bg n pre.length x h, Bg n pre.length x out]⟩
  have hlast:g.op.eval (g.inputs.map fun a=>
      (run ((pre++post).map (Bf n pre.length x)) z).getD a false)=false:=by
    change (run (((pre++post).map (Bf n pre.length x))++[g]) z).getD
      (n+pre.length+post.length) false=false at houtfalse
    rw [Il, ← hbase_len, Ff] at houtfalse
    exact houtfalse
  have hnewcount:((DJ n x h pre post out).wires z).count true=
      (run (post.map (Bf n pre.length x)) w).count true:=by
    change (run (((pre++post).map (Bf n pre.length x))++[g]) z).count true=_
    rw [Il, hlast, List.count_append]
    simp only [show ([false]:List Bool).count true=0 by decide, Nat.add_zero]
    rw [hbase]
  change (run (pre++⟨GateOp.or, [x,h]⟩::post) z).count true=_
  rw [hold, hnewcount]
  rw [hraw]
  exact hcount
lemma Jz (n:ℕ) (hn:2≤n) (i:Fin n) (h:ℕ)
    (pre post:List Gate) (out:ℕ)
    (hhi:h≠i.val) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (hout:out≠i.val)
    (hC:Monotone2 (⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:Circuit))
    (ht:IW n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩)
    (hunique:∀ (t:ℕ) (ht:t < (pre++⟨GateOp.or, [i.val,h]⟩::post).length),
      i.val∈(pre++⟨GateOp.or, [i.val,h]⟩::post)[t].inputs→t=pre.length)
    (k:Fin n):
    ((⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:Circuit).wires
      (List.ofFn fun t:Fin n=>decide (t=k))).count true=
      ((DJ n i.val h pre post out).wires
        (List.ofFn fun t:Fin n=>decide (t=k))).count true+(if k=i then 1 else 0):=by
  let C:Circuit:=⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩
  have hj:pre.length < C.gates.length:=by simp [C]
  have hgate:C.gates[pre.length]=⟨GateOp.or, [i.val,h]⟩:=by simp [C]
  have hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card):=by
    intro S
    simpa using ht (fun t=>decide (t∈S))
  have hcomp:=Ak.Jc hn C hC pre.length hj i h
    hhi hh (by rw [hgate]; exact Or.inl rfl) hunique hout hcorrect (by rw [hgate])
  let z:List Bool:=List.ofFn (fun t:Fin n=>decide (t=k))
  have hz:z.length=n:=by simp [z]
  have hcompfalse:(run pre z).getD h false=false:=by
    have hc:=hcomp.2 k
    change (run (pre++⟨GateOp.or, [i.val,h]⟩::post) z).getD h false=false at hc
    rw [Ij pre (⟨GateOp.or, [i.val,h]⟩::post) z h (by rw [hz]; exact hh)] at hc
    exact hc
  have htD:=DP n hn i h pre post out hhi hh hpre hout hC ht hunique
  have hcorrectD:∀ S:Finset (Fin n),
      (DJ n i.val h pre post out).eval (List.ofFn (fun t=>decide (t∈S)))=
        decide (2≤S.card):=by
    intro S
    simpa using htD (fun t=>decide (t∈S))
  have hDfalse:(DJ n i.val h pre post out).eval z=false:=by
    simpa [z] using hcorrectD ({k}:Finset (Fin n))
  have hbit:(if z.getD i.val false then 1 else 0)=(if k=i then 1 else 0):=by
    simp [z, List.getD_eq_getElem?_getD, i.isLt, eq_comm]
  have hc:=DQ n i.val h pre post out i.isLt hpre
    z hz hcompfalse hDfalse
  rw [hbit] at hc
  exact hc
lemma Jx (n:ℕ) (hn:2≤n) (i:Fin n) (h:ℕ)
    (pre post:List Gate) (out:ℕ)
    (hhi:h≠i.val) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (hout:out≠i.val)
    (hC:Monotone2 (⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:Circuit))
    (ht:IW n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩)
    (hunique:∀ (t:ℕ) (ht:t < (pre++⟨GateOp.or, [i.val,h]⟩::post).length),
      i.val∈(pre++⟨GateOp.or, [i.val,h]⟩::post)[t].inputs→t=pre.length):
    IB n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩=
      IB n (DJ n i.val h pre post out)+1:=by
  unfold IB
  calc
    (∑ k:Fin n, ((⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:Circuit).wires
      (List.ofFn fun t:Fin n=>decide (t=k))).count true)=
        ∑ k:Fin n, (((DJ n i.val h pre post out).wires
          (List.ofFn fun t:Fin n=>decide (t=k))).count true+(if k=i then 1 else 0)):=by
      apply Finset.sum_congr rfl
      intro k _
      exact Jz n hn i h pre post out hhi hh hpre hout hC ht hunique k
    _=_:=by simp [Finset.sum_add_distrib]
lemma Jv (n:ℕ) (hn:2≤n) (i:Fin n) (h:ℕ)
    (pre post:List Gate) (out:ℕ)
    (hhi:h≠i.val) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (hout:out≠i.val)
    (hC:Monotone2 (⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:Circuit))
    (ht:IW n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩)
    (hunique:∀ (t:ℕ) (ht:t < (pre++⟨GateOp.or, [i.val,h]⟩::post).length),
      i.val∈(pre++⟨GateOp.or, [i.val,h]⟩::post)[t].inputs→t=pre.length)
    (hsecondary:∀ E:Circuit, Monotone2 E→
      circuitFun n E=circuitFun n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩→
      E.size=(⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:Circuit).size→
      IB n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩≤IB n E):
    False:=by
  let E:=DJ n i.val h pre post out
  have hE:Monotone2 E:=DM n i.val h pre post out hC
  have htE:=DP n hn i h pre post out hhi hh hpre hout hC ht hunique
  have hfun:circuitFun n E=circuitFun n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:=by
    funext z
    exact (htE z).trans (ht z).symm
  have hs:=DN n i.val h pre post out
  have hm:=hsecondary E hE hfun hs
  have hd:=Jx n hn i h pre post out hhi hh hpre hout hC ht hunique
  change IB n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩=
    IB n E+1 at hd
  omega
end Aw
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Ii (pre post:List Gate) (a b:ℕ) (z:List Bool):
    run (pre++⟨GateOp.or, [a,b]⟩::post) z=
      run (pre++⟨GateOp.or, [b,a]⟩::post) z:=by
  rw [run_append, run_append, run_cons, run_cons]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    id, Bool.or_false]
  rw [Bool.or_comm]
lemma Ks (pre post:List Gate) (a b out:ℕ) (z:List Bool):
    (⟨pre++⟨GateOp.or, [a,b]⟩::post, out⟩:Circuit).wires z=
      (⟨pre++⟨GateOp.or, [b,a]⟩::post, out⟩:Circuit).wires z:=
  Ii pre post a b z
lemma Dr (pre post:List Gate) (a b out:ℕ) (z:List Bool):
    (⟨pre++⟨GateOp.or, [a,b]⟩::post, out⟩:Circuit).eval z=
      (⟨pre++⟨GateOp.or, [b,a]⟩::post, out⟩:Circuit).eval z:=by
  unfold Circuit.eval
  rw [Ks pre post a b out z]
lemma Gx (pre post:List Gate) (a b out:ℕ):
    Monotone2 (⟨pre++⟨GateOp.or, [a,b]⟩::post, out⟩:Circuit)↔
      Monotone2 (⟨pre++⟨GateOp.or, [b,a]⟩::post, out⟩:Circuit):=by
  have swap (a b:ℕ)
      (hC:Monotone2 (⟨pre++⟨GateOp.or, [a,b]⟩::post, out⟩:Circuit)):
      Monotone2 (⟨pre++⟨GateOp.or, [b,a]⟩::post, out⟩:Circuit):=by
    intro g hg
    rcases List.mem_append.mp hg with hp | ht
    · exact hC g (by simp [hp])
    · rcases List.mem_cons.mp ht with rfl | hpost
      · simp
      · exact hC g (by simp [hpost])
  exact ⟨swap a b, swap b a⟩
lemma GX (pre post:List Gate) (a b r t:ℕ)
    (ht₁:t < (pre++⟨GateOp.or, [a,b]⟩::post).length)
    (ht₂:t < (pre++⟨GateOp.or, [b,a]⟩::post).length):
    r∈(pre++⟨GateOp.or, [a,b]⟩::post)[t].inputs↔
      r∈(pre++⟨GateOp.or, [b,a]⟩::post)[t].inputs:=by
  rcases Nat.lt_trichotomy t pre.length with hlt | rfl | hgt
  · rw [List.getElem_append_left hlt, List.getElem_append_left hlt]
  · simp [or_comm]
  · rw [List.getElem_append_right (Nat.le_of_lt hgt),
      List.getElem_append_right (Nat.le_of_lt hgt)]
    obtain ⟨k, hk⟩:∃ k, t=pre.length+(k+1):=⟨t-pre.length-1, by omega⟩
    subst t
    simp
lemma GY (pre post:List Gate) (a b r j:ℕ):
    (∀ (t:ℕ) (ht:t < (pre++⟨GateOp.or, [a,b]⟩::post).length),
      r∈(pre++⟨GateOp.or, [a,b]⟩::post)[t].inputs→t=j)↔
    (∀ (t:ℕ) (ht:t < (pre++⟨GateOp.or, [b,a]⟩::post).length),
      r∈(pre++⟨GateOp.or, [b,a]⟩::post)[t].inputs→t=j):=by
  constructor
  · intro h t ht hmem
    have ht':t < (pre++⟨GateOp.or, [a,b]⟩::post).length:=by simpa using ht
    exact h t ht' ((GX pre post a b r t ht' ht).mpr hmem)
  · intro h t ht hmem
    have ht':t < (pre++⟨GateOp.or, [b,a]⟩::post).length:=by simpa using ht
    exact h t ht' ((GX pre post a b r t ht ht').mp hmem)
end Aw
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Ar
open scoped BigOperators
lemma IC (n:ℕ) (pre post:List Gate) (a b out:ℕ):
    IB n ⟨pre++⟨GateOp.or, [a,b]⟩::post, out⟩=
      IB n ⟨pre++⟨GateOp.or, [b,a]⟩::post, out⟩:=by
  unfold IB
  apply Finset.sum_congr rfl
  intro i _
  rw [Ks pre post a b out]
lemma Jw (n:ℕ) (hn:2≤n) (i:Fin n) (h:ℕ)
    (pre post:List Gate) (out:ℕ)
    (hhi:h≠i.val) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (hout:out≠i.val)
    (hC:Monotone2 (⟨pre++⟨GateOp.or, [h,i.val]⟩::post, out⟩:Circuit))
    (ht:IW n ⟨pre++⟨GateOp.or, [h,i.val]⟩::post, out⟩)
    (hunique:∀ (t:ℕ) (ht:t < (pre++⟨GateOp.or, [h,i.val]⟩::post).length),
      i.val∈(pre++⟨GateOp.or, [h,i.val]⟩::post)[t].inputs→t=pre.length)
    (hsecondary:∀ E:Circuit, Monotone2 E→
      circuitFun n E=circuitFun n ⟨pre++⟨GateOp.or, [h,i.val]⟩::post, out⟩→
      E.size=(⟨pre++⟨GateOp.or, [h,i.val]⟩::post, out⟩:Circuit).size→
      IB n ⟨pre++⟨GateOp.or, [h,i.val]⟩::post, out⟩≤IB n E):
    False:=by
  have hCleft:=(Gx pre post h i.val out).mp hC
  have htleft:IW n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:=by
    intro z
    exact (Dr pre post i.val h out (List.ofFn z)).trans (ht z)
  have huleft:=(GY pre post h i.val i.val pre.length).mp hunique
  have hfun:circuitFun n ⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩=
      circuitFun n ⟨pre++⟨GateOp.or, [h,i.val]⟩::post, out⟩:=by
    funext z
    exact Dr pre post i.val h out (List.ofFn z)
  have hsize:(⟨pre++⟨GateOp.or, [i.val,h]⟩::post, out⟩:Circuit).size=
      (⟨pre++⟨GateOp.or, [h,i.val]⟩::post, out⟩:Circuit).size:=by
    simp [Circuit.size]
  apply Jv n hn i h pre post out hhi hh hpre hout
    hCleft htleft huleft
  intro E hE hfunE hsizeE
  have hm:=hsecondary E hE (hfunE.trans hfun) (hsizeE.trans hsize)
  rw [IC n pre post i.val h out]
  exact hm
lemma Jy (n:ℕ) (hn:2≤n) (i:Fin n) (h:ℕ)
    (pre post:List Gate) (out:ℕ) (g:Gate)
    (hop:g.op=GateOp.or)
    (hports:g.inputs=[i.val,h]∨g.inputs=[h,i.val])
    (hhi:h≠i.val) (hh:h < n+pre.length)
    (hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length)
    (hout:out≠i.val)
    (hC:Monotone2 (⟨pre++g::post, out⟩:Circuit))
    (ht:IW n ⟨pre++g::post, out⟩)
    (hunique:∀ (t:ℕ) (ht:t < (pre++g::post).length),
      i.val∈(pre++g::post)[t].inputs→t=pre.length)
    (hsecondary:∀ E:Circuit, Monotone2 E→
      circuitFun n E=circuitFun n ⟨pre++g::post, out⟩→
      E.size=(⟨pre++g::post, out⟩:Circuit).size→
      IB n ⟨pre++g::post, out⟩≤IB n E):
    False:=by
  obtain ⟨op, inputs⟩:=g
  dsimp only at hop hports
  subst op
  rcases hports with rfl | rfl
  · exact Jv n hn i h pre post out hhi hh hpre hout
      hC ht hunique hsecondary
  · exact Jw n hn i h pre post out hhi hh hpre hout
      hC ht hunique hsecondary
end Aw
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Ar
lemma Je (n:ℕ) (C:Circuit) (ht:IW n C) (i:Fin n):
    C.output≠i.val:=by
  intro heq
  have hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card):=by
    intro S
    simpa using ht (fun t=>decide (t∈S))
  have hs:=hcorrect ({i}:Finset (Fin n))
  change (run C.gates (List.ofFn (fun t:Fin n=>decide (t∈({i}:Finset (Fin n)))))).getD C.output false=_ at hs
  rw [heq, Ig C.gates _ i.val (by simpa using i.isLt)] at hs
  simp [List.getD_eq_getElem?_getD, i.isLt] at hs
lemma GF (n:ℕ) (hn:2≤n) (C:Circuit)
    (hC:Monotone2 C) (ht:IW n C)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)
    (hsecondary:∀ E:Circuit, Monotone2 E→circuitFun n E=circuitFun n C→
      E.size=C.size→IB n C≤IB n E)
    (i:Fin n) (j:ℕ) (hj:j < C.gates.length)
    (hread:i.val∈C.gates[j].inputs)
    (hunique:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j):
    C.gates[j].op≠GateOp.or:=by
  intro hop
  obtain ⟨a,b,hab,hdist,ha,hb⟩:=hshape j hj
  have hmember:i.val=a∨i.val=b:=by simpa [hab] using hread
  obtain ⟨h,hports,hhi,hh⟩:∃ h,
      (C.gates[j].inputs=[i.val,h]∨C.gates[j].inputs=[h,i.val])∧
      h≠i.val∧h < n+j:=by
    rcases hmember with hai | hbi
    · refine ⟨b, Or.inl ?_, ?_, hb⟩
      · simpa [hai] using hab
      · simpa [hai] using Ne.symm hdist
    · refine ⟨a, Or.inr ?_, ?_, ha⟩
      · simpa [hbi] using hab
      · simpa [hbi] using hdist
  let pre:=C.gates.take j
  let post:=C.gates.drop (j+1)
  have hplen:pre.length=j:=by simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hsplit:pre++C.gates[j]::post=C.gates:=by
    change C.gates.take j++C.gates[j]::C.gates.drop (j+1)=C.gates
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hc:(⟨pre++C.gates[j]::post, C.output⟩:Circuit)=C:=by
    cases C
    exact congrArg (fun l=>Circuit.mk l _) hsplit
  have hpre:∀ g∈pre, ∀ w∈g.inputs, w < n+pre.length:=by
    intro g hg w hw
    obtain ⟨t,ht,hg⟩:=List.mem_iff_getElem.mp hg
    have htj:t < j:=by simpa [hplen] using ht
    have htC:t < C.gates.length:=lt_trans htj hj
    have hgate:pre[t]=C.gates[t]:=by simp [pre]
    have hw':w∈C.gates[t].inputs:=by rw [← hgate, hg]; exact hw
    obtain ⟨a,b,hports,hdist,ha,hb⟩:=hshape t htC
    have hwab:w=a∨w=b:=by simpa [hports] using hw'
    rcases hwab with rfl | rfl <;> omega
  apply Jy n hn i h pre post C.output C.gates[j]
    hop hports hhi (by simpa [hplen] using hh) hpre (Je n C ht i)
  · simpa only [hc] using hC
  · simpa only [hc] using ht
  · intro t ht hmem
    have htC:t < C.gates.length:=by simpa only [hsplit] using ht
    have hmC:i.val∈C.gates[t].inputs:=by simpa only [hsplit] using hmem
    simpa only [hplen] using hunique t htC hmC
  · simpa only [hc] using hsecondary
end Aw
namespace Ao
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Gc (n:ℕ) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C)
    (hne:¬∃ b, ∀ x:Fin n→Bool, C.eval (List.ofFn x)=b)
    (j:ℕ) (hj:j < C.gates.length):
    ¬((∃ b, ∀ x:Fin n→Bool,
        (run C.gates (List.ofFn x)).getD (n+j) false=b)∨
      ∃ w < n+j, ∀ x:Fin n→Bool,
        (run C.gates (List.ofFn x)).getD (n+j) false=
          (run C.gates (List.ofFn x)).getD w false):=by
  intro halias
  have hlen:∀ x:Fin n→Bool, (List.ofFn x).length=n:=by simp
  have hinit:∀ w < n,
      (∃ b, ∀ x:Fin n→Bool, (List.ofFn x).getD w false=b)∨
        ∃ t, t < n∧∀ x:Fin n→Bool,
          (List.ofFn x).getD w false=(List.ofFn x).getD t false:=by
    intro w hw
    exact Or.inr ⟨w, hw, fun _=>rfl⟩
  obtain ⟨D, hD, hsize, heval⟩:=Dq n n C List.ofFn List.ofFn hlen hlen {j}
    hmin.1 hinit hne (by
      intro k hk
      have heq:=Finset.mem_singleton.mp hk
      subst k
      exact ⟨hj, halias⟩)
  have hfun:circuitFun n D=circuitFun n C:=funext heval
  have hge:=hmin.2 D hD hfun
  simp only [Finset.card_singleton] at hsize
  omega
lemma EV (N:ℕ) (op:GateOp) (args:List ℕ)
    (hop:op=GateOp.and∨op=GateOp.or) (hlen:args.length≤2):
    (∃ a b, args=[a,b]∧a≠b∧a < N∧b < N)∨
    (∃ c, ∀ V:ℕ→Bool,
      op.eval (args.map (fun i=>if i < N then V i else false))=c)∨
    (∃ a < N, ∀ V:ℕ→Bool,
      op.eval (args.map (fun i=>if i < N then V i else false))=V a):=by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact Or.inr (Or.inl ⟨true, by simp [GateOp.eval]⟩)
    · exact Or.inr (Or.inl ⟨false, by simp [GateOp.eval]⟩)
  · by_cases ha:a < N
    · right; right; refine ⟨a, ha, ?_⟩
      rcases hop with rfl | rfl <;> simp [GateOp.eval, ha]
    · right; left; refine ⟨false, ?_⟩
      rcases hop with rfl | rfl <;> simp [GateOp.eval, ha]
  · by_cases ha:a < N
    · by_cases hb:b < N
      · by_cases hab:a=b
        · subst b
          right; right; refine ⟨a, ha, ?_⟩
          rcases hop with rfl | rfl <;> simp [GateOp.eval, ha]
        · exact Or.inl ⟨a, b, rfl, hab, ha, hb⟩
      · rcases hop with rfl | rfl
        · right; left; exact ⟨false, by simp [GateOp.eval, hb]⟩
        · right; right; exact ⟨a, ha, by simp [GateOp.eval, ha, hb]⟩
    · rcases hop with rfl | rfl
      · right; left; exact ⟨false, by simp [GateOp.eval, ha]⟩
      · by_cases hb:b < N
        · right; right; exact ⟨b, hb, by simp [GateOp.eval, ha, hb]⟩
        · right; left; exact ⟨false, by simp [GateOp.eval, ha, hb]⟩
  · simp at hlen
lemma FZ (n:ℕ) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C)
    (hne:¬∃ b, ∀ x:Fin n→Bool, C.eval (List.ofFn x)=b)
    (j:ℕ) (hj:j < C.gates.length):
    ∃ a b, C.gates[j].inputs=[a,b]∧a≠b∧a < n+j∧b < n+j:=by
  have hg:=hmin.1 C.gates[j] (List.getElem_mem hj)
  have hop:C.gates[j].op=GateOp.and∨C.gates[j].op=GateOp.or:=by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  have hcases:=EV (n+j) C.gates[j].op C.gates[j].inputs hop hg.2
  rcases hcases with hnormal | hconst | halias
  · exact hnormal
  · exfalso
    apply Gc n C hmin hne j hj
    left
    obtain ⟨c, hc⟩:=hconst
    refine ⟨c, fun x=>?_⟩
    have he:=If C.gates (List.ofFn x) j hj
    simp only [List.length_ofFn] at he
    rw [he]
    exact hc (fun w=>(run C.gates (List.ofFn x)).getD w false)
  · exfalso
    apply Gc n C hmin hne j hj
    right
    obtain ⟨a, ha, heval⟩:=halias
    refine ⟨a, ha, fun x=>?_⟩
    have he:=If C.gates (List.ofFn x) j hj
    simp only [List.length_ofFn] at he
    rw [he]
    exact heval (fun w=>(run C.gates (List.ofFn x)).getD w false)
lemma Gh (n:ℕ) (hn:2≤n)
    (C:Circuit) (hmin:IsMinimalMonoCircuit n C) (ht:IW n C)
    (j:ℕ) (hj:j < C.gates.length):
    ∃ a b, C.gates[j].inputs=[a,b]∧a≠b∧a < n+j∧b < n+j:=by
  exact FZ n C hmin (Jb n hn C ht) j hj
end Ao
namespace Aw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Ar
lemma Gf (n:ℕ) (hn:2≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C)
    (hsecondary:∀ E:Circuit, Monotone2 E→circuitFun n E=circuitFun n C→
      E.size=C.size→IB n C≤IB n E)
    (i:Fin n) (j:ℕ) (hj:j < C.gates.length)
    (hread:i.val∈C.gates[j].inputs)
    (hunique:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j):
    C.gates[j].op=GateOp.and:=by
  have hnot:=GF n hn C hmin.1 ht
    (Ao.Gh n hn C hmin ht)
    hsecondary i j hj hread hunique
  have hgate:=hmin.1 C.gates[j] (List.getElem_mem hj)
  have hop:C.gates[j].op=GateOp.and∨C.gates[j].op=GateOp.or:=by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hgate.1
  exact hop.resolve_right hnot
end Aw
namespace Ar
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma DE (n:ℕ) (C:Circuit) (hC:Monotone2 C):
    ∃ D:Circuit, circuitFun n D=circuitFun n C∧D.size≤C.size∧
      IsMinimalMonoCircuit n D∧
      ∀ E:Circuit, Monotone2 E→circuitFun n E=circuitFun n D→
        E.size=D.size→IB n D≤IB n E:=by
  classical
  let P:ℕ→Prop:=fun size=>
    ∃ E:Circuit, Monotone2 E∧circuitFun n E=circuitFun n C∧E.size=size
  have hP:∃ size, P size:=⟨C.size, C, hC, rfl, rfl⟩
  let Q:ℕ→Prop:=fun mass=>
    ∃ E:Circuit, Monotone2 E∧circuitFun n E=circuitFun n C∧
      E.size=Nat.find hP∧IB n E=mass
  have hQ:∃ mass, Q mass:=by
    obtain ⟨E, hE, hfun, hsize⟩:=Nat.find_spec hP
    exact ⟨IB n E, E, hE, hfun, hsize, rfl⟩
  obtain ⟨D, hD, hfunD, hsizeD, hmassD⟩:=Nat.find_spec hQ
  have hmin:IsMinimalMonoCircuit n D:=by
    refine ⟨hD, ?_⟩
    intro E hE hfunE
    rw [hsizeD]
    exact Nat.find_min' hP ⟨E, hE, hfunE.trans hfunD, rfl⟩
  refine ⟨D, hfunD, ?_, hmin, ?_⟩
  · rw [hsizeD]
    exact Nat.find_min' hP ⟨C, hC, rfl, rfl⟩
  · intro E hE hfunE hsizeE
    rw [hmassD]
    exact Nat.find_min' hQ ⟨E, hE, hfunE.trans hfunD, hsizeE.trans hsizeD, rfl⟩
end Ar
namespace Ar
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma DC
    (n:ℕ) (hn:2≤n) (C:Circuit) (hC:Monotone2 C) (htC:IW n C):
    ∃ D:Circuit, circuitFun n D=circuitFun n C∧D.size≤C.size∧
      IsMinimalMonoCircuit n D∧IW n D∧
      (∀ E:Circuit, Monotone2 E→circuitFun n E=circuitFun n D→
        E.size=D.size→IB n D≤IB n E)∧
      (∀ (t:ℕ) (ht:t < D.gates.length),
        ∃ a b, D.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)∧
      (∀ (i:Fin n) (j:ℕ) (hj:j < D.gates.length),
        i.val∈D.gates[j].inputs→
        (∀ (t:ℕ) (ht:t < D.gates.length), i.val∈D.gates[t].inputs→t=j)→
        D.gates[j].op=GateOp.and):=by
  obtain ⟨D, hfun, hsize, hminimum, hsecondary⟩:=
    DE n C hC
  have htD:IW n D:=by
    intro z
    exact (congrFun hfun z).trans (htC z)
  refine ⟨D, hfun, hsize, hminimum, htD, hsecondary, ?_, ?_⟩
  · exact Ao.Gh n hn D hminimum htD
  · intro i j hj hread hunique
    exact Aw.Gf n hn D hminimum htD
      hsecondary i j hj hread hunique
end Ar
namespace At
open scoped BigOperators
lemma JZ {I J:Type} [Fintype I] [Fintype J]
    (rawWeight:I→ℕ) (gateWeight code:J→ℕ)
    (rawEdges:J→I→ℕ) (gateEdges:J→J→ℕ)
    (hlocal:∀ j, gateWeight j+code j≤
      (∑ i:I, rawEdges j i*rawWeight i)+
        ∑ k:J, gateEdges j k*gateWeight k):
    (∑ j:J, code j)≤
      (∑ i:I, (∑ j:J, rawEdges j i)*rawWeight i)+
        ∑ k:J, ((∑ j:J, gateEdges j k) - 1)*gateWeight k:=by
  classical
  have hs:=Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset J))=>hlocal j)
  simp only [Finset.sum_add_distrib] at hs
  have hraw:(∑ j:J, ∑ i:I, rawEdges j i*rawWeight i)=
      ∑ i:I, (∑ j:J, rawEdges j i)*rawWeight i:=by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  have hgate:(∑ j:J, ∑ k:J, gateEdges j k*gateWeight k)=
      ∑ k:J, (∑ j:J, gateEdges j k)*gateWeight k:=by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [hraw, hgate] at hs
  have hbound:(∑ k:J, (∑ j:J, gateEdges j k)*gateWeight k)≤
      (∑ k:J, gateWeight k)+
        ∑ k:J, ((∑ j:J, gateEdges j k) - 1)*gateWeight k:=by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k _
    have hq:(∑ j:J, gateEdges j k)≤1+((∑ j:J, gateEdges j k) - 1):=by omega
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right (gateWeight k) hq
  omega
lemma Ka (n G:ℕ)
    (weight:Fin (n+G)→ℕ) (code:Fin G→ℕ)
    (edges:Fin G→Fin (n+G)→ℕ)
    (hlocal:∀ j:Fin G, weight (Fin.natAdd n j)+code j≤
      ∑ w:Fin (n+G), edges j w*weight w):
    (∑ j:Fin G, code j)≤
      (∑ i:Fin n, (∑ j:Fin G, edges j (Fin.castAdd G i))*weight (Fin.castAdd G i))+
        ∑ k:Fin G, ((∑ j:Fin G, edges j (Fin.natAdd n k)) - 1)*weight (Fin.natAdd n k):=by
  apply JZ
    (fun i:Fin n=>weight (Fin.castAdd G i))
    (fun j:Fin G=>weight (Fin.natAdd n j)) code
    (fun j i=>edges j (Fin.castAdd G i))
    (fun j k=>edges j (Fin.natAdd n k))
  intro j
  simpa only [Fin.sum_univ_add] using hlocal j
end At
namespace At
open scoped BigOperators
end At
namespace At
open scoped BigOperators
lemma Kb (l:List ℕ) (M:ℕ) (f:ℕ→ℕ)
    (hbound:∀ a∈l, a < M):
    (∑ w:Fin M, l.count w.val*f w.val)=(l.map f).sum:=by
  induction l with
  | nil=>simp
  | cons a l ih=>
    have ha:a < M:=hbound a (by simp)
    have hl:∀ b∈l, b < M:=fun b hb=>hbound b (by simp [hb])
    have hc:∀ w:Fin M,
        (a::l).count w.val*f w.val=
          (if w.val=a then f a else 0)+l.count w.val*f w.val:=by
      intro w
      by_cases hwa:w.val=a
      · simp [hwa, Nat.add_mul, Nat.add_comm]
      · simp [hwa, Ne.symm hwa]
    have hsingle:(∑ w:Fin M, if w.val=a then f a else 0)=f a:=by
      have heq:∀ w:Fin M, w.val=a↔w=⟨a, ha⟩:=by
        intro w
        exact ⟨fun h=>Fin.ext h, fun h=>congrArg Fin.val h⟩
      simp_rw [heq]
      simp
    calc
      (∑ w:Fin M, (a::l).count w.val*f w.val)=
          ∑ w:Fin M, ((if w.val=a then f a else 0)+l.count w.val*f w.val):=
        Finset.sum_congr rfl (fun w _=>hc w)
      _=(∑ w:Fin M, if w.val=a then f a else 0)+
          ∑ w:Fin M, l.count w.val*f w.val:=Finset.sum_add_distrib
      _=f a+(l.map f).sum:=by rw [hsingle, ih hl]
      _=((a::l).map f).sum:=by simp
lemma DT (l:List ℕ) (N:ℕ) (f:ℕ→ℕ):
    ((l.filter (fun a=>a < N)).map f).sum=
      (l.map (fun a=>if a < N then f a else 0)).sum:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>
    by_cases ha:a < N <;> simp [ha, ih]
lemma JY (l:List ℕ) (N M:ℕ) (f:ℕ→ℕ)
    (hNM:N≤M):
    (∑ w:Fin M, (l.filter (fun a=>a < N)).count w.val*f w.val)=
      (l.map (fun a=>if a < N then f a else 0)).sum:=by
  rw [Kb _ M f (by
    intro a ha
    have hlt:a < N:=by simpa using (List.mem_filter.mp ha).2
    omega)]
  exact DT l N f
end At
namespace As
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
def Iv (lo hi:Bool):ℕ:=if lo then 0 else if hi then 1 else 0
def Du:GateOp→List (Bool × Bool)→ℕ
  | .and, [(false, a), (false, b)]=>if a=b then 0 else 1
  | _, _=>0
lemma Fc (op:GateOp) (hop:op=.and∨op=.or)
    (rs:List (Bool × Bool)) (hlen:rs.length≤2):
    Iv (op.eval (rs.map Prod.fst)) (op.eval (rs.map Prod.snd))+
        Du op rs≤(rs.map fun p=>Iv p.1 p.2).sum:=by
  rcases rs with _ | ⟨⟨a₀,a₁⟩, _ | ⟨⟨b₀,b₁⟩, _ | ⟨c,rest⟩⟩⟩
  · rcases hop with rfl | rfl <;> decide
  · rcases hop with rfl | rfl <;> cases a₀ <;> cases a₁ <;> decide
  · rcases hop with rfl | rfl <;> cases a₀ <;> cases a₁ <;>
      cases b₀ <;> cases b₁ <;> decide
  · simp at hlen
def Kf (C:Circuit) (lo hi:List Bool) (w:ℕ):ℕ:=
  Iv ((C.wires lo).getD w false) ((C.wires hi).getD w false)
def GW (C:Circuit) (lo hi:List Bool) (j:Fin C.gates.length):
    List (Bool × Bool):=
  C.gates[j.val].inputs.map fun w=>
    (if w < lo.length+j.val then (C.wires lo).getD w false else false,
      if w < hi.length+j.val then (C.wires hi).getD w false else false)
def gateCode (C:Circuit) (lo hi:List Bool) (j:Fin C.gates.length):ℕ:=
  Du C.gates[j.val].op (GW C lo hi j)
lemma Bc (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (lo hi:List Bool) (hlo:lo.length=n) (hhi:hi.length=n)
    (j:Fin C.gates.length):
    Kf C lo hi (n+j.val)+gateCode C lo hi j≤
      (C.gates[j.val].inputs.map fun w=>
        if w < n+j.val then Kf C lo hi w else 0).sum:=by
  have hg:=hC C.gates[j.val] (List.getElem_mem j.isLt)
  have hop:C.gates[j.val].op=GateOp.and∨C.gates[j.val].op=GateOp.or:=hg.1
  have hflow:=Fc C.gates[j.val].op hop (GW C lo hi j)
    (by simpa [GW] using hg.2)
  have helo:=If C.gates lo j.val j.isLt
  have hehi:=If C.gates hi j.val j.isLt
  change (C.wires lo).getD (lo.length+j.val) false=_ at helo
  change (C.wires hi).getD (hi.length+j.val) false=_ at hehi
  simp only [hlo] at helo
  simp only [hhi] at hehi
  change Iv ((C.wires lo).getD (n+j.val) false)
      ((C.wires hi).getD (n+j.val) false)+_≤_
  rw [helo, hehi]
  have hmap:((GW C lo hi j).map fun p=>Iv p.1 p.2)=
      C.gates[j.val].inputs.map (fun w=>if w < n+j.val then Kf C lo hi w else 0):=by
    simp only [GW, List.map_map, hlo, hhi]
    apply List.map_congr_left
    intro w _
    by_cases hw:w < n+j.val <;> simp [hw, Kf, Iv]
  rw [hmap] at hflow
  simpa only [GW, List.map_map, Function.comp_def, hlo, hhi, gateCode,
    Circuit.wires, run] using hflow
end As
namespace As
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open scoped BigOperators
def JN (C:Circuit) (n:ℕ) (j:Fin C.gates.length) (w:ℕ):ℕ:=
  (C.gates[j.val].inputs.filter (fun a=>decide (a < n+j.val))).count w
def JI (C:Circuit) (n w:ℕ):ℕ:=
  ∑ j:Fin C.gates.length, JN C n j w
lemma HF (n:ℕ) (C:Circuit) (lo hi:List Bool)
    (hlo:lo.length=n) (hhi:hi.length=n) (i:Fin n):
    Kf C lo hi i.val=Iv (lo.getD i.val false) (hi.getD i.val false):=by
  change Iv ((run C.gates lo).getD i.val false) ((run C.gates hi).getD i.val false)=_
  rw [Ig C.gates lo i.val (by rw [hlo]; exact i.isLt),
    Ig C.gates hi i.val (by rw [hhi]; exact i.isLt)]
def Ku (n:ℕ):List Bool:=List.ofFn (fun _:Fin n=>false)
def IA {n:ℕ} (i:Fin n):List Bool:=
  List.ofFn (fun k=>decide (k=i))
lemma IH (n:ℕ) (C:Circuit) (i k:Fin n):
    Kf C (Ku n) (IA i) k.val=if k=i then 1 else 0:=by
  rw [HF n C _ _ (by simp [Ku]) (by simp [IA]) k]
  simp [Ku, IA, List.getD_eq_getElem?_getD, k.isLt, Iv]
end As
namespace As
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators
end As
namespace As
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open scoped BigOperators
def Ee (C:Circuit) (F:Finset ℕ):Circuit:=
  ⟨C.gates.mapIdx (fun j g=>if j∈F then ⟨GateOp.and, []⟩ else g), C.output⟩
lemma Ej (C:Circuit) (F:Finset ℕ):
    (Ee C F).gates.length=C.gates.length:=by simp [Ee]
lemma Eg (C:Circuit) (F:Finset ℕ) (j:ℕ) (hj:j < C.gates.length):
    (Ee C F).gates[j]'(by simpa [Ee] using hj)=
      if j∈F then ⟨GateOp.and, []⟩ else C.gates[j]:=by
  simp [Ee]
lemma Ek (C:Circuit) (F:Finset ℕ) (hC:Monotone2 C):
    Monotone2 (Ee C F):=by
  intro g hg
  obtain ⟨j, hj, rfl⟩:=List.mem_iff_getElem.mp hg
  have hjC:j < C.gates.length:=by simpa [Ee] using hj
  rw [Eg C F j hjC]
  split_ifs with hF
  · simp
  · exact hC _ (List.getElem_mem hjC)
def Ex (C:Circuit) (F:Finset ℕ) (j:Fin C.gates.length):
    Fin (Ee C F).gates.length:=⟨j.val, by rw [Ej]; exact j.isLt⟩
def Eu (C:Circuit) (F:Finset ℕ) (lo hi:List Bool) (j:Fin C.gates.length):ℕ:=
  gateCode (Ee C F) lo hi (Ex C F j)
def Dn (n:ℕ) (C:Circuit) (F:Finset ℕ) (lo hi:List Bool)
    (j:Fin C.gates.length):ℕ:=
  if j.val∈F then
    (C.gates[j.val].inputs.map (fun w=>
      if w < n+j.val then Kf (Ee C F) lo hi w else 0)).sum
  else 0
lemma Ei (n:ℕ) (C:Circuit) (F:Finset ℕ)
    (j:Fin C.gates.length) (hjF:j.val∈F) (z:List Bool) (hz:z.length=n):
    ((Ee C F).wires z).getD (n+j.val) false=true:=by
  have he:=If (Ee C F).gates z j.val
    (by rw [Ej]; exact j.isLt)
  rw [Eg C F j.val j.isLt] at he
  simpa only [hz, hjF, ite_true, List.map_nil, GateOp.eval, List.all_nil,
    Circuit.wires, run] using he
lemma Eh (n:ℕ) (C:Circuit) (F:Finset ℕ)
    (j:Fin C.gates.length) (hjF:j.val∈F) (lo hi:List Bool)
    (hlo:lo.length=n) (_hhi:hi.length=n):
    Kf (Ee C F) lo hi (n+j.val)=0:=by
  unfold Kf
  rw [Ei n C F j hjF lo hlo]
  rfl
lemma Ew (C:Circuit) (F:Finset ℕ) (j:Fin C.gates.length)
    (hjF:j.val∈F) (lo hi:List Bool):Eu C F lo hi j=0:=by
  simp [Eu, gateCode, GW, Ex, Ee, hjF, Du]
lemma Ez (n:ℕ) (C:Circuit) (hC:Monotone2 C) (F:Finset ℕ)
    (lo hi:List Bool) (hlo:lo.length=n) (hhi:hi.length=n)
    (j:Fin C.gates.length):
    Kf (Ee C F) lo hi (n+j.val)+Eu C F lo hi j+
      Dn n C F lo hi j≤
    (C.gates[j.val].inputs.map (fun w=>
      if w < n+j.val then Kf (Ee C F) lo hi w else 0)).sum:=by
  by_cases hjF:j.val∈F
  · rw [Eh n C F j hjF lo hi hlo hhi,
      Ew C F j hjF lo hi, Dn, ite_eq_left hjF]
    simp
  · have hlocal:=Bc n (Ee C F) (Ek C F hC)
      lo hi hlo hhi (Ex C F j)
    have hjD:j.val < (Ee C F).gates.length:=by
      rw [Ej]
      exact j.isLt
    change Kf (Ee C F) lo hi (n+j.val)+Eu C F lo hi j≤
      ((Ee C F).gates[j.val].inputs.map (fun w=>
        if w < n+j.val then Kf (Ee C F) lo hi w else 0)).sum at hlocal
    rw [Eg C F j.val j.isLt, ite_eq_right hjF] at hlocal
    simpa only [Dn, hjF, ite_false, Nat.add_zero] using hlocal
lemma EA (n:ℕ) (C:Circuit) (hC:Monotone2 C) (F:Finset ℕ)
    (lo hi:List Bool) (hlo:lo.length=n) (hhi:hi.length=n)
    (j:Fin C.gates.length):
    Kf (Ee C F) lo hi (n+j.val)+
      (Eu C F lo hi j+Dn n C F lo hi j)≤
      ∑ w:Fin (n+C.gates.length),
        JN C n j w.val*Kf (Ee C F) lo hi w.val:=by
  have hsum:=At.JY
    C.gates[j.val].inputs (n+j.val) (n+C.gates.length)
    (Kf (Ee C F) lo hi) (by have:=j.isLt; omega)
  change (∑ w:Fin (n+C.gates.length),
      JN C n j w.val*Kf (Ee C F) lo hi w.val)=
    (C.gates[j.val].inputs.map (fun w=>
      if w < n+j.val then Kf (Ee C F) lo hi w else 0)).sum at hsum
  rw [hsum]
  simpa only [Nat.add_assoc] using Ez n C hC F lo hi hlo hhi j
lemma EC (n:ℕ) (C:Circuit) (hC:Monotone2 C) (F:Finset ℕ)
    (lo hi:List Bool) (hlo:lo.length=n) (hhi:hi.length=n):
    (∑ j:Fin C.gates.length, Eu C F lo hi j)+
      (∑ j:Fin C.gates.length, Dn n C F lo hi j)≤
      (∑ i:Fin n, JI C n i.val*Kf (Ee C F) lo hi i.val)+
      ∑ j:Fin C.gates.length, (JI C n (n+j.val)-1)*
        Kf (Ee C F) lo hi (n+j.val):=by
  have h:=At.Ka n C.gates.length
    (fun w=>Kf (Ee C F) lo hi w.val)
    (fun j=>Eu C F lo hi j+Dn n C F lo hi j)
    (fun j w=>JN C n j w.val)
    (EA n C hC F lo hi hlo hhi)
  simp only [Finset.sum_add_distrib] at h
  exact h
lemma EE (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (F:Finset ℕ) (i:Fin n):
    (∑ j:Fin C.gates.length, Eu C F (Ku n) (IA i) j)+
      (∑ j:Fin C.gates.length, Dn n C F (Ku n) (IA i) j)≤
      JI C n i.val+
      ∑ j:Fin C.gates.length, (JI C n (n+j.val)-1)*
        Kf (Ee C F) (Ku n) (IA i) (n+j.val):=by
  have hflow:=EC n C hC F (Ku n) (IA i)
    (by simp [Ku]) (by simp [IA])
  have hraw:(∑ k:Fin n, JI C n k.val*
      Kf (Ee C F) (Ku n) (IA i) k.val)=JI C n i.val:=by
    simp only [IH]
    simp
  rw [hraw] at hflow
  exact hflow
end As
namespace As
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma El (C:Circuit) (F:Finset ℕ) (j:ℕ)
    (hbefore:∀ k < j, k∉F):
    (Ee C F).gates.take j=C.gates.take j:=by
  apply List.ext_getElem (by simp [Ee])
  intro k hk₁ hk₂
  have hkj:k < j:=by
    have hlt:k < min j C.gates.length:=by simpa only [List.length_take] using hk₂
    omega
  simp only [Ee, List.getElem_take, List.getElem_mapIdx,
    ite_eq_right (hbefore k hkj)]
lemma En (n:ℕ) (C:Circuit) (F:Finset ℕ) (j:ℕ)
    (hj:j≤C.gates.length) (hbefore:∀ k < j, k∉F)
    (x:List Bool) (hx:x.length=n) (w:ℕ) (hw:w < n+j):
    ((Ee C F).wires x).getD w false=(C.wires x).getD w false:=by
  have hf_len:j≤(Ee C F).gates.length:=by simpa [Ee] using hj
  have hc:=Ij (C.gates.take j) (C.gates.drop j) x w
    (by simpa only [hx, List.length_take, Nat.min_eq_left hj] using hw)
  have hf:=Ij ((Ee C F).gates.take j) ((Ee C F).gates.drop j) x w
    (by simpa only [hx, List.length_take, Nat.min_eq_left hf_len] using hw)
  rw [List.take_append_drop] at hc hf
  change (run (Ee C F).gates x).getD w false=(run C.gates x).getD w false
  rw [hf, El C F j hbefore]
  exact hc.symm
lemma Em (n:ℕ) (C:Circuit) (F:Finset ℕ) (j:ℕ)
    (hj:j≤C.gates.length) (hbefore:∀ k < j, k∉F)
    (lo hi:List Bool) (hlo:lo.length=n) (hhi:hi.length=n)
    (w:ℕ) (hw:w < n+j):
    Kf (Ee C F) lo hi w=Kf C lo hi w:=by
  unfold Kf
  rw [En n C F j hj hbefore lo hlo w hw,
    En n C F j hj hbefore hi hhi w hw]
lemma Do (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (F:Finset ℕ) (lo hi:List Bool) (hlo:lo.length=n) (hhi:hi.length=n)
    (j:Fin C.gates.length) (hjF:j.val∈F)
    (hbefore:∀ k < j.val, k∉F)
    (hzero:(C.wires lo).getD (n+j.val) false=false)
    (hone:(C.wires hi).getD (n+j.val) false=true):
    1≤Dn n C F lo hi j:=by
  have hflow:=Bc n C hC lo hi hlo hhi j
  have hweight:Kf C lo hi (n+j.val)=1:=by
    unfold Kf
    rw [hzero, hone]
    rfl
  rw [hweight] at hflow
  have hmap:(C.gates[j.val].inputs.map (fun w=>
      if w < n+j.val then Kf (Ee C F) lo hi w else 0))=
      (C.gates[j.val].inputs.map (fun w=>
        if w < n+j.val then Kf C lo hi w else 0)):=by
    apply List.map_congr_left
    intro w _
    by_cases hw:w < n+j.val
    · simp only [ite_eq_left hw]
      exact Em n C F j.val (Nat.le_of_lt j.isLt) hbefore
        lo hi hlo hhi w hw
    · simp [hw]
  rw [Dn, ite_eq_left hjF, hmap]
  omega
end As
namespace As
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators
lemma EF (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (F:Finset ℕ) (i:Fin n) (j:Fin C.gates.length)
    (hjF:j.val∈F) (hbefore:∀ k < j.val, k∉F)
    (hzero:(C.wires (Ku n)).getD (n+j.val) false=false)
    (hone:(C.wires (IA i)).getD (n+j.val) false=true):
    (∑ k:Fin C.gates.length, Eu C F (Ku n) (IA i) k)+1≤
      JI C n i.val+
      ∑ k:Fin C.gates.length, (JI C n (n+k.val)-1)*
        Kf (Ee C F) (Ku n) (IA i) (n+k.val):=by
  have hflow:=EE n C hC F i
  have hloss:=Do n C hC F (Ku n) (IA i)
    (by simp [Ku]) (by simp [IA]) j hjF hbefore hzero hone
  have hsum:Dn n C F (Ku n) (IA i) j≤
      ∑ k:Fin C.gates.length, Dn n C F (Ku n) (IA i) k:=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  omega
lemma EG (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (F:Finset ℕ) (i:Fin n) (j:Fin C.gates.length)
    (hjF:j.val∈F) (hbefore:∀ k < j.val, k∉F)
    (hzero:(C.wires (Ku n)).getD (n+j.val) false=false)
    (hone:(C.wires (IA i)).getD (n+j.val) false=true)
    (hraw:JI C n i.val≤2):
    (∑ k:Fin C.gates.length, Eu C F (Ku n) (IA i) k)≤
      1+∑ k:Fin C.gates.length, (JI C n (n+k.val)-1)*
        Kf (Ee C F) (Ku n) (IA i) (n+k.val):=by
  have h:=EF n C hC F i j hjF hbefore hzero hone
  omega
end As
namespace AD
def Ip (z x:Bool):ℕ:=if z=false∧x=true then 1 else 0
def Iw (az bz ax bx:Bool):ℕ:=
  if az=false∧bz=false∧ax≠bx then 1 else 0
lemma Iq (az bz ax bx:Bool)
    (ha:az=true→ax=true) (hb:bz=true→bx=true):
    Iw az bz ax bx+Ip (az && bz) (ax && bx)≤
      Ip az ax+Ip bz bx:=by
  cases az <;> cases bz <;> cases ax <;> cases bx <;>
    simp_all [Iw, Ip]
lemma It (az bz ax bx:Bool):
    Ip (az || bz) (ax || bx)≤Ip az ax+Ip bz bx:=by
  cases az <;> cases bz <;> cases ax <;> cases bx <;>
    simp [Ip]
lemma Is (z x:Bool):
    Ip z x≤ if x then 1 else 0:=by
  cases z <;> cases x <;> decide
open PEqualNP.CircuitLowerBounds
def ES (g:Gate) (z x:ℕ→Bool):ℕ:=
  match g.op, g.inputs with
  | .and, [a, b]=>Iw (z a) (z b) (x a) (x b)
  | _, _=>0
lemma EZ (g:Gate) (z x:ℕ→Bool)
    (hop:g.op=.and∨g.op=.or) (hsize:g.inputs.length≤2)
    (hmono:∀ w, z w=true→x w=true):
    ES g z x+
      Ip (g.op.eval (g.inputs.map z)) (g.op.eval (g.inputs.map x))≤
      (g.inputs.map (fun w=>Ip (z w) (x w))).sum:=by
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil=>
    rcases hop with rfl | rfl <;> simp [ES, GateOp.eval, Ip]
  | cons a tail=>
    cases tail with
    | nil=>
      rcases hop with rfl | rfl <;> simp [ES, GateOp.eval]
    | cons b rest=>
      cases rest with
      | nil=>
        rcases hop with rfl | rfl
        · simpa [ES, GateOp.eval] using
            Iq (z a) (z b) (x a) (x b) (hmono a) (hmono b)
        · simpa [ES, GateOp.eval] using
            It (z a) (z b) (x a) (x b)
      | cons c rest=>simp at hsize
lemma DR (d s:ℕ):d*s≤ s+(d - 1)*s:=by
  cases d with
  | zero=>simp
  | succ d=>simp [Nat.succ_mul, Nat.add_comm]
lemma Co {κ:Type*} [Fintype κ]
    (raw:κ→ℕ) (use:κ→κ→ℕ) (out critical:κ→ℕ)
    (local_flow:∀ g, critical g+out g≤raw g+∑ h, use g h*out h):
    ∑ g, critical g≤∑ g, raw g+∑ h, ((∑ g, use g h) - 1)*out h:=by
  have hs:=Finset.sum_le_sum (fun g (_:g∈Finset.univ)=>local_flow g)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  have hreorder:(∑ g, ∑ h, use g h*out h)=∑ h, (∑ g, use g h)*out h:=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_mul]
  rw [hreorder] at hs
  have hallow:=Finset.sum_le_sum (fun h (_:h∈Finset.univ)=>
    DR (∑ g, use g h) (out h))
  rw [Finset.sum_add_distrib] at hallow
  omega
def run:List Gate→List Bool→List Bool
  | [], x=>x
  | g::gs, x=>run gs (x++[g.op.eval (g.inputs.map fun w=>x.getD w false)])
lemma Ic (gs:List Gate) (x:List Bool):
    run gs x=({ gates:=gs, output:=0 }:Circuit).wires x:=by
  induction gs generalizing x with
  | nil=>rfl
  | cons g gs ih=>
    simpa only [run, Circuit.wires, List.foldl_cons] using
      (ih (x++[g.op.eval (g.inputs.map fun w=>x.getD w false)]))
lemma run_length (gs:List Gate) (x:List Bool):
    (run gs x).length=x.length+gs.length:=by
  induction gs generalizing x with
  | nil=>simp [run]
  | cons g gs ih=>simp [run, ih, Nat.add_comm, Nat.add_left_comm]
lemma run_append (gs hs:List Gate) (x:List Bool):
    run (gs++hs) x=run hs (run gs x):=by
  induction gs generalizing x with
  | nil=>rfl
  | cons g gs ih=>exact ih _
lemma Id (gs:List Gate) (x:List Bool):
    ∃ tail, run gs x=x++tail:=by
  induction gs generalizing x with
  | nil=>exact ⟨[], by simp [run]⟩
  | cons g gs ih=>
    obtain ⟨tail, ht⟩:=ih (x++[g.op.eval (g.inputs.map fun w=>x.getD w false)])
    exact ⟨[g.op.eval (g.inputs.map fun w=>x.getD w false)]++tail,
      by simpa only [run, List.append_assoc] using ht⟩
lemma Ih (gs:List Gate) (x:List Bool) (w:ℕ) (hw:w < x.length):
    (run gs x).getD w false=x.getD w false:=by
  obtain ⟨tail, ht⟩:=Id gs x
  rw [ht, List.getD_append _ _ _ _ hw]
lemma EX (g:Gate) (z x:ℕ→Bool)
    (hop:g.op=.and∨g.op=.or)
    (hmono:∀ w, z w=true→x w=true):
    g.op.eval (g.inputs.map z)=true→ g.op.eval (g.inputs.map x)=true:=by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp] at*
    exact fun h w hw=>hmono w (h w hw)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp] at*
    rintro ⟨w, hw, hz⟩
    exact ⟨w, hw, hmono w hz⟩
lemma Br (z x:List Bool) (a b:Bool)
    (hlen:z.length=x.length)
    (hmono:∀ w, z.getD w false=true→x.getD w false=true)
    (hab:a=true→b=true):
    ∀ w, (z++[a]).getD w false=true→(x++[b]).getD w false=true:=by
  intro w
  by_cases hw:w < z.length
  · rw [List.getD_append _ _ _ _ hw,
      List.getD_append _ _ _ _ (by omega)]
    exact hmono w
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), ← hlen]
    by_cases he:w=z.length
    · subst w
      simpa using hab
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      simp
lemma run_mono (gs:List Gate) (z x:List Bool)
    (hops:∀ g∈gs, g.op=.and∨g.op=.or)
    (hlen:z.length=x.length)
    (hmono:∀ w, z.getD w false=true→x.getD w false=true):
    ∀ w, (run gs z).getD w false=true→(run gs x).getD w false=true:=by
  induction gs generalizing z x with
  | nil=>exact hmono
  | cons g gs ih=>
    apply ih _ _ (fun g hg=>hops g (by simp [hg]))
    · simp [hlen]
    · apply Br _ _ _ _ hlen hmono
      exact EX g _ _ (hops g (by simp)) hmono
def Kk (C:Circuit) (x:List Bool) (j:ℕ):List Bool:=
  run (C.gates.take j) x
lemma Kp (C:Circuit) (x:List Bool):C.wires x=run C.gates x:=by
  simpa only [Circuit.wires] using (Ic C.gates x).symm
lemma Kl (C:Circuit) (x:List Bool) (j:ℕ) (hj:j≤C.gates.length):
    (Kk C x j).length=x.length+j:=by
  simp only [Kk, run_length, List.length_take, Nat.min_eq_left hj]
lemma Kn (C:Circuit) (x:List Bool) (j w:ℕ)
    (hj:j≤C.gates.length) (hw:w < x.length+j):
    (C.wires x).getD w false=(Kk C x j).getD w false:=by
  rw [Kp, ← List.take_append_drop j C.gates, run_append]
  apply Ih
  simpa only [run_length, List.length_take, Nat.min_eq_left hj] using hw
lemma Km (C:Circuit) (z x:List Bool) (j:ℕ)
    (hops:∀ g∈C.gates, g.op=.and∨g.op=.or)
    (hlen:z.length=x.length)
    (hmono:∀ w, z.getD w false=true→x.getD w false=true):
    ∀ w, (Kk C z j).getD w false=true→
      (Kk C x j).getD w false=true:=by
  apply run_mono _ _ _ _ hlen hmono
  intro g hg
  exact hops g (List.mem_of_mem_take hg)
lemma Fe (C:Circuit) (x:List Bool) (j:Fin C.gates.length):
    (C.wires x).getD (x.length+j.val) false=
      C.gates[j].op.eval (C.gates[j].inputs.map fun w=>(Kk C x j).getD w false):=by
  rw [Kn C x (j.val+1) (x.length+j.val) (by omega) (by omega)]
  unfold Kk
  rw [List.take_succ_eq_append_getElem j.isLt, run_append]
  simp only [run]
  have hlen:(run (C.gates.take j.val) x).length=x.length+j.val:=by
    simp only [run_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  rw [← hlen, List.getD_append_right _ _ _ _ le_rfl]
  simp
def EQ (C:Circuit) (z x:List Bool) (j:Fin C.gates.length):ℕ:=
  Ip ((C.wires z).getD (z.length+j.val) false)
    ((C.wires x).getD (x.length+j.val) false)
def BP (C:Circuit) (z x:List Bool) (j:Fin C.gates.length):ℕ:=
  ES C.gates[j] (fun w=>(Kk C z j).getD w false)
    (fun w=>(Kk C x j).getD w false)
lemma BW (C:Circuit) (z x:List Bool) (j:Fin C.gates.length)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (hlen:z.length=x.length)
    (hmono:∀ w, z.getD w false=true→x.getD w false=true):
    BP C z x j+EQ C z x j≤
      (C.gates[j].inputs.map fun w=>
        Ip ((Kk C z j).getD w false) ((Kk C x j).getD w false)).sum:=by
  have hj:=hC C.gates[j] (List.getElem_mem j.isLt)
  unfold BP EQ
  rw [Fe, Fe]
  exact EZ _ _ _ (by simpa using hj.1) hj.2 (Km C z x j
    (fun g hg=>by simpa using (hC g hg).1) hlen hmono)
def HB (z x:List Bool) (w:ℕ):ℕ:=
  if w < z.length then Ip (z.getD w false) (x.getD w false) else 0
def JQ (n:ℕ) (j h:ℕ) (w:ℕ):ℕ:=
  if w=n+h∧h < j then 1 else 0
lemma Kg (C:Circuit) (z x:List Bool) (j:Fin C.gates.length)
    (hlen:z.length=x.length) (w:ℕ):
    Ip ((Kk C z j).getD w false) ((Kk C x j).getD w false)=
      HB z x w+∑ h:Fin C.gates.length,
        JQ z.length j h w*EQ C z x h:=by
  by_cases hw:w < z.length
  · have hz:=Ih (C.gates.take j) z w hw
    have hx:=Ih (C.gates.take j) x w (by omega)
    have hzero:∀ h:Fin C.gates.length, JQ z.length j h w=0:=by
      intro h
      have hne:w≠z.length+h.val:=by omega
      simp [JQ, hne]
    simp only [Kk, hz, hx, HB, hw, ↓reduceIte, hzero, zero_mul,
      Finset.sum_const_zero, Nat.add_zero]
  · by_cases hp:w < z.length+j.val
    · let h:Fin C.gates.length:=⟨w - z.length, by omega⟩
      have he:w=z.length+h.val:=by dsimp [h]; omega
      have hh:h.val < j.val:=by dsimp [h]; omega
      have hs:(∑ k:Fin C.gates.length,
          JQ z.length j k w*EQ C z x k)=EQ C z x h:=by
        rw [Finset.sum_eq_single h]
        · simp [JQ, he, hh]
        · intro k hk hkh
          have hne:w≠z.length+k.val:=by
            intro hwk
            apply hkh
            apply Fin.ext
            omega
          simp [JQ, hne]
        · simp
      rw [hs]
      simp only [HB, hw, ↓reduceIte, Nat.zero_add]
      unfold EQ
      rw [Kn C z j (z.length+h.val) (by omega) (by omega),
        Kn C x j (x.length+h.val) (by omega) (by omega)]
      rw [← hlen, ← he]
    · have hzlen:=Kl C z j (Nat.le_of_lt j.isLt)
      have hxlen:=Kl C x j (Nat.le_of_lt j.isLt)
      have hz:(Kk C z j).getD w false=false:=
        List.getD_eq_default _ _ (by omega)
      have hx:(Kk C x j).getD w false=false:=
        List.getD_eq_default _ _ (by omega)
      have hzero:∀ h:Fin C.gates.length, JQ z.length j h w=0:=by
        intro h
        have hnot:¬(w=z.length+h.val∧h.val < j.val):=by omega
        simp only [JQ, ite_eq_right hnot]
      rw [hz, hx]
      simp only [HB, ite_eq_right hw, hzero, zero_mul, Finset.sum_const_zero]
      rfl
lemma IO {ι:Type*} [Fintype ι] (l:List ℕ)
    (A:ℕ→ℕ) (B:ℕ→ι→ℕ) (s:ι→ℕ):
    (l.map (fun w=>A w+∑ h, B w h*s h)).sum=
      (l.map A).sum+∑ h, (l.map (fun w=>B w h)).sum*s h:=by
  induction l with
  | nil=>simp
  | cons w l ih=>
    simp only [List.map_cons, List.sum_cons, ih]
    simp_rw [Nat.add_mul]
    rw [Finset.sum_add_distrib]
    omega
def Hz (C:Circuit) (z x:List Bool) (j:Fin C.gates.length):ℕ:=
  (C.gates[j].inputs.map (HB z x)).sum
def ET (C:Circuit) (n:ℕ) (j h:Fin C.gates.length):ℕ:=
  (C.gates[j].inputs.map (JQ n j h)).sum
lemma BX (C:Circuit) (z x:List Bool) (j:Fin C.gates.length)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (hlen:z.length=x.length)
    (hmono:∀ w, z.getD w false=true→x.getD w false=true):
    BP C z x j+EQ C z x j≤
      Hz C z x j+∑ h, ET C z.length j h*EQ C z x h:=by
  have hg:=BW C z x j hC hlen hmono
  simp_rw [Kg C z x j hlen] at hg
  rw [IO] at hg
  exact hg
lemma BZ (C:Circuit) (z x:List Bool)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (hlen:z.length=x.length)
    (hmono:∀ w, z.getD w false=true→x.getD w false=true):
    ∑ j, BP C z x j≤
      ∑ j, Hz C z x j+
        ∑ h, ((∑ j, ET C z.length j h) - 1)*EQ C z x h:=by
  exact Co (Hz C z x) (ET C z.length)
    (EQ C z x) (BP C z x)
    (fun j=>BX C z x j hC hlen hmono)
lemma Ca (C:Circuit) (z x:List Bool)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (hlen:z.length=x.length)
    (hmono:∀ w, z.getD w false=true→x.getD w false=true)
    (q:ℕ) (credits IP:Fin C.gates.length→ℕ)
    (hraw:∑ j, Hz C z x j≤q)
    (hcredits:∀ h, (∑ j, ET C z.length j h) - 1≤credits h)
    (hsupport:∀ h, EQ C z x h≤IP h):
    ∑ j, BP C z x j≤q+∑ h, credits h*IP h:=by
  calc
    _≤∑ j, Hz C z x j+
        ∑ h, ((∑ j, ET C z.length j h) - 1)*EQ C z x h:=
      BZ C z x hC hlen hmono
    _≤q+∑ h, credits h*IP h:=by
      apply Nat.add_le_add hraw
      exact Finset.sum_le_sum (fun h _=>Nat.mul_le_mul (hcredits h) (hsupport h))
lemma ER (C:Circuit) (z x:List Bool) (j:Fin C.gates.length):
    EQ C z x j≤ if (C.wires x).getD (x.length+j.val) false then 1 else 0:=
  Is _ _
lemma HC (n:ℕ) (i:Fin n) (w:ℕ):
    HB (List.replicate n false)
      (List.ofFn (fun j:Fin n=>decide (j=i))) w=if w=i.val then 1 else 0:=by
  by_cases hw:w < n
  · simp only [HB, List.length_replicate, ↓reduceIte,
      List.getD_eq_getElem?_getD, List.getElem?_replicate, List.getElem?_ofFn, hw,
      ↓reduceDIte, Option.getD_some, Ip]
    by_cases he:w=i.val
    · simp [he]
    · have hfin:(⟨w, hw⟩:Fin n)≠i:=fun h=>he (congrArg Fin.val h)
      simp [he, hfin]
  · have hne:w≠i.val:=by omega
    simp [HB, hw, hne]
end AD
namespace Aa
def Dg {k:ℕ} (c:Fin k→Option Bool):ℕ:=
  (Finset.univ.filter (fun j=>c j≠none)).card
def AX {n k:ℕ} (c:Fin n→Fin k→Option Bool):Prop:=
  ∀ i j, i≠j→∃ t,
    (c i t=some true∧c j t=some false)∨
    (c i t=some false∧c j t=some true)
def Bl (b:Option Bool):Finset Bool:=
  match b with
  | none=>Finset.univ
  | some b=>{b}
def box {k:ℕ} (c:Fin k→Option Bool):Finset (Fin k→Bool):=
  Fintype.piFinset (fun j=>Bl (c j))
lemma Bm (b:Option Bool):
    (Bl b).card=if b=none then 2 else 1:=by
  cases b <;> simp [Bl]
lemma EI {k:ℕ} (c:Fin k→Option Bool):
    (Finset.univ.filter (fun j=>c j=none)).card=k - Dg c:=by
  have h:=Finset.card_filter_add_card_filter_not
    (s:=(Finset.univ:Finset (Fin k))) (fun j=>c j=none)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h':(Finset.univ.filter (fun j=>c j=none)).card+Dg c=k:=by
    simpa [Dg] using h
  omega
lemma BI {k:ℕ} (c:Fin k→Option Bool):
    (box c).card=2^(k - Dg c):=by
  simp only [box, Fintype.card_piFinset, Bm]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, Nat.mul_one]
  rw [EI]
lemma BE {n k:ℕ} (c:Fin n→Fin k→Option Bool)
    (hc:AX c) {i j:Fin n} (hij:i≠j):
    Disjoint (box (c i)) (box (c j)):=by
  apply Finset.disjoint_left.mpr
  intro f hfi hfj
  obtain ⟨t, ht⟩:=hc i j hij
  have hi:=Fintype.mem_piFinset.mp hfi t
  have hj:=Fintype.mem_piFinset.mp hfj t
  rcases ht with ⟨hi', hj'⟩ | ⟨hi', hj'⟩ <;>
    simp [hi', hj', Bl] at hi hj <;> simp_all
lemma FH {n k:ℕ} (c:Fin n→Fin k→Option Bool)
    (hc:AX c):
    ∑ i, 2^(k - Dg (c i))≤2^k:=by
  have hdis:(↑(Finset.univ:Finset (Fin n)):Set (Fin n)).PairwiseDisjoint (fun i=>box (c i)):=by
    intro i hi j hj hij
    exact BE c hc hij
  have hcard:=Finset.card_le_card
    (Finset.subset_univ (Finset.univ.biUnion (fun i=>box (c i))))
  rw [Finset.card_biUnion hdis] at hcard
  simpa only [BI, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] using hcard
lemma Dh {k:ℕ} (c:Fin k→Option Bool):Dg c≤k:=by
  unfold Dg
  exact (Finset.card_filter_le _ _).trans_eq (by simp)
lemma Jo (k d:ℕ) (hd:d≤k):
    (2:ℚ)^k*(1 / 2:ℚ)^d=2^(k - d):=by
  rw [one_div_pow, mul_one_div]
  apply (div_eq_iff (by positivity)).mpr
  rw [← pow_add, Nat.sub_add_cancel hd]
lemma FI {n k:ℕ} (c:Fin n→Fin k→Option Bool)
    (hc:AX c):
    ∑ i, (1 / 2:ℚ)^Dg (c i)≤1:=by
  have h:(∑ i, (2:ℚ)^(k - Dg (c i)))≤(2:ℚ)^k:=by
    exact_mod_cast FH c hc
  have he:(2:ℚ)^k*(∑ i, (1 / 2:ℚ)^Dg (c i))=
      ∑ i, (2:ℚ)^(k - Dg (c i)):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Jo k _ (Dh _)
  rw [← he] at h
  have hp:(0:ℚ) < 2^k:=by positivity
  nlinarith
lemma FG {n k:ℕ} (c:Fin n→Fin k→Option Bool)
    (hc:AX c) (D:Fin n→ℕ) (hD:∀ i, Dg (c i)≤D i):
    ∑ i, (1 / 2:ℚ)^D i≤1:=by
  calc
    _≤∑ i, (1 / 2:ℚ)^Dg (c i):=by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hD i)
    _≤1:=FI c hc
end Aa
namespace AE
open PEqualNP.CircuitLowerBounds AD
def Fresh (a b p:Bool):Prop:=p=true∧a=false∧b=false
def Cross (ar br as_ bs:Bool):Prop:=
  (ar=true∧br=false∧as_=false∧bs=true)∨
  (ar=false∧br=true∧as_=true∧bs=false)
lemma Bo (ar br as_ bs pr ps:Bool)
    (hp:(pr && ps)=true) (ha:(ar && as_)=false) (hb:(br && bs)=false)
    (hr:pr=true→ar=true∨br=true)
    (hs:ps=true→as_=true∨bs=true):Cross ar br as_ bs:=by
  cases ar <;> cases br <;> cases as_ <;> cases bs <;> cases pr <;> cases ps <;>
    simp_all [Cross]
lemma EY (g:Gate) (a b p:ℕ→Bool)
    (hop:g.op=.and∨g.op=.or) (hsize:g.inputs.length≤2)
    (hdom:∀ w, p w=true→a w=true∨b w=true)
    (hfresh:Fresh (g.op.eval (g.inputs.map a)) (g.op.eval (g.inputs.map b))
      (g.op.eval (g.inputs.map p))):
    ∃ r s, g.op=.and∧g.inputs=[r,s]∧Cross (a r) (b r) (a s) (b s):=by
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil=>rcases hop with rfl | rfl <;> simp [Fresh, GateOp.eval] at hfresh
  | cons r rest=>
    cases rest with
    | nil=>
      rcases hop with rfl | rfl <;> simp [Fresh, GateOp.eval] at hfresh
      all_goals
        rcases hfresh with ⟨hp, ha, hb⟩
        rcases hdom r hp with h | h <;> simp_all
    | cons s rest=>
      cases rest with
      | nil=>
        rcases hop with rfl | rfl
        · refine ⟨r, s, rfl, rfl, ?_⟩
          simp only [Fresh, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, Bool.and_true] at hfresh
          exact Bo _ _ _ _ _ _ hfresh.1 hfresh.2.1 hfresh.2.2 (hdom r) (hdom s)
        · simp only [Fresh, GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
            Bool.or_eq_false_iff] at hfresh
          rcases hfresh with ⟨hr | hs, ⟨har, has⟩, hbr, hbs⟩
          · rcases hdom r hr with h | h <;> simp_all
          · rcases hdom s hs with h | h <;> simp_all
      | cons t rest=>simp at hsize
lemma GI (a b p:Bool) (h:¬Fresh a b p):
    p=true→a=true∨b=true:=by
  cases a <;> cases b <;> cases p <;> simp_all [Fresh]
lemma Bq (a b p:List Bool) (av bv pv:Bool)
    (hlenab:a.length=b.length) (hlenap:a.length=p.length)
    (hdom:∀ w, p.getD w false=true→a.getD w false=true∨b.getD w false=true)
    (hgate:pv=true→av=true∨bv=true):
    ∀ w, (p++[pv]).getD w false=true→
      (a++[av]).getD w false=true∨(b++[bv]).getD w false=true:=by
  intro w
  by_cases hw:w < a.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hw,
      List.getD_append _ _ _ _ (by omega)]
    exact hdom w
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), ← hlenab, ← hlenap]
    by_cases he:w=a.length
    · subst w
      simpa using hgate
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      simp
lemma Ie (gs:List Gate) (a b p:List Bool)
    (hops:∀ g∈gs, g.op=.and∨g.op=.or)
    (hsizes:∀ g∈gs, g.inputs.length≤2)
    (hlenab:a.length=b.length) (hlenap:a.length=p.length)
    (hdom:∀ w, p.getD w false=true→a.getD w false=true∨b.getD w false=true)
    (hfresh:∃ w, Fresh ((run gs a).getD w false) ((run gs b).getD w false)
      ((run gs p).getD w false)):
    ∃ pre g post r s, gs=pre++g::post∧g.op=.and∧g.inputs=[r,s]∧
      Cross ((run pre a).getD r false) ((run pre b).getD r false)
        ((run pre a).getD s false) ((run pre b).getD s false):=by
  induction gs generalizing a b p with
  | nil=>
    obtain ⟨w, hp, ha, hb⟩:=hfresh
    rcases hdom w hp with h | h <;> simp_all [run]
  | cons g gs ih=>
    let av:=g.op.eval (g.inputs.map fun w=>a.getD w false)
    let bv:=g.op.eval (g.inputs.map fun w=>b.getD w false)
    let pv:=g.op.eval (g.inputs.map fun w=>p.getD w false)
    by_cases hf:Fresh av bv pv
    · obtain ⟨r, s, hop, hins, hcross⟩:=EY g _ _ _
        (hops g (by simp)) (hsizes g (by simp)) hdom hf
      exact ⟨[], g, gs, r, s, rfl, hop, hins, hcross⟩
    · obtain ⟨pre, h, post, r, s, heq, hop, hins, hcross⟩:=
        ih (a++[av]) (b++[bv]) (p++[pv])
          (fun g hg=>hops g (by simp [hg]))
          (fun g hg=>hsizes g (by simp [hg]))
          (by simp [hlenab]) (by simp [hlenap])
          (Bq _ _ _ _ _ _ hlenab hlenap hdom (GI _ _ _ hf)) hfresh
      refine ⟨g::pre, h, post, r, s, ?_, hop, hins, hcross⟩
      simpa using congrArg (List.cons g) heq
def Bx (zr zs ar as_:Bool):Option Bool:=
  if zr=false∧zs=false then
    match ar, as_ with
    | true, false=>some true
    | false, true=>some false
    | _, _=>none
  else none
def gateCode (g:Gate) (z a:ℕ→Bool):Option Bool:=
  match g.op, g.inputs with
  | .and, [r,s]=>Bx (z r) (z s) (a r) (a s)
  | _, _=>none
def Hi (C:Circuit) (z a:List Bool) (j:Fin C.gates.length):Option Bool:=
  gateCode C.gates[j] (fun w=>(Kk C z j).getD w false)
    (fun w=>(Kk C a j).getD w false)
def AP (a b:Option Bool):Prop:=
  (a=some true∧b=some false)∨(a=some false∧b=some true)
lemma By (zr zs ar br as_ bs:Bool)
    (hr:zr=true→ar=true) (hr':zr=true→br=true)
    (hs:zs=true→as_=true) (hs':zs=true→bs=true)
    (hc:Cross ar br as_ bs):
    AP (Bx zr zs ar as_) (Bx zr zs br bs):=by
  cases zr <;> cases zs <;> cases ar <;> cases br <;> cases as_ <;> cases bs <;>
    simp_all [Cross, AP, Bx]
lemma Bz (zr zs ar as_:Bool):
    (if Bx zr zs ar as_≠none then 1 else 0)=Iw zr zs ar as_:=by
  cases zr <;> cases zs <;> cases ar <;> cases as_ <;> decide
lemma EP (g:Gate) (z a:ℕ→Bool):
    (if gateCode g z a≠none then 1 else 0)=ES g z a:=by
  rcases g with ⟨op, ins⟩
  cases op <;> try rfl
  cases ins with
  | nil=>rfl
  | cons r rest=>
    cases rest with
    | nil=>rfl
    | cons t rest=>
      cases rest with
      | nil=>exact Bz _ _ _ _
      | cons u rest=>rfl
lemma Hj (C:Circuit) (z a:List Bool) (j:Fin C.gates.length):
    (if Hi C z a j≠none then 1 else 0)=BP C z a j:=
  EP _ _ _
lemma BY (C:Circuit) (z a b p:List Bool)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (hlenza:z.length=a.length) (hlenzb:z.length=b.length)
    (hlenzp:z.length=p.length)
    (hza:∀ w, z.getD w false=true→a.getD w false=true)
    (hzb:∀ w, z.getD w false=true→b.getD w false=true)
    (hdom:∀ w, p.getD w false=true→a.getD w false=true∨b.getD w false=true)
    (ha:C.eval a=false) (hb:C.eval b=false) (hp:C.eval p=true):
    ∃ j:Fin C.gates.length, AP (Hi C z a j) (Hi C z b j):=by
  have hfresh:∃ w, Fresh ((run C.gates a).getD w false)
      ((run C.gates b).getD w false) ((run C.gates p).getD w false):=by
    refine ⟨C.output, ?_⟩
    simpa only [Fresh, Circuit.eval, Kp] using And.intro hp (And.intro ha hb)
  obtain ⟨pre, g, post, r, t, heq, hop, hins, hcross⟩:=
    Ie C.gates a b p (fun g hg=>by simpa using (hC g hg).1)
      (fun g hg=>(hC g hg).2) (by omega) (by omega) hdom hfresh
  have hpre:∀ g∈pre, g.op=.and∨g.op=.or:=by
    intro h hh
    apply (by simpa using (hC h (by rw [heq]; simp [hh])).1)
  have haz:=run_mono pre z a hpre hlenza hza
  have hbz:=run_mono pre z b hpre hlenzb hzb
  let j:Fin C.gates.length:=⟨pre.length, by simp [heq]⟩
  have hjg:C.gates[j]=g:=by simp [j, heq]
  have hjpre:C.gates.take j.val=pre:=by simp [j, heq]
  refine ⟨j, ?_⟩
  simp only [Hi, hjg, gateCode, hop, hins, Kk, hjpre]
  exact By _ _ _ _ _ _ (haz r) (hbz r) (haz t) (hbz t) hcross
lemma Cd (C:Circuit) (z a:List Bool):
    Aa.Dg (Hi C z a)=∑ j, BP C z a j:=by
  calc
    _=∑ j:Fin C.gates.length, if Hi C z a j≠none then 1 else 0:=by
      symm
      exact Finset.sum_boole _ _
    _=_:=Finset.sum_congr rfl (fun j _=>Hj C z a j)
lemma BV {n:ℕ} (C:Circuit) (z:List Bool)
    (a:Fin n→List Bool) (p:Fin n→Fin n→List Bool)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (hlena:∀ i, z.length=(a i).length)
    (hlenp:∀ i j, z.length=(p i j).length)
    (hza:∀ i w, z.getD w false=true→(a i).getD w false=true)
    (hdom:∀ i j, i≠j→∀ w, (p i j).getD w false=true→
      (a i).getD w false=true∨(a j).getD w false=true)
    (ha:∀ i, C.eval (a i)=false)
    (hp:∀ i j, i≠j→C.eval (p i j)=true):
    Aa.AX (fun i=>Hi C z (a i)):=by
  intro i j hij
  exact BY C z (a i) (a j) (p i j) hC (hlena i) (hlena j)
    (hlenp i j) (hza i) (hza j) (hdom i j hij) (ha i) (ha j) (hp i j hij)
lemma BU {n:ℕ} (C:Circuit) (z:List Bool)
    (a:Fin n→List Bool) (p:Fin n→Fin n→List Bool)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (hlena:∀ i, z.length=(a i).length)
    (hlenp:∀ i j, z.length=(p i j).length)
    (hza:∀ i w, z.getD w false=true→(a i).getD w false=true)
    (hdom:∀ i j, i≠j→∀ w, (p i j).getD w false=true→
      (a i).getD w false=true∨(a j).getD w false=true)
    (ha:∀ i, C.eval (a i)=false)
    (hp:∀ i j, i≠j→C.eval (p i j)=true)
    (q:Fin n→ℕ) (credits:Fin C.gates.length→ℕ)
    (IP:Fin n→Fin C.gates.length→ℕ)
    (hraw:∀ i, ∑ j, Hz C z (a i) j≤q i)
    (hcredits:∀ h, (∑ j, ET C z.length j h) - 1≤credits h)
    (hsupport:∀ i h, EQ C z (a i) h≤IP i h):
    ∑ i, (1 / 2:ℚ)^(q i+∑ h, credits h*IP i h)≤1:=by
  apply Aa.FG (fun i=>Hi C z (a i))
    (BV C z a p hC hlena hlenp hza hdom ha hp)
  intro i
  rw [Cd]
  exact Ca C z (a i) hC (hlena i) (hza i)
    (q i) credits (IP i) (hraw i) hcredits (hsupport i)
def Iz {n:ℕ} (i:Fin n):List Bool:=
  List.ofFn (fun j:Fin n=>decide (j=i))
def pairInput {n:ℕ} (i j:Fin n):List Bool:=
  List.ofFn (fun k:Fin n=>decide (k=i∨k=j))
lemma Hk {n:ℕ} (i j:Fin n) (w:ℕ):
    (pairInput i j).getD w false=true→
      (Iz i).getD w false=true∨(Iz j).getD w false=true:=by
  by_cases hw:w < n
  · simp only [pairInput, Iz, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some, decide_eq_true_eq]
    exact fun h=>h
  · rw [List.getD_eq_default _ _ (by simp [pairInput]; omega)]
    simp
lemma Kw {n:ℕ} (x:List Bool) (w:ℕ):
    (List.replicate n false).getD w false=true→x.getD w false=true:=by
  simp
def JW (C:Circuit) (i:ℕ):ℕ:=
  ∑ j:Fin C.gates.length, (C.gates[j].inputs.map fun w=>if w=i then 1 else 0).sum
lemma HA {n:ℕ} (C:Circuit) (i:Fin n):
    (∑ j, Hz C (List.replicate n false) (Iz i) j)=JW C i:=by
  unfold Hz JW Iz
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply List.map_congr_left
  intro w hw
  exact HC n i w
lemma Ja {n:ℕ} (C:Circuit)
    (hC:PEqualNP.MetaComplexity.Monotone2 C)
    (hsingle:∀ i:Fin n, C.eval (Iz i)=false)
    (hpair:∀ i j:Fin n, i≠j→C.eval (pairInput i j)=true)
    (q:Fin n→ℕ) (credits:Fin C.gates.length→ℕ)
    (IP:Fin n→Fin C.gates.length→ℕ)
    (hraw:∀ i:Fin n, JW C i≤q i)
    (hcredits:∀ h, (∑ j, ET C n j h) - 1≤credits h)
    (hsupport:∀ i h, EQ C (List.replicate n false) (Iz i) h≤
      IP i h):
    ∑ i, (1 / 2:ℚ)^(q i+∑ h, credits h*IP i h)≤1:=by
  apply BU C (List.replicate n false) Iz pairInput hC
      (fun i=>by simp [Iz]) (fun i j=>by simp [pairInput])
      (fun i w=>Kw _ _) (fun i j _ w=>Hk i j w)
      hsingle hpair q credits IP
  · intro i
    rw [HA]
    exact hraw i
  · simpa only [List.length_replicate] using hcredits
  · exact hsupport
end AE
namespace An
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_18264
open scoped BigOperators
lemma Ko (C:Circuit) (x:List Bool) (j w:ℕ)
    (hj:j≤C.gates.length):
    (AD.Kk C x j).getD w false=
      if w < x.length+j then (C.wires x).getD w false else false:=by
  by_cases hw:w < x.length+j
  · simp only [hw, ite_true]
    exact (AD.Kn C x j w hj hw).symm
  · simp only [hw, ite_false]
    apply List.getD_eq_default
    rw [AD.Kl C x j hj]
    omega
lemma Dv (g:Gate) (z a:ℕ→Bool):
    As.Du g.op (g.inputs.map fun w=>(z w, a w))=
      AD.ES g z a:=by
  rcases g with ⟨op, ins⟩
  cases op <;> try rfl
  cases ins with
  | nil=>rfl
  | cons r rest=>
    cases rest with
    | nil=>
      cases hzr:z r <;>
        simp [As.Du, AD.ES, hzr]
    | cons s rest=>
      cases rest with
      | nil=>
        cases hzr:z r <;> cases hzs:z s <;> cases har:a r <;> cases has:a s <;>
          simp [As.Du, AD.ES,
            AD.Iw, hzr, hzs, har, has]
      | cons t rest=>
        cases hzr:z r <;> cases hzs:z s <;>
          simp [As.Du, AD.ES, hzr, hzs]
lemma EO (C:Circuit) (lo hi:List Bool)
    (j:Fin C.gates.length):
    As.gateCode C lo hi j=AD.BP C lo hi j:=by
  unfold As.gateCode As.GW
  simp_rw [← Ko C lo j.val _ (Nat.le_of_lt j.isLt),
    ← Ko C hi j.val _ (Nat.le_of_lt j.isLt)]
  exact Dv C.gates[j] _ _
lemma Cf (C:Circuit) (lo hi:List Bool):
    Aa.Dg (AE.Hi C lo hi)=
      ∑ j:Fin C.gates.length, As.gateCode C lo hi j:=by
  rw [AE.Cd]
  exact Finset.sum_congr rfl (fun j _=>(EO C lo hi j).symm)
lemma Ey (C:Circuit) (F:Finset ℕ):
    Function.Bijective (As.Ex C F):=by
  constructor
  · intro i j hij
    apply Fin.ext
    exact congrArg (fun k:Fin (As.Ee C F).gates.length=>k.val) hij
  · intro j
    refine ⟨⟨j.val, ?_⟩, ?_⟩
    · simpa only [As.Ej] using j.isLt
    · apply Fin.ext
      rfl
lemma Ev (C:Circuit) (F:Finset ℕ) (lo hi:List Bool):
    (∑ j:Fin C.gates.length, As.Eu C F lo hi j)=
      ∑ j:Fin (As.Ee C F).gates.length,
        As.gateCode (As.Ee C F) lo hi j:=by
  unfold As.Eu
  exact Equiv.sum_comp (Equiv.ofBijective _ (Ey C F)) _
lemma Ce (C:Circuit) (F:Finset ℕ) (lo hi:List Bool):
    Aa.Dg (AE.Hi (As.Ee C F) lo hi)=
      ∑ j:Fin C.gates.length, As.Eu C F lo hi j:=by
  rw [Cf]
  exact (Ev C F lo hi).symm
end An
namespace An
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity As
open PEqualNP.Outside.L_meta_18264
open scoped BigOperators
lemma Kv (n w:ℕ):(Ku n).getD w false=false:=by
  by_cases hw:w < n <;>
    simp [Ku, List.getD_eq_getElem?_getD, hw]
lemma Jp (n m:ℕ) (C:Circuit) (hC:Monotone2 C)
    (F:Finset ℕ) (index:Fin m→Fin n) (j:Fin C.gates.length)
    (hjF:j.val∈F) (hbefore:∀ k < j.val, k∉F)
    (hzero:(C.wires (Ku n)).getD (n+j.val) false=false)
    (hone:∀ i, (C.wires (IA (index i))).getD (n+j.val) false=true)
    (hraw:∀ i, JI C n (index i).val≤2)
    (hsingle:∀ i, (Ee C F).eval (IA (index i))=false)
    (hpair:∀ i k, i≠k→
      (Ee C F).eval (AE.pairInput (index i) (index k))=true)
    (credits:Fin C.gates.length→ℕ)
    (IP:Fin m→Fin C.gates.length→ℕ)
    (hcredits:∀ k, JI C n (n+k.val) - 1≤credits k)
    (hsupport:∀ i k, Kf (Ee C F) (Ku n)
      (IA (index i)) (n+k.val)≤IP i k):
    ∑ i, (1 / 2:ℚ)^
      (1+∑ k:Fin C.gates.length,
        if k.val∈F then 0 else credits k*IP i k)≤1:=by
  let bound:=fun i:Fin m=>1+∑ k:Fin C.gates.length,
    if k.val∈F then 0 else credits k*IP i k
  refine Aa.FG
    (fun i=>AE.Hi (Ee C F) (Ku n)
      (IA (index i))) ?_ bound ?_
  · apply AE.BV (Ee C F) (Ku n)
      (fun i=>IA (index i))
      (fun i k=>AE.pairInput (index i) (index k)) (Ek C F hC)
    · intro i
      simp [Ku, IA]
    · intro i k
      simp [Ku, AE.pairInput]
    · intro i w hw
      rw [Kv] at hw
      contradiction
    · intro i k _ w
      exact AE.Hk (index i) (index k) w
    · exact hsingle
    · exact hpair
  · intro i
    rw [Ce]
    have hbound:=EG n C hC F (index i) j
      hjF hbefore hzero (hone i) (hraw i)
    apply hbound.trans
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro k _
    by_cases hk:k.val∈F
    · rw [Eh n C F k hk (Ku n)
        (IA (index i)) (by simp [Ku]) (by simp [IA])]
      simp [hk]
    · simp only [hk, ↓reduceIte]
      exact Nat.mul_le_mul (hcredits k) (hsupport i k)
end An
namespace As
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Eo (C:Circuit) (F:Finset ℕ) (x:List Bool)
    (hF:∀ j, j∈F→j < C.gates.length→
      (C.wires x).getD (x.length+j) false=true):
    ∀ w, ((Ee C F).wires x).getD w false=(C.wires x).getD w false:=by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    change (run (Ee C F).gates x).getD w false=(run C.gates x).getD w false
    by_cases hraw:w < x.length
    · rw [Ig (Ee C F).gates x w hraw, Ig C.gates x w hraw]
    · by_cases hbound:w < x.length+C.gates.length
      · let j:=w-x.length
        have hj:j < C.gates.length:=by dsimp [j]; omega
        have hwj:x.length+j=w:=by dsimp [j]; omega
        by_cases hjF:j∈F
        · have hf:=Ei x.length C F ⟨j,hj⟩ hjF x rfl
          have hc:=hF j hjF hj
          simp only [hwj] at hf hc
          exact hf.trans hc.symm
        · have hd:=If (Ee C F).gates x j
            (by rw [Ej]; exact hj)
          have hc:=If C.gates x j hj
          rw [hwj] at hd hc
          rw [hd, hc, Eg C F j hj, ite_eq_right hjF]
          congr 1
          apply List.map_congr_left
          intro a _
          by_cases ha:a < w
          · simp only [ite_eq_left ha]
            exact ih a ha
          · simp only [ite_eq_right ha]
      · rw [List.getD_eq_default _ _ (by rw [run_length, Ej]; omega),
          List.getD_eq_default _ _ (by rw [run_length]; omega)]
lemma Ef (C:Circuit) (F:Finset ℕ) (x:List Bool)
    (hF:∀ j, j∈F→j < C.gates.length→
      (C.wires x).getD (x.length+j) false=true):
    (Ee C F).eval x=C.eval x:=by
  exact Eo C F x hF C.output
lemma ED (C:Circuit) (F:Finset ℕ)
    (lo hi:List Bool)
    (hF:∀ j, j∈F→j < C.gates.length→
      (C.wires hi).getD (hi.length+j) false=true) (w:ℕ):
    Kf (Ee C F) lo hi w≤
      if (C.wires hi).getD w false then 1 else 0:=by
  unfold Kf
  rw [Eo C F hi hF w]
  cases hs:(C.wires hi).getD w false <;>
    cases hz:((Ee C F).wires lo).getD w false <;> simp [Iv]
end As
namespace An
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity As
open PEqualNP.Outside.L_meta_18264
open scoped BigOperators
lemma IF {n:ℕ} (i k:Fin n) (w:ℕ):
    (IA i).getD w false=true→
      (AE.pairInput i k).getD w false=true:=by
  by_cases hw:w < n
  · simp only [IA, AE.pairInput, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some, decide_eq_true_eq]
    exact fun hi=>Or.inl hi
  · simp [IA, AE.pairInput, List.getD_eq_getElem?_getD,
      hw]
lemma IG {n:ℕ} (C:Circuit) (hC:Monotone2 C)
    (i k:Fin n) (w:ℕ):
    (C.wires (IA i)).getD w false=true→
      (C.wires (AE.pairInput i k)).getD w false=true:=by
  have h:=AD.run_mono C.gates (IA i)
    (AE.pairInput i k) (fun g hg=>(hC g hg).1)
    (by simp [IA, AE.pairInput]) (IF i k) w
  simpa only [AD.Kp] using h
lemma Jq (n m:ℕ) (C:Circuit) (hC:Monotone2 C)
    (F:Finset ℕ) (index:Fin m→Fin n) (j:Fin C.gates.length)
    (hjF:j.val∈F) (hbefore:∀ k < j.val, k∉F)
    (hzero:(C.wires (Ku n)).getD (n+j.val) false=false)
    (hraw:∀ i, JI C n (index i).val≤2)
    (hsingle:∀ i, C.eval (IA (index i))=false)
    (hpair:∀ i k, i≠k→
      C.eval (AE.pairInput (index i) (index k))=true)
    (hF:∀ i k, k∈F→k < C.gates.length→
      (C.wires (IA (index i))).getD (n+k) false=true)
    (credits:Fin C.gates.length→ℕ)
    (hcredits:∀ k, JI C n (n+k.val) - 1≤credits k):
    ∑ i, (1 / 2:ℚ)^
      (1+∑ k:Fin C.gates.length,
        if k.val∈F then 0 else credits k*
          (if (C.wires (IA (index i))).getD (n+k.val) false then 1 else 0))≤1:=by
  have hFsingle (i:Fin m):∀ k, k∈F→k < C.gates.length→
      (C.wires (IA (index i))).getD ((IA (index i)).length+k) false=true:=by
    simpa only [IA, List.length_ofFn] using hF i
  refine Jp n m C hC F index j hjF hbefore hzero
    (fun i=>hF i j.val hjF j.isLt) hraw ?_ ?_ credits
    (fun i k=>if (C.wires (IA (index i))).getD (n+k.val) false then 1 else 0)
    hcredits ?_
  · intro i
    rw [Ef C F (IA (index i)) (hFsingle i)]
    exact hsingle i
  · intro i k hik
    have hFp:∀ t, t∈F→t < C.gates.length→
        (C.wires (AE.pairInput (index i) (index k))).getD
          ((AE.pairInput (index i) (index k)).length+t) false=true:=by
      intro t htF ht
      simpa only [AE.pairInput, List.length_ofFn] using
        IG C hC (index i) (index k) (n+t) (hF i t htF ht)
    rw [Ef C F _ hFp]
    exact hpair i k hik
  · intro i k
    exact ED C F (Ku n)
      (IA (index i)) (hFsingle i) (n+k.val)
lemma Jr (n m:ℕ) (C:Circuit) (hC:Monotone2 C)
    (F:Finset ℕ) (index:Fin m→Fin n) (hinj:Function.Injective index)
    (j:Fin C.gates.length) (hjF:j.val∈F) (hbefore:∀ k < j.val, k∉F)
    (hzero:(C.wires (Ku n)).getD (n+j.val) false=false)
    (hraw:∀ i, JI C n (index i).val≤2)
    (hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn fun t=>decide (t∈S))=decide (2≤S.card))
    (hF:∀ i k, k∈F→k < C.gates.length→
      (C.wires (IA (index i))).getD (n+k) false=true)
    (credits:Fin C.gates.length→ℕ)
    (hcredits:∀ k, JI C n (n+k.val) - 1≤credits k):
    ∑ i, (1 / 2:ℚ)^
      (1+∑ k:Fin C.gates.length,
        if k.val∈F then 0 else credits k*
          (if (C.wires (IA (index i))).getD (n+k.val) false then 1 else 0))≤1:=by
  refine Jq n m C hC F index j hjF hbefore hzero
    hraw ?_ ?_ hF credits hcredits
  · intro i
    change C.eval (List.ofFn fun t:Fin n=>decide (t=index i))=false
    simpa using hcorrect {index i}
  · intro i k hik
    have hne:index i≠index k:=fun he=>hik (hinj he)
    change C.eval (List.ofFn fun t:Fin n=>decide (t=index i∨t=index k))=true
    simpa [hne] using hcorrect {index i, index k}
end An
namespace Ad
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma Ds (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hpos:∀ x:Fin n→Bool, (List.ofFn x).count true=2→
      C.eval (List.ofFn x)=true)
    (hneg:∀ x:Fin n→Bool, (List.ofFn x).count true≤1→
      C.eval (List.ofFn x)=false):
    ∀ S:Finset (Fin n), C.eval (List.ofFn fun i=>decide (i∈S))=
      decide (2≤S.card):=by
  classical
  intro S
  by_cases hs:2≤S.card
  · obtain ⟨T, hTS, hT⟩:=Finset.exists_subset_card_eq hs
    have hp:=hpos (fun i=>decide (i∈T)) (by simpa [List.count_ofFn] using hT)
    have hmono (w:ℕ):
        (List.ofFn fun i:Fin n=>decide (i∈T)).getD w false=true→
        (List.ofFn fun i:Fin n=>decide (i∈S)).getD w false=true:=by
      by_cases hw:w < n
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw,
          ↓reduceDIte, Option.getD_some, decide_eq_true_eq]
        exact fun h=>hTS h
      · simp [List.getD_eq_getElem?_getD, hw]
    have h:=AD.run_mono C.gates
      (List.ofFn fun i:Fin n=>decide (i∈T))
      (List.ofFn fun i:Fin n=>decide (i∈S))
      (fun g hg=>(hC g hg).1) (by simp) hmono C.output
    simp only [Circuit.eval, AD.Kp] at hp ⊢
    simpa [hs] using h hp
  · have hn:S.card≤1:=by omega
    have h:=hneg (fun i=>decide (i∈S)) (by simpa [List.count_ofFn] using hn)
    simpa [hs] using h
lemma Dd {n s:ℕ} (hn:2≤n)
    (hr:PEqualNP.Represents.RepSizeAtMost (fun u v:Fin n=>decide (u≠v)) s):
    ∃ C:Circuit, Monotone2 C∧C.size+n≤ s∧
      ∀ S:Finset (Fin n), C.eval (List.ofFn fun i=>decide (i∈S))=
        decide (2≤S.card):=by
  obtain ⟨C,hC,hsize,hpos,hneg⟩:=Ae n s hn hr
  exact ⟨C,hC,hsize,Ds n C hC hpos hneg⟩
lemma Dt (n:ℕ) (C:Circuit)
    (h:∀ S:Finset (Fin n), C.eval (List.ofFn fun i=>decide (i∈S))=
      decide (2≤S.card)):
    ∀ x:Fin n→Bool, C.eval (List.ofFn x)=
      decide (2≤(List.ofFn x).count true):=by
  intro x
  let S:Finset (Fin n):=Finset.univ.filter fun i=>x i=true
  simpa [S, List.count_ofFn] using h S
lemma De {n s:ℕ} (hn:2≤n)
    (hr:PEqualNP.Represents.RepSizeAtMost (fun u v:Fin n=>decide (u≠v)) s):
    ∃ C:Circuit, Monotone2 C∧C.size+n≤ s∧
      ∀ x:Fin n→Bool, C.eval (List.ofFn x)=
        decide (2≤(List.ofFn x).count true):=by
  obtain ⟨C,hC,hsize,hcorrect⟩:=Dd hn hr
  exact ⟨C,hC,hsize,Dt n C hcorrect⟩
end Ad
namespace Al
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Jd (n:ℕ) (hn:2≤n) (C:Circuit)
    (ht:IW n C):n≤C.output∧C.output < n+C.size:=by
  constructor
  · by_contra h
    have hout:C.output < n:=by omega
    exact Aw.Je n C ht ⟨C.output, hout⟩ rfl
  · by_contra h
    have hout:n+C.size≤C.output:=by omega
    apply Jb n hn C ht
    refine ⟨false, fun x=>?_⟩
    change (run C.gates (List.ofFn x)).getD C.output false=false
    apply List.getD_eq_default
    rw [run_length, List.length_ofFn]
    exact hout
end Al
namespace Ay
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma Bp (w:List Bool) (a b:Bool):
    ∀ k, k≠w.length→(w++[a]).getD k false=(w++[b]).getD k false:=by
  intro k hk
  by_cases hlt:k < w.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
  · have hgt:w.length+1≤k:=by omega
    rw [List.getD_eq_default _ _ (by simpa using hgt),
      List.getD_eq_default _ _ (by simpa using hgt)]
lemma JG (pre post:List Gate) (g h:Gate) (out n:ℕ)
    (hpost:∀ d∈post, n+pre.length∉d.inputs)
    (hout:out≠n+pre.length) (x:List Bool) (hx:x.length=n):
    (⟨pre++g::post,out⟩:Circuit).eval x=
      (⟨pre++h::post,out⟩:Circuit).eval x:=by
  let w:=Ak.run pre x
  have hw:w.length=n+pre.length:=by
    simp [w, Ak.run_length, hx]
  change (Ak.run (pre++g::post) x).getD out false=
    (Ak.run (pre++h::post) x).getD out false
  rw [Ak.run_append, Ak.run_append,
    Ak.run_cons, Ak.run_cons]
  apply Ak.HY post (n+pre.length)
    _ _ (by simp [Ak.step]) _ hpost out hout
  simpa only [← hw, Ak.step] using Bp w
    (g.op.eval (g.inputs.map fun k=>w.getD k false))
    (h.op.eval (h.inputs.map fun k=>w.getD k false))
lemma Ga (n:ℕ) (C:Circuit) (hmin:IsMinimalMonoCircuit n C)
    (hne:¬∃ b, ∀ x:Fin n→Bool, C.eval (List.ofFn x)=b)
    (j:Fin C.gates.length):
    C.output=n+j.val∨∃ k:Fin C.gates.length, n+j.val∈C.gates[k.val].inputs:=by
  classical
  by_contra hc
  have hout:C.output≠n+j.val:=fun h=>hc (Or.inl h)
  have hread:∀ k:Fin C.gates.length, n+j.val∉C.gates[k.val].inputs:=
    fun k hk=>hc (Or.inr ⟨k,hk⟩)
  let pre:=C.gates.take j.val
  let post:=C.gates.drop (j.val+1)
  let g:=C.gates[j.val]
  have hpre:pre.length=j.val:=by simp [pre]
  have hsplit:pre++g::post=C.gates:=by
    change C.gates.take j.val++C.gates[j.val]::C.gates.drop (j.val+1)=_
    rw [← List.drop_eq_getElem_cons j.isLt, List.take_append_drop]
  let D:Circuit:=⟨pre++⟨GateOp.or,[]⟩::post,C.output⟩
  have hD:Monotone2 D:=by
    intro d hd
    change d∈pre++⟨GateOp.or,[]⟩::post at hd
    rcases List.mem_append.mp hd with hp | hr
    · exact hmin.1 d (hsplit ▸ List.mem_append_left _ hp)
    · rcases List.mem_cons.mp hr with rfl | hp
      · simp
      · exact hmin.1 d (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  have heval (x:Fin n→Bool):C.eval (List.ofFn x)=D.eval (List.ofFn x):=by
    have hpost:∀ d∈post, n+pre.length∉d.inputs:=by
      intro d hd
      have hdC:d∈C.gates:=hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hd)
      obtain ⟨k,hk,he⟩:=List.mem_iff_getElem.mp hdC
      rw [hpre, ← he]
      exact hread ⟨k,hk⟩
    have hh:=JG pre post g ⟨GateOp.or,[]⟩ C.output n
      hpost (by simpa [hpre] using hout) (List.ofFn x) (by simp)
    simpa [hsplit, D] using hh
  have hsize:D.size=C.size:=by
    change (pre++⟨GateOp.or,[]⟩::post).length=C.gates.length
    rw [← hsplit]
    simp
  have hminD:IsMinimalMonoCircuit n D:=by
    refine ⟨hD,fun E hE he=>?_⟩
    rw [hsize]
    apply hmin.2 E hE
    exact he.trans (funext fun x=>(heval x).symm)
  have hneD:¬∃ b, ∀ x:Fin n→Bool, D.eval (List.ofFn x)=b:=by
    rintro ⟨b,hb⟩
    exact hne ⟨b,fun x=>(heval x).trans (hb x)⟩
  have hjD:j.val < D.gates.length:=by change _ < D.size; rw [hsize]; exact j.isLt
  apply Ao.Gc n D hminD hneD j.val hjD
  left
  refine ⟨false,fun x=>?_⟩
  have he:=Aj.If D.gates (List.ofFn x) j.val hjD
  simp only [List.length_ofFn] at he
  rw [he]
  have hgD:D.gates[j.val]=⟨GateOp.or,[]⟩:=by
    change (pre++⟨GateOp.or,[]⟩::post)[j.val]=_
    simpa only [hpre] using (show
      (pre++(⟨GateOp.or,[]⟩:Gate)::post)[pre.length]=
        (⟨GateOp.or,[]⟩:Gate) by simp)
  simp [hgD, GateOp.eval]
end Ay
namespace Ay
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators
lemma Gb (n:ℕ) (C:Circuit) (hmin:IsMinimalMonoCircuit n C)
    (hne:¬∃ b, ∀ x:Fin n→Bool, C.eval (List.ofFn x)=b)
    (j:Fin C.gates.length):
    C.output=n+j.val∨∃ k:Fin C.gates.length,
      j.val < k.val∧n+j.val∈C.gates[k.val].inputs:=by
  rcases Ga n C hmin hne j with hout | ⟨k, hread⟩
  · exact Or.inl hout
  · right
    obtain ⟨a,b,hports,hdist,ha,hb⟩:=
      Ao.FZ n C hmin hne k.val k.isLt
    have hcases:n+j.val=a∨n+j.val=b:=by simpa [hports] using hread
    exact ⟨k, by rcases hcases with h | h <;> omega, hread⟩
end Ay
namespace Ax
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma In (n:ℕ) (gs:List Gate)
    (hops:∀ g∈gs, g.op=GateOp.and∨g.op=GateOp.or)
    (hports:∀ g∈gs, ∃ a b, g.inputs=[a,b]):
    run gs (List.replicate n false)=List.replicate (n+gs.length) false:=by
  induction gs using List.reverseRecOn with
  | nil=>simp [run]
  | append_singleton gs g ih=>
    have hp:∀ d∈gs, d.op=GateOp.and∨d.op=GateOp.or:=by
      intro d hd
      exact hops d (by simp [hd])
    have hi:∀ d∈gs, ∃ a b, d.inputs=[a,b]:=by
      intro d hd
      exact hports d (by simp [hd])
    have hg:=hops g (by simp)
    obtain ⟨a,b,hab⟩:=hports g (by simp)
    have hv:g.op.eval (g.inputs.map fun w=>
        (List.replicate (n+gs.length) false).getD w false)=false:=by
      rcases hg with hg | hg <;> simp [hg, hab, GateOp.eval]
    rw [Il, ih hp hi, hv]
    simp only [List.length_append, List.length_singleton, List.replicate_add,
      List.replicate_one, Nat.add_assoc, List.append_assoc]
lemma Kt (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hports:∀ g∈C.gates, ∃ a b, g.inputs=[a,b]):
    C.wires (List.replicate n false)=List.replicate (n+C.gates.length) false:=by
  apply In n C.gates
  · intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
  · exact hports
lemma GH (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)
    (w:ℕ):(C.wires (List.ofFn fun _:Fin n=>false)).getD w false=false:=by
  have hp:∀ g∈C.gates, ∃ a b, g.inputs=[a,b]:=by
    intro g hg
    obtain ⟨t,ht,rfl⟩:=List.mem_iff_getElem.mp hg
    obtain ⟨a,b,hab,_⟩:=hshape t ht
    exact ⟨a,b,hab⟩
  rw [List.ofFn_const, Kt n C hC hp]
  simp
lemma GG (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)
    (j:Fin C.gates.length):
    (C.wires (List.ofFn fun _:Fin n=>false)).getD (n+j.val) false=false:=by
  exact GH n C hC hshape (n+j.val)
end Ax
namespace Aq
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open scoped BigOperators
end Aq
namespace Af
open PEqualNP.CircuitLowerBounds
open AD
open AE
lemma Ki (n G:ℕ) (j:Fin G) (w:ℕ) (hw:w < n+j.val):
    (∑ i:Fin n, if w=i.val then 1 else 0)+
      (∑ h:Fin G, JQ n j h w)=1:=by
  by_cases hn:w < n
  · let i:Fin n:=⟨w, hn⟩
    have hr:(∑ k:Fin n, if w=k.val then 1 else 0)=1:=by
      rw [Finset.sum_eq_single i]
      · simp [i]
      · intro k hk hki
        have hne:w≠k.val:=by
          intro he
          apply hki
          apply Fin.ext
          simpa [i] using he.symm
        simp [hne]
      · simp
    have hg:∀ h:Fin G, JQ n j h w=0:=by
      intro h
      have hne:w≠n+h.val:=by omega
      simp [JQ, hne]
    simp [hr, hg]
  · let h:Fin G:=⟨w - n, by omega⟩
    have he:w=n+h.val:=by dsimp [h]; omega
    have hj:h.val < j.val:=by dsimp [h]; omega
    have hr:∀ i:Fin n, (if w=i.val then 1 else 0:ℕ)=0:=by
      intro i
      have hne:w≠i.val:=by omega
      simp [hne]
    have hg:(∑ k:Fin G, JQ n j k w)=1:=by
      rw [Finset.sum_eq_single h]
      · simp [JQ, he, hj]
      · intro k hk hkh
        have hne:w≠n+k.val:=by
          intro he'
          apply hkh
          apply Fin.ext
          omega
        simp [JQ, hne]
      · simp
    simp [hr, hg]
lemma FK {α:Type} (n:ℕ) (l:List α) (f:α→Fin n→ℕ):
    (l.map fun a=>∑ i, f a i).sum=∑ i, (l.map fun a=>f a i).sum:=by
  induction l with
  | nil=>simp
  | cons a l ih=>simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]
lemma Fb (C:Circuit) (n:ℕ) (j:Fin C.gates.length)
    (hvalid:∀ w∈C.gates[j].inputs, w < n+j.val):
    (∑ i:Fin n, (C.gates[j].inputs.map fun w=>if w=i.val then 1 else 0).sum)+
      (∑ h:Fin C.gates.length, ET C n j h)=C.gates[j].inputs.length:=by
  unfold ET
  rw [← FK, ← FK]
  have hs:∀ l:List ℕ, (∀ w∈l, w < n+j.val)→
      (l.map fun w=>∑ i:Fin n, if w=i.val then 1 else 0).sum+
        (l.map fun w=>∑ h:Fin C.gates.length, JQ n j h w).sum=l.length:=by
    intro l hl
    induction l with
    | nil=>simp
    | cons w l ih=>
      have hw:=Ki n C.gates.length j w (hl w (by simp))
      have ht:=ih (fun v hv=>hl v (by simp [hv]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  exact hs _ hvalid
lemma Jk (C:Circuit) (n:ℕ)
    (hfanin:∀ j:Fin C.gates.length, C.gates[j].inputs.length=2)
    (hvalid:∀ j:Fin C.gates.length, ∀ w∈C.gates[j].inputs, w < n+j.val)
    (hraw:∀ i:Fin n, JW C i=2):
    2*n+(∑ h:Fin C.gates.length, ∑ j, ET C n j h)=2*C.size:=by
  have hp:=fun j=>Fb C n j (hvalid j)
  have he:=congrArg (fun f:Fin C.gates.length→ℕ=>∑ j, f j) (funext hp)
  simp only [Finset.sum_add_distrib, hfanin] at he
  rw [Finset.sum_comm, Finset.sum_comm (f:=fun j h=>ET C n j h)] at he
  change (∑ i:Fin n, JW C i)+
    (∑ h:Fin C.gates.length, ∑ j, ET C n j h)=_ at he
  simpa [hraw, Circuit.size, Nat.mul_comm] using he
def Hc (C:Circuit) (n:ℕ) (h:Fin C.gates.length):ℕ:=
  (∑ j, ET C n j h)+if C.output=n+h.val then 1 else 0
def credit (C:Circuit) (n:ℕ) (h:Fin C.gates.length):ℕ:=
  Hc C n h - 1
lemma Ea (C:Circuit) (n:ℕ) (h:Fin C.gates.length):
    (∑ j, ET C n j h) - 1≤credit C n h:=by
  unfold credit Hc
  omega
lemma Hd (C:Circuit) (n:ℕ)
    (hout:∃ h:Fin C.gates.length, C.output=n+h.val):
    (∑ h:Fin C.gates.length, if C.output=n+h.val then 1 else 0)=1:=by
  obtain ⟨h, hh⟩:=hout
  rw [Finset.sum_eq_single h]
  · simp [hh]
  · intro k hk hkh
    have hne:C.output≠n+k.val:=by
      intro he
      apply hkh
      apply Fin.ext
      omega
    simp [hne]
  · simp
lemma Ji (C:Circuit) (n:ℕ)
    (hfanin:∀ j:Fin C.gates.length, C.gates[j].inputs.length=2)
    (hvalid:∀ j:Fin C.gates.length, ∀ w∈C.gates[j].inputs, w < n+j.val)
    (hraw:∀ i:Fin n, JW C i=2)
    (hout:∃ h:Fin C.gates.length, C.output=n+h.val)
    (hlive:∀ h:Fin C.gates.length,
      0 < (∑ j, ET C n j h)∨C.output=n+h.val):
    (∑ h, credit C n h)+2*n=C.size+1:=by
  have he:=Jk C n hfanin hvalid hraw
  have ht:=Hd C n hout
  have hd:∀ h:Fin C.gates.length, 1≤Hc C n h:=by
    intro h
    rcases hlive h with hu | ho
    · unfold Hc
      omega
    · simp only [Hc, ho, ↓reduceIte]
      omega
  have hc:∀ h:Fin C.gates.length, credit C n h+1=Hc C n h:=by
    intro h
    unfold credit
    exact Nat.sub_add_cancel (hd h)
  have hs:=congrArg (fun f:Fin C.gates.length→ℕ=>∑ h, f h) (funext hc)
  simp only [Finset.sum_add_distrib, Hc] at hs
  rw [ht] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_one] at hs
  unfold Circuit.size at*
  omega
lemma EU (C:Circuit) (n:ℕ) (j h:Fin C.gates.length)
    (hlt:h.val < j.val) (hmem:n+h.val∈C.gates[j].inputs):
    0 < ET C n j h:=by
  have hp:∀ l:List ℕ, n+h.val∈l→(0 < (l.map (JQ n j h)).sum):=by
    intro l
    induction l with
    | nil=>simp
    | cons w l ih=>
      intro hm
      rcases List.mem_cons.mp hm with he | hm
      · subst w
        simp [JQ, hlt]
      · have ht:=ih hm
        simp only [List.map_cons, List.sum_cons]
        omega
  exact hp _ hmem
lemma Jj (C:Circuit) (n:ℕ)
    (hfanin:∀ j:Fin C.gates.length, C.gates[j].inputs.length=2)
    (hvalid:∀ j:Fin C.gates.length, ∀ w∈C.gates[j].inputs, w < n+j.val)
    (hraw:∀ i:Fin n, JW C i=2)
    (hout:∃ h:Fin C.gates.length, C.output=n+h.val)
    (hlive:∀ h:Fin C.gates.length,
      (∃ j:Fin C.gates.length, n+h.val∈C.gates[j].inputs)∨
        C.output=n+h.val):
    (∑ h, credit C n h)+2*n=C.size+1:=by
  apply Ji C n hfanin hvalid hraw hout
  intro h
  rcases hlive h with ⟨j, hj⟩ | ho
  · left
    have hp:h.val < j.val:=by have hw:=hvalid j _ hj; omega
    have hu:=EU C n j h hp hj
    have hs:ET C n j h≤∑ k, ET C n k h:=
      Finset.single_le_sum (f:=fun k=>ET C n k h)
        (fun k _=>Nat.zero_le _) (Finset.mem_univ j)
    omega
  · exact Or.inr ho
end Af
namespace AG
def Cm {m r:ℕ} (owner:Fin r→Option (Fin m)) (h:Fin m):Finset (Fin r):=
  Finset.univ.filter fun s=>owner s=some h
def JB {m r:ℕ} (owner:Fin r→Option (Fin m)) (R:Finset (Fin m)):
    Finset (Fin r):=R.biUnion (Cm owner)
def Jl {m r:ℕ} (owner:Fin r→Option (Fin m)) (F:Finset (Fin r)):
    Finset (Fin m):=Finset.univ.filter fun h=>∃ s∈F, owner s=some h
lemma FR {m r:ℕ} (owner:Fin r→Option (Fin m)) (h:Fin m) (s:Fin r):
    s∈Cm owner h↔owner s=some h:=by
  simp [Cm]
lemma FX {m r:ℕ} (owner:Fin r→Option (Fin m))
    (R:Finset (Fin m)) (s:Fin r):
    s∈JB owner R↔∃ h∈R, owner s=some h:=by
  simp [JB, Cm]
lemma FW {m r:ℕ} (owner:Fin r→Option (Fin m))
    (F:Finset (Fin r)) (h:Fin m):
    h∈Jl owner F↔∃ s∈F, owner s=some h:=by
  simp [Jl]
lemma Cn {m r:ℕ} (owner:Fin r→Option (Fin m))
    {a b:Fin m} (hab:a≠b):Disjoint (Cm owner a) (Cm owner b):=by
  apply Finset.disjoint_left.mpr
  intro s ha hb
  have ha':=(FR owner a s).mp ha
  have hb':=(FR owner b s).mp hb
  exact hab (Option.some.inj (ha'.symm.trans hb'))
lemma JC {m r:ℕ} (owner:Fin r→Option (Fin m))
    (c:Fin m→ℕ) (hcount:∀ h, (Cm owner h).card=c h) (R:Finset (Fin m)):
    (JB owner R).card=∑ h∈R, c h:=by
  unfold JB
  rw [Finset.card_biUnion]
  · simp_rw [hcount]
  · intro a ha b hb hab
    exact Cn owner hab
lemma Jn {m r:ℕ} (owner:Fin r→Option (Fin m))
    (R:Finset (Fin m)) (F:Finset (Fin r)) (hF:F⊆JB owner R):
    Jl owner F⊆R:=by
  intro h hh
  obtain ⟨s, hsF, hso⟩:=(FW owner F h).mp hh
  obtain ⟨a, ha, hsa⟩:=(FX owner R s).mp (hF hsF)
  have he:a=h:=Option.some.inj (hsa.symm.trans hso)
  simpa [he] using ha
lemma JF {m r:ℕ} (owner:Fin r→Option (Fin m))
    (R:Finset (Fin m)) (F:Finset (Fin r)):
    JB owner (R \ Jl owner F)⊆JB owner R \ F:=by
  intro s hs
  obtain ⟨h, hh, hso⟩:=(FX owner _ s).mp hs
  obtain ⟨hR, hnot⟩:=Finset.mem_sdiff.mp hh
  apply Finset.mem_sdiff.mpr
  refine ⟨(FX owner R s).mpr ⟨h, hR, hso⟩, ?_⟩
  intro hsF
  exact hnot ((FW owner F h).mpr ⟨s, hsF, hso⟩)
lemma HL {m r:ℕ} (owner:Fin r→Option (Fin m))
    (c:Fin m→ℕ) (hcount:∀ h, (Cm owner h).card=c h)
    (R:Finset (Fin m)) (F:Finset (Fin r)):
    (∑ h∈R \ Jl owner F, c h)≤(JB owner R \ F).card:=by
  rw [← JC owner c hcount]
  exact Finset.card_le_card (JF owner R F)
lemma Jm {m r:ℕ} (owner:Fin r→Option (Fin m))
    (c:Fin m→ℕ) (hcount:∀ h, (Cm owner h).card=c h)
    (F:Finset (Fin r)) (h:Fin m) (hh:h∈Jl owner F):0 < c h:=by
  obtain ⟨s, hs, hso⟩:=(FW owner F h).mp hh
  rw [← hcount h]
  exact Finset.card_pos.mpr ⟨s, (FR owner h s).mpr hso⟩
lemma DG {n m r:ℕ} (owner:Fin r→Option (Fin m))
    (c:Fin m→ℕ) (hcount:∀ h, (Cm owner h).card=c h)
    (row:Fin n→Finset (Fin m))
    (hglobal:∑ i, (1 / 2:ℚ)^(2+∑ h∈row i, c h)≤1):
    ∑ i, (1 / 2:ℚ)^(2+(JB owner (row i)).card)≤1:=by
  simpa only [JC owner c hcount] using hglobal
lemma DH {n m r:ℕ} (owner:Fin r→Option (Fin m))
    (c:Fin m→ℕ) (hcount:∀ h, (Cm owner h).card=c h)
    (row:Fin n→Finset (Fin m))
    (hforce:∀ J:Finset (Fin m), J.Nonempty→(∀ h∈J, 0 < c h)→
      (∑ i, if J⊆row i then (1 / 2:ℚ)^(1+∑ h∈row i \ J, c h) else 0)≤1)
    (F:Finset (Fin r)) (hF:F.Nonempty):
    (∑ i, if F⊆JB owner (row i) then
      (1 / 2:ℚ)^(1+(JB owner (row i) \ F).card) else 0)≤1:=by
  by_cases hJ:(Jl owner F).Nonempty
  · apply le_trans _ (hforce (Jl owner F) hJ
      (fun h hh=>Jm owner c hcount F h hh))
    apply Finset.sum_le_sum
    intro i hi
    by_cases hs:F⊆JB owner (row i)
    · have ht:=Jn owner (row i) F hs
      simp only [hs, ht, ↓reduceIte]
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      have he:=HL owner c hcount (row i) F
      omega
    · simp only [hs, ↓reduceIte]
      split_ifs <;> positivity
  · have hn:∀ i, ¬ F⊆JB owner (row i):=by
      intro i hs
      obtain ⟨s, hsF⟩:=hF
      obtain ⟨h, hh, hso⟩:=(FX owner (row i) s).mp (hs hsF)
      exact hJ ⟨h, (FW owner F h).mpr ⟨s, hsF, hso⟩⟩
    simp [hn]
end AG
namespace AB
open AG
def CX {m:ℕ} (c:Fin m→ℕ) (j:ℕ):ℕ:=
  ∑ h:Fin m with h.val < j, c h
lemma CZ {m:ℕ} (c:Fin m→ℕ) {j k:ℕ} (hjk:j≤k):
    CX c j≤CX c k:=by
  unfold CX
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro h hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ h,
      lt_of_lt_of_le (Finset.mem_filter.mp hh).2 hjk⟩
  · intro h hh hn
    exact Nat.zero_le _
lemma CY {m:ℕ} (c:Fin m→ℕ) (j:ℕ):
    CX c j≤∑ h, c h:=by
  unfold CX
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro h hh hn
    exact Nat.zero_le _
lemma Da {m:ℕ} (c:Fin m→ℕ) (h:Fin m):
    CX c (h.val+1)=CX c h.val+c h:=by
  have hs:(Finset.univ.filter fun k:Fin m=>k.val < h.val+1)=
      insert h (Finset.univ.filter fun k:Fin m=>k.val < h.val):=by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      by_cases he:k=h
      · exact Or.inl he
      · right
        have hn:k.val≠h.val:=fun hv=>he (Fin.ext hv)
        omega
    · intro hk
      rcases hk with rfl | hk <;> omega
  unfold CX
  rw [hs, Finset.sum_insert (by simp)]
  omega
lemma BC {m:ℕ} (c:Fin m→ℕ) {h k:Fin m} (hhk:h < k):
    CX c h.val+c h≤CX c k.val:=by
  rw [← Da]
  apply CZ
  exact hhk
lemma BD {m:ℕ} (c:Fin m→ℕ) (h:Fin m):
    CX c h.val+c h≤∑ k, c k:=by
  rw [← Da]
  exact CY c _
def BA {m r:ℕ} (c:Fin m→ℕ) (hbudget:(∑ h, c h)≤r)
    (x:Σ h:Fin m, Fin (c h)):Fin r:=
  ⟨CX c x.1.val+x.2.val, by
    have he:=BD c x.1
    have hx:=x.2.isLt
    omega⟩
lemma BB {m r:ℕ} (c:Fin m→ℕ) (hbudget:(∑ h, c h)≤r):
    Function.Injective (BA c hbudget):=by
  rintro ⟨h, k⟩ ⟨j, l⟩ he
  have hv:=congrArg Fin.val he
  change CX c h.val+k.val=CX c j.val+l.val at hv
  have hh:h=j:=by
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hb:=BC c (h:=h) (k:=j) hlt
      have hk:=k.isLt
      omega
    · have hb:=BC c (h:=j) (k:=h) hgt
      have hl:=l.isLt
      omega
  subst j
  have hkl:k=l:=Fin.ext (by omega)
  subst l
  rfl
lemma Hg {m r:ℕ} (c:Fin m→ℕ)
    (e:(Σ h:Fin m, Fin (c h)) ↪ Fin r):
    ∃ owner:Fin r→Option (Fin m),
      (∀ s h, owner s=some h↔∃ k:Fin (c h), e ⟨h, k⟩=s)∧
      (∀ h, (Cm owner h).card=c h):=by
  classical
  let owner:Fin r→Option (Fin m):=fun s=>
    if hs:∃ x, e x=s then some (Classical.choose hs).1 else none
  have hone:∀ x, owner (e x)=some x.1:=by
    intro x
    have hx:∃ y, e y=e x:=⟨x, rfl⟩
    dsimp only [owner]
    rw [dite_eq_left hx]
    have he:e (Classical.choose hx)=e x:=Classical.choose_spec hx
    rw [e.injective he]
  have hiff:∀ s h, owner s=some h↔∃ k:Fin (c h), e ⟨h, k⟩=s:=by
    intro s h
    constructor
    · intro ho
      have hx:∃ x, e x=s:=by
        by_contra hn
        dsimp only [owner] at ho
        split at ho
        · rename_i hx
          exact hn hx
        · contradiction
      let x:=Classical.choose hx
      have hex:e x=s:=Classical.choose_spec hx
      have hfirst:x.1=h:=by
        have heo:owner s=some x.1:=by rw [← hex]; exact hone x
        exact Option.some.inj (heo.symm.trans ho)
      obtain ⟨a, k⟩:=x
      dsimp only at hfirst hex
      subst a
      exact ⟨k, hex⟩
    · rintro ⟨k, hk⟩
      rw [← hk]
      exact hone ⟨h, k⟩
  refine ⟨owner, hiff, ?_⟩
  intro h
  have hc:=Finset.card_bij
    (s:=(Finset.univ:Finset (Fin (c h)))) (t:=Cm owner h)
    (fun k _=>e ⟨h, k⟩)
    (fun k _=>(FR owner h _).mpr (hone ⟨h, k⟩))
    (fun k _ l _ he=>Fin.ext (congrArg (fun x:Σ a:Fin m, Fin (c a)=>x.2.val)
      (e.injective he)))
    (fun s hs=>by
      obtain ⟨k, hk⟩:=(hiff s h).mp ((FR owner h s).mp hs)
      exact ⟨k, Finset.mem_univ k, hk⟩)
  simpa using hc.symm
lemma Dx {m r:ℕ} (c:Fin m→ℕ) (hbudget:(∑ h, c h)≤r):
    ∃ owner:Fin r→Option (Fin m),
      (∀ h, (Cm owner h).card=c h)∧
      (∀ s h, owner s=some h↔CX c h.val≤ s.val∧s.val < CX c h.val+c h):=by
  let e:(Σ h:Fin m, Fin (c h)) ↪ Fin r:=
    ⟨BA c hbudget, BB c hbudget⟩
  obtain ⟨owner, hiff, hcount⟩:=Hg c e
  refine ⟨owner, hcount, ?_⟩
  intro s h
  rw [hiff]
  constructor
  · rintro ⟨k, hk⟩
    have hv:=congrArg Fin.val hk
    change CX c h.val+k.val=s.val at hv
    have hklt:=k.isLt
    omega
  · intro hs
    let k:Fin (c h):=⟨s.val - CX c h.val, by omega⟩
    refine ⟨k, ?_⟩
    apply Fin.ext
    change CX c h.val+(s.val - CX c h.val)=s.val
    omega
lemma Hh {m r:ℕ} (c:Fin m→ℕ) (owner:Fin r→Option (Fin m))
    (hblock:∀ s h, owner s=some h↔
      CX c h.val≤ s.val∧s.val < CX c h.val+c h)
    (a b:Fin r) (h k:Fin m) (hab:a < b)
    (ha:owner a=some h) (hb:owner b=some k):h≤k:=by
  have ha':=(hblock a h).mp ha
  have hb':=(hblock b k).mp hb
  change h.val≤k.val
  by_contra hn
  have hkh:k < h:=by omega
  have hp:=BC c hkh
  have hab':a.val < b.val:=hab
  omega
lemma Hf {m r:ℕ} (c:Fin m→ℕ) (hbudget:(∑ h, c h)≤r)
    (owner:Fin r→Option (Fin m))
    (hcount:∀ h, (Cm owner h).card=c h)
    (hblock:∀ s h, owner s=some h↔
      CX c h.val≤ s.val∧s.val < CX c h.val+c h)
    (s:Fin r):owner s=none↔(∑ h, c h)≤ s.val:=by
  let early:Finset (Fin r):=Finset.univ.image (Fin.castLE hbudget)
  have hearly:early.card=∑ h, c h:=by
    dsimp only [early]
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective hbudget)]
    simp
  have hsub:JB owner Finset.univ⊆early:=by
    intro t ht
    obtain ⟨h, hh, hto⟩:=(FX owner Finset.univ t).mp ht
    have htb:=(hblock t h).mp hto
    have he:=BD c h
    have htlt:t.val < ∑ k, c k:=by omega
    apply Finset.mem_image.mpr
    exact ⟨⟨t.val, htlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have heq:JB owner Finset.univ=early:=by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hearly, JC owner c hcount]
  constructor
  · intro hn
    by_contra hlt
    have hs:s∈JB owner Finset.univ:=by
      rw [heq]
      apply Finset.mem_image.mpr
      exact ⟨⟨s.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
    obtain ⟨h, hh, hso⟩:=(FX owner Finset.univ s).mp hs
    rw [hn] at hso
    contradiction
  · intro hlate
    cases ho:owner s with
    | none=>rfl
    | some h=>
      have hb:=(hblock s h).mp ho
      have he:=BD c h
      omega
def DV {m r:ℕ} (c:Fin m→ℕ) (hbudget:(∑ h, c h)≤r)
    (h:Fin m) (hpos:0 < c h):Fin r:=BA c hbudget ⟨h, ⟨0, hpos⟩⟩
lemma DX {m r:ℕ} (c:Fin m→ℕ) (hbudget:(∑ h, c h)≤r)
    (h:Fin m) (hpos:0 < c h):
    (DV c hbudget h hpos).val=CX c h.val:=by
  rfl
lemma DW {m r:ℕ} (c:Fin m→ℕ) (hbudget:(∑ h, c h)≤r)
    (owner:Fin r→Option (Fin m))
    (hblock:∀ s h, owner s=some h↔
      CX c h.val≤ s.val∧s.val < CX c h.val+c h)
    (h:Fin m) (hpos:0 < c h):owner (DV c hbudget h hpos)=some h:=by
  apply (hblock _ h).mpr
  rw [DX]
  omega
lemma IJ {m r:ℕ} (owner:Fin r→Option (Fin m))
    (R:Finset (Fin m)) (s:Fin r) (h:Fin m) (hs:owner s=some h):
    s∈JB owner R↔h∈R:=by
  rw [FX]
  constructor
  · rintro ⟨k, hk, hko⟩
    have he:k=h:=Option.some.inj (hko.symm.trans hs)
    simpa [he] using hk
  · intro hh
    exact ⟨h, hh, hs⟩
lemma DA {m r:ℕ} (c:Fin m→ℕ) (hbudget:(∑ h, c h)≤r):
    ∃ owner:Fin r→Option (Fin m),
      (∀ h, (Cm owner h).card=c h)∧
      (∀ s h, owner s=some h↔
        CX c h.val≤ s.val∧s.val < CX c h.val+c h)∧
      (∀ a b h k, a < b→ owner a=some h→ owner b=some k→h≤k)∧
      (∀ s, owner s=none↔(∑ h, c h)≤ s.val):=by
  obtain ⟨owner, hcount, hblock⟩:=Dx c hbudget
  exact ⟨owner, hcount, hblock, Hh c owner hblock,
    Hf c hbudget owner hcount hblock⟩
end AB
namespace AC
lemma Fl (a b:ℕ) (h:b≤a):
    (2:ℚ)^a*(1 / 2:ℚ)^b=(2:ℚ)^(a - b):=by
  conv_lhs=>rw [show a=(a - b)+b by omega]
  rw [pow_add, mul_assoc, ← mul_pow]
  norm_num
lemma BJ {r:ℕ} (R:Finset (Fin r)):R.card≤r:=by
  have h:=Finset.card_le_card (Finset.subset_univ R)
  simpa only [Finset.card_univ, Fintype.card_fin] using h
lemma Fj {n r:ℕ} (slots:Fin n→Finset (Fin r))
    (h:(∑ i, (1 / 2:ℚ)^(2+(slots i).card))≤1):
    (∑ i, 2^(r - (slots i).card))≤2^(r+2):=by
  have hs:=mul_le_mul_of_nonneg_left h (by positivity:(0:ℚ)≤2^(r+2))
  simp only [Finset.mul_sum, mul_one] at hs
  have hw:∀ i, (2:ℚ)^(r+2)*(1 / 2:ℚ)^(2+(slots i).card)=
      (2:ℚ)^(r - (slots i).card):=by
    intro i
    have hd:=BJ (slots i)
    rw [Fl _ _ (by omega)]
    congr 1
    omega
  simp_rw [hw] at hs
  exact_mod_cast hs
lemma EH {r:ℕ} (R F:Finset (Fin r)) (hF:F⊆R):
    (2:ℚ)^(r+2)*(1 / 2:ℚ)^(1+(R \ F).card)=
      (2:ℚ)^(F.card+1)*(2:ℚ)^(r - R.card):=by
  have hd:=BJ R
  have hf:=Finset.card_le_card hF
  rw [Finset.card_sdiff_of_subset hF, Fl _ _ (by omega)]
  rw [show r+2 - (1+(R.card - F.card))=(F.card+1)+(r - R.card) by omega]
  exact pow_add _ _ _
lemma EB {n r:ℕ} (slots:Fin n→Finset (Fin r))
    (F:Finset (Fin r))
    (h:(∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card)
      else 0)≤1):
    (∑ i, if F⊆slots i then 2^(F.card+1)*2^(r - (slots i).card)
      else 0)≤2^(r+2):=by
  have hs:=mul_le_mul_of_nonneg_left h (by positivity:(0:ℚ)≤2^(r+2))
  simp only [Finset.mul_sum, mul_one] at hs
  have hw:∀ i, (2:ℚ)^(r+2)*
      (if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)=
      (if F⊆slots i then (2:ℚ)^(F.card+1)*(2:ℚ)^(r - (slots i).card)
      else 0):=by
    intro i
    by_cases hF:F⊆slots i
    · simpa only [ite_eq_left hF] using EH (slots i) F hF
    · simp only [ite_eq_right hF, mul_zero]
  simp_rw [hw] at hs
  exact_mod_cast hs
end AC
namespace FiberCounts
def count {n:ℕ} {β:Type} [Fintype β] [DecidableEq β]
    (row:Fin n→β) (s:β):ℕ:=
  (Finset.univ.filter fun i=>row i=s).card
lemma JX {n:ℕ} {β:Type} [Fintype β] [DecidableEq β]
    (row:Fin n→β) (w:β→ℕ):
    (∑ s, count row s*w s)=∑ i, w (row i):=by
  simpa [count, Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise' (Finset.univ:Finset (Fin n)) row w)
lemma total {n:ℕ} {β:Type} [Fintype β] [DecidableEq β]
    (row:Fin n→β):(∑ s, count row s)=n:=by
  simpa using JX row (fun _=>1)
lemma bound {n:ℕ} {β:Type} [Fintype β] [DecidableEq β]
    (row:Fin n→β) (s:β):count row s≤n:=by
  have h:=Finset.card_le_card (Finset.filter_subset (fun i=>row i=s) Finset.univ)
  simpa only [count, Finset.card_univ, Fintype.card_fin] using h
lemma Hr {n:ℕ} {β:Type} [Fintype β] [DecidableEq β]
    (row:Fin n→β) (s:β):0 < count row s↔∃ i, row i=s:=by
  simp only [count, Finset.card_pos, Finset.nonempty_iff_ne_empty, ne_eq]
  simp
lemma DU {n:ℕ} {β:Type} [Fintype β] [DecidableEq β]
    (row:Fin n→β) (P:β→Prop) [DecidablePred P]:
    (∑ s, if P s then count row s else 0)=
      (Finset.univ.filter fun i=>P (row i)).card:=by
  have h:=JX row (fun s=>if P s then 1 else 0)
  simpa [mul_ite] using h
end FiberCounts
namespace MaskDecode
def decode (r:ℕ) (s:Fin (2^r)):Finset (Fin r):=
  Finset.univ.filter fun j=>s.val.testBit j.val=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma Df (r:ℕ) (hr:r≤5):Function.Surjective (decode r):=by
  interval_cases r <;> decide+kernel
end MaskDecode
namespace Az
open MaskDecode
def IP {n r:ℕ} (slots:Fin n→Finset (Fin r)) (j:Fin r):ℕ:=
  (Finset.univ.filter fun i=>j∈slots i).card
def Ci {n r:ℕ} (slots:Fin n→Finset (Fin r)) (j k:Fin r):ℕ:=
  (Finset.univ.filter fun i=>j∈slots i∧k∈slots i).card
def BO {n r:ℕ} (slots:Fin n→Finset (Fin r)):Prop:=
  ∀ i j k, j∈slots i→(∀ l:Fin r, l < j→l∉slots i)→j < k→k∈slots i→
    2≤Ci slots j k→Ci slots j k < IP slots j→
    ∃ l:Fin r, j < l∧l < k∧l∈slots i∧
      Ci slots j l=1∧Ci slots j l < IP slots j
def FP (r:ℕ) (c:Fin (2^r)→ℕ) (j:Fin r):ℕ:=
  ∑ s, if j∈decode r s then c s else 0
def FN (r:ℕ) (c:Fin (2^r)→ℕ) (j k:Fin r):ℕ:=
  ∑ s, if j∈decode r s∧k∈decode r s then c s else 0
def FO (r:ℕ) (s:Fin (2^r)) (j:Fin r):Prop:=
  j∈decode r s∧∀ l:Fin r, l < j→l∉decode r s
def profile (r n:ℕ) (c:Fin (2^r)→ℕ):Prop:=
  (∀ s, c s≤n)∧
  (∑ s, c s)=n∧
  (∑ s, 2^(r - (decode r s).card)*c s)≤2^(r+2)∧
  (∀ f:Fin (2^r), (decode r f).Nonempty→
    (∑ s, if decode r f⊆decode r s then
      (2^((decode r f).card+1)*2^(r - (decode r s).card))*c s else 0)≤2^(r+2))∧
  (∀ s j k, FO r s j→j < k→k∈decode r s→
    (0 < c s∧2≤FN r c j k∧FN r c j k < FP r c j)→
    ∃ l:Fin r, j < l∧l < k∧l∈decode r s∧
      FN r c j l=1∧FN r c j l < FP r c j)
lemma Dp {n r:ℕ} (slots:Fin n→Finset (Fin r))
    (row:Fin n→Fin (2^r)) (hrow:∀ i, decode r (row i)=slots i)
    (hglobal:(∑ i, (1 / 2:ℚ)^(2+(slots i).card))≤1)
    (hforced:∀ F:Finset (Fin r), F.Nonempty→
      (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)
    (htemporal:BO slots):profile r n (FiberCounts.count row):=by
  classical
  let c:=FiberCounts.count row
  have hsupport:∀ j, FP r c j=IP slots j:=by
    intro j
    unfold FP IP
    have h:=FiberCounts.DU row (fun s=>j∈decode r s)
    simpa only [hrow] using h
  have hcommon:∀ j k, FN r c j k=Ci slots j k:=by
    intro j k
    unfold FN Ci
    have h:=FiberCounts.DU row (fun s=>j∈decode r s∧k∈decode r s)
    simpa only [hrow] using h
  dsimp only [c] at hsupport hcommon
  refine ⟨FiberCounts.bound row, FiberCounts.total row, ?_, ?_, ?_⟩
  · have h:=AC.Fj slots hglobal
    have hw:=FiberCounts.JX row (fun s=>2^(r - (decode r s).card))
    simp only [hrow] at hw
    simpa only [Nat.mul_comm, hw] using h
  · intro f hf
    have h:=AC.EB slots (decode r f) (hforced _ hf)
    have hw:=FiberCounts.JX row (fun s=>if decode r f⊆decode r s then
      2^((decode r f).card+1)*2^(r - (decode r s).card) else 0)
    simp only [hrow] at hw
    have he:(∑ s, if decode r f⊆decode r s then
        (2^((decode r f).card+1)*2^(r - (decode r s).card))*c s else 0)=
        ∑ i, if decode r f⊆slots i then
        2^((decode r f).card+1)*2^(r - (slots i).card) else 0:=by
      simpa only [c, mul_ite, mul_zero, Nat.mul_comm] using hw
    rw [he]
    exact h
  · intro s j k hj hjk hks hc
    obtain ⟨i, hi⟩:=(FiberCounts.Hr row s).mp hc.1
    have hs:slots i=decode r s:=by rw [← hrow i, hi]
    have hji:j∈slots i:=by simpa only [hs] using hj.1
    have hji':∀ l:Fin r, l < j→l∉slots i:=by simpa only [hs] using hj.2
    have hki:k∈slots i:=by simpa only [hs] using hks
    have h2:2≤Ci slots j k:=by simpa only [hcommon] using hc.2.1
    have hp:Ci slots j k < IP slots j:=by
      simpa only [hcommon, hsupport] using hc.2.2
    obtain ⟨l, hjl, hlk, hli, h1, hlp⟩:=htemporal i j k hji hji' hjk hki h2 hp
    refine ⟨l, hjl, hlk, ?_, ?_, ?_⟩
    · simpa only [hs] using hli
    · simpa only [hcommon] using h1
    · simpa only [hcommon, hsupport] using hlp
lemma DB {n r:ℕ} (hr:r≤5) (slots:Fin n→Finset (Fin r))
    (hglobal:(∑ i, (1 / 2:ℚ)^(2+(slots i).card))≤1)
    (hforced:∀ F:Finset (Fin r), F.Nonempty→
      (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)
    (htemporal:BO slots):∃ c:Fin (2^r)→ℕ, profile r n c:=by
  classical
  choose row hrow using fun i=>Df r hr (slots i)
  exact ⟨FiberCounts.count row, Dp slots row hrow hglobal hforced htemporal⟩
end Az
namespace AF
open AG
open AB
open Az
def IQ {n m:ℕ} (row:Fin n→Finset (Fin m)) (h:Fin m):Finset (Fin n):=
  Finset.univ.filter fun i=>h∈row i
def Hs {n m:ℕ} (c:Fin m→ℕ) (row:Fin n→Finset (Fin m)):Prop:=
  ∀ i j k, 0 < c j→0 < c k→j∈row i→
    (∀ h:Fin m, h < j→0 < c h→h∉row i)→j < k→k∈row i→
    IQ row j∩IQ row k≠IQ row j→
    ∃ h:Fin m, 0 < c h∧j < h∧h≤k∧
      IQ row j∩IQ row h={i}
lemma Cj {n m:ℕ} (row:Fin n→Finset (Fin m)) (j k:Fin m):
    Ci row j k=(IQ row j∩IQ row k).card:=by
  unfold Ci IQ
  congr 1
  ext i
  simp
lemma JE {n m r:ℕ} (owner:Fin r→Option (Fin m))
    (row:Fin n→Finset (Fin m)) (a:Fin r) (j:Fin m) (ha:owner a=some j):
    IP (fun i=>JB owner (row i)) a=IP row j:=by
  unfold IP
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact IJ owner (row i) a j ha
lemma JD {n m r:ℕ} (owner:Fin r→Option (Fin m))
    (row:Fin n→Finset (Fin m)) (a b:Fin r) (j k:Fin m)
    (ha:owner a=some j) (hb:owner b=some k):
    Ci (fun i=>JB owner (row i)) a b=Ci row j k:=by
  unfold Ci
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [IJ owner (row i) a j ha, IJ owner (row i) b k hb]
lemma IT {n m r:ℕ} (c:Fin m→ℕ)
    (hbudget:(∑ h, c h)≤r) (owner:Fin r→Option (Fin m))
    (hblock:∀ s h, owner s=some h↔
      CX c h.val≤ s.val∧s.val < CX c h.val+c h)
    (row:Fin n→Finset (Fin m)) (horiginal:Hs c row):
    BO (fun i=>JB owner (row i)):=by
  let slots:=fun i=>JB owner (row i)
  change BO slots
  intro i a b hai hfresh hab hbi htwo hproper
  obtain ⟨j, hji, haj⟩:=(FX owner (row i) a).mp hai
  obtain ⟨k, hki, hbk⟩:=(FX owner (row i) b).mp hbi
  have haBlock:=(hblock a j).mp haj
  have hbBlock:=(hblock b k).mp hbk
  have hjpos:0 < c j:=by omega
  have hkpos:0 < c k:=by omega
  have hsa:IP slots a=IP row j:=JE owner row a j haj
  have hcab:Ci slots a b=Ci row j k:=JD owner row a b j k haj hbk
  have hjkle:j≤k:=Hh c owner hblock a b j k hab haj hbk
  have hjk:j < k:=by
    have hne:j≠k:=by
      intro he
      have hc:Ci slots a b=IP slots a:=by
        rw [hcab, hsa, he]
        simp [Ci, IP]
      omega
    exact lt_of_le_of_ne hjkle hne
  have hjfresh:∀ h:Fin m, h < j→0 < c h→h∉row i:=by
    intro h hhj hhpos hhi
    let t:=DV c hbudget h hhpos
    have hto:owner t=some h:=DW c hbudget owner hblock h hhpos
    have hti:t∈slots i:=(IJ owner (row i) t h hto).mpr hhi
    have htv:t.val=CX c h.val:=DX c hbudget h hhpos
    have hp:=BC c hhj
    have hta:t < a:=by
      change t.val < a.val
      omega
    exact hfresh t hta hti
  have hjproper:IQ row j∩IQ row k≠IQ row j:=by
    intro he
    have hc:=congrArg Finset.card he
    rw [← Cj] at hc
    change Ci row j k=IP row j at hc
    omega
  obtain ⟨h, hhpos, hjh, hhk, hsingle⟩:=
    horiginal i j k hjpos hkpos hji hjfresh hjk hki hjproper
  let t:=DV c hbudget h hhpos
  have hto:owner t=some h:=DW c hbudget owner hblock h hhpos
  have htv:t.val=CX c h.val:=DX c hbudget h hhpos
  have hat:a < t:=by
    have hp:=BC c hjh
    change a.val < t.val
    omega
  have htle:t≤b:=by
    have hp:=CZ c (show h.val≤k.val from hhk)
    change t.val≤b.val
    omega
  have hi:i∈IQ row j∩IQ row h:=by rw [hsingle]; simp
  have hhi:h∈row i:=(Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
  have hti:t∈slots i:=(IJ owner (row i) t h hto).mpr hhi
  have hct:Ci slots a t=1:=by
    rw [JD owner row a t j h haj hto, Cj, hsingle]
    simp
  have htb:t < b:=by
    change t.val < b.val
    by_contra hn
    have hval:t.val≤b.val:=htle
    have he:t=b:=Fin.ext (by omega)
    rw [he] at hct
    omega
  exact ⟨t, hat, htb, hti, hct, by omega⟩
lemma Dy {n m r:ℕ} (c:Fin m→ℕ)
    (hbudget:(∑ h, c h)≤r) (row:Fin n→Finset (Fin m))
    (hglobal:∑ i, (1 / 2:ℚ)^(2+∑ h∈row i, c h)≤1)
    (hforce:∀ J:Finset (Fin m), J.Nonempty→(∀ h∈J, 0 < c h)→
      (∑ i, if J⊆row i then (1 / 2:ℚ)^(1+∑ h∈row i \ J, c h) else 0)≤1)
    (htemporal:Hs c row):
    ∃ slots:Fin n→Finset (Fin r),
      (∑ i, (1 / 2:ℚ)^(2+(slots i).card)≤1)∧
      (∀ F:Finset (Fin r), F.Nonempty→
        (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)∧
      BO slots:=by
  obtain ⟨owner, hcount, hblock, horder, hpadding⟩:=DA c hbudget
  refine ⟨fun i=>JB owner (row i), ?_, ?_, ?_⟩
  · exact DG owner c hcount row hglobal
  · exact DH owner c hcount row hforce
  · exact IT c hbudget owner hblock row htemporal
end AF
namespace Az
end Az
namespace Ac
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open AD
open AE
open Af
lemma Cq (l:List ℕ) (n j w:ℕ):
    (l.filter fun a=>decide (a < n+j)).count w=
      (l.map fun a=>if a=w∧a < n+j then 1 else 0).sum:=by
  induction l with
  | nil=>simp
  | cons a l ih=>
    by_cases ha:a < n+j
    · by_cases he:a=w
      · subst a
        simp [ha, ih, Nat.add_comm]
      · simp [ha, he, ih]
    · simp [ha, ih]
lemma JL (n:ℕ) (C:Circuit) (i:Fin n):
    As.JI C n i.val=JW C i.val:=by
  unfold As.JI JW
  apply Finset.sum_congr rfl
  intro j hj
  unfold As.JN
  rw [Cq]
  congr 1
  apply List.map_congr_left
  intro a ha
  by_cases he:a=i.val
  · subst a
    have hi:i.val < n+j.val:=by omega
    simp [hi]
  · simp [he]
lemma JK (n:ℕ) (C:Circuit) (h:Fin C.gates.length):
    As.JI C n (n+h.val)=∑ j, ET C n j h:=by
  unfold As.JI
  apply Finset.sum_congr rfl
  intro j hj
  unfold As.JN ET
  rw [Cq]
  congr 1
  apply List.map_congr_left
  intro a ha
  by_cases he:a=n+h.val
  · subst a
    simp [JQ]
  · simp [JQ, he]
def rows (n:ℕ) (C:Circuit) (i:Fin n):Finset (Fin C.gates.length):=
  Finset.univ.filter fun h=>(C.wires (Iz i)).getD (n+h.val) false=true
lemma FU (n:ℕ) (C:Circuit) (i:Fin n) (h:Fin C.gates.length):
    h∈rows n C i↔(C.wires (Iz i)).getD (n+h.val) false=true:=by
  simp [rows]
lemma HX (n:ℕ) (C:Circuit) (i:Fin n) (c:Fin C.gates.length→ℕ):
    (∑ h∈rows n C i, c h)=∑ h, c h*
      (if (C.wires (Iz i)).getD (n+h.val) false then 1 else 0):=by
  unfold rows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h hh
  cases (C.wires (Iz i)).getD (n+h.val) false <;> simp
lemma FS {G:ℕ} (J:Finset (Fin G)) (h:Fin G):
    h.val∈J.image Fin.val↔h∈J:=by
  constructor
  · intro hh
    obtain ⟨k, hk, hkh⟩:=Finset.mem_image.mp hh
    have he:k=h:=Fin.ext hkh
    simpa [he] using hk
  · intro hh
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
lemma HK (n:ℕ) (C:Circuit) (i:Fin n)
    (c:Fin C.gates.length→ℕ) (J:Finset (Fin C.gates.length)):
    (∑ h∈rows n C i \ J, c h)=∑ h:Fin C.gates.length,
      if h.val∈J.image Fin.val then 0 else c h*
        (if (C.wires (Iz i)).getD (n+h.val) false then 1 else 0):=by
  have hs:rows n C i \ J=Finset.univ.filter (fun h=>
      (C.wires (Iz i)).getD (n+h.val) false=true∧h∉J):=by
    ext h
    simp [rows]
  rw [hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [FS]
  by_cases hj:h∈J <;>
    cases (C.wires (Iz i)).getD (n+h.val) false <;> simp [hj]
lemma Fk (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn fun t=>decide (t∈S))=decide (2≤S.card))
    (hraw:∀ i:Fin n, JW C i≤2):
    (∑ i:Fin n, (1 / 2:ℚ)^(2+∑ h∈rows n C i, credit C n h))≤1:=by
  have hsingle:∀ i:Fin n, C.eval (Iz i)=false:=by
    intro i
    change C.eval (List.ofFn fun t:Fin n=>decide (t=i))=false
    simpa using hcorrect {i}
  have hpair:∀ i k:Fin n, i≠k→C.eval (pairInput i k)=true:=by
    intro i k hik
    change C.eval (List.ofFn fun t:Fin n=>decide (t=i∨t=k))=true
    simpa [hik] using hcorrect {i,k}
  have hg:=Ja C hC hsingle hpair (fun _=>2) (credit C n)
    (fun i h=>if (C.wires (Iz i)).getD (n+h.val) false then 1 else 0)
    hraw (Ea C n) (by
      intro i h
      have hlen:(Iz i).length=n:=by simp [Iz]
      simpa only [hlen] using
        ER C (List.replicate n false) (Iz i) h)
  simpa only [HX n C] using hg
lemma Js (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn fun t=>decide (t∈S))=decide (2≤S.card))
    (hraw:∀ i:Fin n, JW C i≤2)
    (hzero:∀ h:Fin C.gates.length,
      (C.wires (As.Ku n)).getD (n+h.val) false=false)
    (J:Finset (Fin C.gates.length)) (hJ:J.Nonempty):
    (∑ i:Fin n, if J⊆rows n C i then
      (1 / 2:ℚ)^(1+∑ h∈rows n C i \ J, credit C n h) else 0)≤1:=by
  let X:Finset (Fin n):=Finset.univ.filter fun i=>J⊆rows n C i
  let index:Fin X.card→Fin n:=fun t=>((Finset.equivFin X).symm t).val
  have hindex:∀ t, index t∈X:=fun t=>((Finset.equivFin X).symm t).property
  have hinj:Function.Injective index:=by
    intro a b hab
    exact (Finset.equivFin X).symm.injective (Subtype.ext hab)
  let j:Fin C.gates.length:=J.min' hJ
  have hjJ:j∈J:=Finset.min'_mem J hJ
  have hjF:j.val∈J.image Fin.val:=(FS J j).mpr hjJ
  have hbefore:∀ k < j.val, k∉J.image Fin.val:=by
    intro k hkj hkF
    obtain ⟨h, hhJ, hhk⟩:=Finset.mem_image.mp hkF
    have hm:j≤h:=Finset.min'_le J h hhJ
    have hmv:j.val≤h.val:=hm
    omega
  have hF:∀ t k, k∈J.image Fin.val→k < C.gates.length→
      (C.wires (As.IA (index t))).getD (n+k) false=true:=by
    intro t k hk hkvalid
    obtain ⟨h, hhJ, hhk⟩:=Finset.mem_image.mp hk
    have hsub:J⊆rows n C (index t):=(Finset.mem_filter.mp (hindex t)).2
    have ht:=(FU n C (index t) h).mp (hsub hhJ)
    subst k
    exact ht
  have hf:=An.Jr n X.card C hC
    (J.image Fin.val) index hinj j hjF hbefore (hzero j)
    (fun t=>by rw [JL]; exact hraw (index t)) hcorrect hF (credit C n)
    (fun h=>by rw [JK]; exact Ea C n h)
  let f:Fin n→ℚ:=fun i=>(1 / 2:ℚ)^
    (1+∑ h∈rows n C i \ J, credit C n h)
  have hf':(∑ t:Fin X.card, f (index t))≤1:=by
    convert hf using 1
    simp [f, HK n C, As.IA, Iz]
  have hsum:(∑ t:Fin X.card, f (index t))=∑ i∈X, f i:=by
    calc
      _=∑ i:X, f i.val:=(Finset.equivFin X).symm.sum_comp (fun i:X=>f i.val)
      _=∑ i∈X, f i:=Finset.sum_coe_sort X f
  rw [hsum] at hf'
  simpa only [X, f, Finset.sum_filter] using hf'
lemma GE (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)
    (hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn fun t=>decide (t∈S))=decide (2≤S.card))
    (hraw:∀ i:Fin n, JW C i≤2)
    (J:Finset (Fin C.gates.length)) (hJ:J.Nonempty):
    (∑ i:Fin n, if J⊆rows n C i then
      (1 / 2:ℚ)^(1+∑ h∈rows n C i \ J, credit C n h) else 0)≤1:=by
  apply Js n C hC hcorrect hraw
  · intro h
    exact Ax.GG n C hC hshape h
  · exact hJ
end Ac
namespace Ag
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover
def step (w:List Bool) (g:Gate):List Bool:=
  w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma Ed:∀ (gs:List Gate) (w:List Bool),
    ∃ t, gs.foldl step w=w++t∧t.length=gs.length
  | [], w=>⟨[], by simp⟩
  | g::gs, w=>by
    obtain ⟨t, ht, hl⟩:=Ed gs (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i=>w.getD i false)::t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]
lemma Ec (gs:List Gate) (w:List Bool):
    (gs.foldl step w).length=w.length+gs.length:=by
  obtain ⟨t, ht, hl⟩:=Ed gs w
  rw [ht, List.length_append, hl]
lemma Eb (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length):
    (gs.foldl step w).getD i false=w.getD i false:=by
  obtain ⟨t, ht, -⟩:=Ed gs w
  rw [ht, List.getD_append _ _ _ _ hi]
lemma EN (C:Circuit) (j:ℕ) (hj:j < C.gates.length):
    gateAt C j=C.gates[j]:=by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma EW (n:ℕ) (C:Circuit) (hb:ReadsBack n C)
    (j:ℕ) (hj:j < C.gates.length) (x:List Bool) (hx:x.length=n):
    (C.wires x).getD (n+j) false=
      C.gates[j].op.eval (C.gates[j].inputs.map fun a=>(C.wires x).getD a false):=by
  have hsplit:C.gates=C.gates.take j++C.gates[j]::C.gates.drop (j+1):=by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  let w:=(C.gates.take j).foldl step x
  have hw:w.length=n+j:=by
    simp only [w, Ec, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hW:C.wires x=(C.gates.drop (j+1)).foldl step (step w C.gates[j]):=by
    change C.gates.foldl step x=_
    conv_lhs=>rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hindex:(C.wires x).getD (n+j) false=
      C.gates[j].op.eval (C.gates[j].inputs.map fun a=>w.getD a false):=by
    rw [hW, Eb _ _ _ (by simp [step]; omega)]
    change (w++[_]).getD (n+j) false=_
    rw [← hw, List.getD_append_right _ _ _ _ le_rfl]
    simp
  rw [hindex]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal:a < n+j:=by
    apply hb j hj a
    simpa only [EN C j hj] using ha
  have ht:a < (step w C.gates[j]).length:=by simp [step]; omega
  rw [hW, Eb _ _ _ ht]
  exact (List.getD_append _ _ _ _ (by omega:a < w.length)).symm
def singleton {n:ℕ} (i:Fin n):List Bool:=
  List.ofFn (fun k:Fin n=>decide (k=i))
def wire (n:ℕ) (C:Circuit) (i:Fin n) (w:ℕ):Bool:=
  (C.wires (singleton i)).getD w false
def AT (n:ℕ) (C:Circuit) (u v:ℕ):Prop:=
  ∃ j, ∃ hj:j < C.gates.length, v=n+j∧u∈C.gates[j].inputs
lemma AU {n:ℕ} {C:Circuit} (hb:ReadsBack n C) {u v:ℕ}
    (h:AT n C u v):u < v:=by
  obtain ⟨j, hj, rfl, hu⟩:=h
  apply hb j hj u
  simpa only [EN C j hj] using hu
lemma Kq (C:Circuit) (x:List Bool):
    (C.wires x).length=x.length+C.gates.length:=
  Ec C.gates x
lemma Kh {n:ℕ} (C:Circuit) (i:Fin n) (u:ℕ) (hu:u < n):
    wire n C i u=true↔u=i.val:=by
  unfold wire
  change (C.gates.foldl step (singleton i)).getD u false=true↔_
  rw [Eb _ _ _ (by simp [singleton]; exact hu)]
  simp only [singleton, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    hu, ↓reduceDIte, Option.getD_some, decide_eq_true_eq]
  exact Fin.ext_iff
def IM (n:ℕ) (C:Circuit) (u:ℕ):Finset ℕ:=
  ((Finset.range C.gates.length).filter fun j=>u∈(gateAt C j).inputs).image
    (fun j=>n+j)
lemma FV {n:ℕ} {C:Circuit} {u v:ℕ}:
    v∈IM n C u↔AT n C u v:=by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩:=Finset.mem_image.mp h
    obtain ⟨hj, hu⟩:=Finset.mem_filter.mp hj
    have hj':=Finset.mem_range.mp hj
    exact ⟨j, hj', rfl, by simpa only [EN C j hj'] using hu⟩
  · rintro ⟨j, hj, rfl, hu⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ?_⟩, rfl⟩
    simpa only [EN C j hj] using hu
end Ag
namespace Ag
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover
lemma DS (S:Finset ℕ) (f:ℕ→List ℕ) (u:ℕ):
    (S.filter fun j=>u∈f j).card≤∑ j∈S, (f j).count u:=by
  classical
  calc
    _=∑ j∈S.filter (fun j=>u∈f j), (1:ℕ):=by simp
    _≤∑ j∈S.filter (fun j=>u∈f j), (f j).count u:=by
      apply Finset.sum_le_sum
      intro j hj
      exact List.count_pos_iff.mpr (Finset.mem_filter.mp hj).2
    _≤∑ j∈S, (f j).count u:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j hj hj'
      exact Nat.zero_le _
lemma IN (n:ℕ) (C:Circuit) (u:ℕ):
    (IM n C u).card≤readsIn C (Finset.range C.gates.length) u:=by
  unfold IM readsIn
  exact Finset.card_image_le.trans (DS _ _ _)
lemma JA {n:ℕ} {C:Circuit} {u:ℕ}
    (hcount:readsIn C (Finset.range C.gates.length) u≤1)
    {v w:ℕ} (hv:AT n C u v) (hw:AT n C u w):v=w:=by
  have hc:=(IN n C u).trans hcount
  exact Finset.card_le_one.mp hc v (FV.mpr hv) w (FV.mpr hw)
end Ag
namespace Ag
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover
def AS (n:ℕ) (C:Circuit) (i:Fin n) (u v:ℕ):Prop:=
  AT n C u v∧wire n C i u=true∧wire n C i v=true
abbrev AQ (n:ℕ) (C:Circuit) (i:Fin n):ℕ→ℕ→Prop:=
  Relation.ReflTransGen (AS n C i)
lemma Hu {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (hmono:AndOrOnly C) (hbinary:∀ g∈C.gates, g.inputs.length=2)
    (i:Fin n) (w:ℕ):wire n C i w=true→AQ n C i i.val w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    intro hpos
    by_cases hw:w < n
    · have he:=(Kh C i w hw).mp hpos
      subst w
      exact .refl
    · have hwlen:w < n+C.gates.length:=by
        by_contra hnot
        have he:wire n C i w=false:=by
          unfold wire
          apply List.getD_eq_default
          rw [Kq]
          simp only [singleton, List.length_ofFn]
          omega
        rw [he] at hpos
        contradiction
      let j:=w-n
      have hj:j < C.gates.length:=by dsimp [j]; omega
      have hwj:w=n+j:=by dsimp [j]; omega
      have he:=EW n C hb j hj (singleton i) (by simp [singleton])
      change wire n C i (n+j)=
        C.gates[j].op.eval (C.gates[j].inputs.map fun a=>wire n C i a) at he
      have hp:C.gates[j].op.eval
          (C.gates[j].inputs.map fun a=>wire n C i a)=true:=by
        rw [← he, ← hwj]
        exact hpos
      have hex:∃ a∈C.gates[j].inputs, wire n C i a=true:=by
        rcases hmono C.gates[j] (List.getElem_mem hj) with hand | hor
        · obtain ⟨a, b, hins⟩:=List.length_eq_two.mp (hbinary _ (List.getElem_mem hj))
          have hab:(wire n C i a && wire n C i b)=true:=by
            simpa [hand, hins, GateOp.eval] using hp
          have hbool:∀ a b:Bool, (a && b)=true→a=true:=by decide
          exact ⟨a, by simp [hins], hbool _ _ hab⟩
        · simpa only [hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] using hp
      obtain ⟨a, ha, hat⟩:=hex
      have hread:AT n C a w:=⟨j, hj, hwj, ha⟩
      exact (ih a (AU hb hread) hat).tail ⟨hread, hat, hpos⟩
lemma AR {n:ℕ} {C:Circuit} {i:Fin n} (hb:ReadsBack n C)
    {u v:ℕ} (hp:AQ n C i u v):u≤v:=by
  induction hp with
  | refl=>exact le_rfl
  | tail hp hs ih=>exact ih.trans (Nat.le_of_lt (AU hb hs.1))
def AM (n:ℕ) (C:Circuit) (u v:ℕ):Prop:=
  AT n C u v∧readsIn C (Finset.range C.gates.length) u≤1∧u≠C.output
abbrev AK (n:ℕ) (C:Circuit):ℕ→ℕ→Prop:=
  Relation.ReflTransGen (AM n C)
lemma Ht {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (i:Fin n) (b:ℕ)
    (hneg:wire n C i C.output=false)
    (hlow:∀ u, n≤u→u < b→wire n C i u=true→
      readsIn C (Finset.range C.gates.length) u≤1)
    {q:ℕ} (hpath:AQ n C i q b) (hq:n≤q):
    AK n C q b:=by
  revert hq
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl=>intro _; exact .refl
  | @head a c hs hrest ih=>
    intro ha
    have hab:a < b:=(AU hb hs.1).trans_le (AR hb hrest)
    have hc:n≤c:=by
      obtain ⟨j, hj, rfl, _⟩:=hs.1
      omega
    refine Relation.ReflTransGen.head ⟨hs.1, hlow a ha hab hs.2.1, ?_⟩ (ih hc)
    intro he
    have hp:=hs.2.1
    rw [he, hneg] at hp
    contradiction
lemma EJ {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (hmono:AndOrOnly C) (hbinary:∀ g∈C.gates, g.inputs.length=2)
    (i:Fin n) (b:ℕ) (hbgate:n≤b)
    (hpos:wire n C i b=true) (hneg:wire n C i C.output=false)
    (hfresh:∀ u, n≤u→u < b→
      2≤readsIn C (Finset.range C.gates.length) u→wire n C i u=false):
    ∃ q, AT n C i.val q∧wire n C i q=true∧
      AK n C q b∧b≠C.output:=by
  have hpath:=Hu hb hmono hbinary i b hpos
  rcases hpath.cases_head with he | ⟨q, hq, hqb⟩
  · have:=i.isLt
    omega
  · have hqgate:n≤q:=by
      obtain ⟨j, hj, rfl, _⟩:=hq.1
      omega
    refine ⟨q, hq.1, hq.2.2, Ht hb i b hneg ?_ hqb hqgate, ?_⟩
    · intro u hu hub hup
      by_contra hn
      have hz:=hfresh u hu hub (by omega)
      rw [hz] at hup
      contradiction
    · intro he
      rw [he, hneg] at hpos
      contradiction
end Ag
namespace Ag
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover
lemma AL {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    {q b:ℕ} (hchain:AK n C q b):q≤b:=by
  induction hchain with
  | refl=>exact le_rfl
  | tail hchain hs ih=>exact ih.trans (Nat.le_of_lt (AU hb hs.1))
lemma Dw {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    {q b:ℕ} (hq:n≤q) (hchain:AK n C q b):
    ∃ Z:Finset ℕ, (q∈Z∨q=b)∧b∉Z∧C.output∉Z∧
      (∀ u∈Z, n≤u∧u < b∧readsIn C (Finset.range C.gates.length) u≤1)∧
      (∀ u∈Z, ∀ v, AT n C u v→v∈Z∨v=b):=by
  classical
  revert hq
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl=>
    intro _
    refine ⟨∅, Or.inr rfl, by simp, by simp, ?_, ?_⟩
    · simp
    · simp
  | @head a c hs hrest ih=>
    intro ha
    have hac:=AU hb hs.1
    have hab:a < b:=hac.trans_le (AL hb hrest)
    have hc:n≤c:=ha.trans (Nat.le_of_lt hac)
    obtain ⟨Z, hcZ, hbZ, hoZ, hbound, hclosed⟩:=ih hc
    refine ⟨insert a Z, Or.inl (Finset.mem_insert_self _ _), ?_, ?_, ?_, ?_⟩
    · simp only [Finset.mem_insert, not_or]
      exact ⟨Ne.symm (Nat.ne_of_lt hab), hbZ⟩
    · simp only [Finset.mem_insert, not_or]
      exact ⟨Ne.symm hs.2.2, hoZ⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨ha, hab, hs.2.1⟩
      · exact hbound u hu
    · intro u hu v hv
      rcases Finset.mem_insert.mp hu with rfl | hu
      · have hvc:v=c:=JA hs.2.1 hv hs.1
        subst v
        rcases hcZ with hcZ | hcb
        · exact Or.inl (Finset.mem_insert_of_mem hcZ)
        · exact Or.inr hcb
      · rcases hclosed u hu v hv with hvZ | hvb
        · exact Or.inl (Finset.mem_insert_of_mem hvZ)
        · exact Or.inr hvb
end Ag
namespace Ag
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover
lemma EK {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (hmono:AndOrOnly C) (hbinary:∀ g∈C.gates, g.inputs.length=2)
    (I:Finset (Fin n)) (b:ℕ) (hbgate:n≤b)
    (hpos:∀ i∈I, wire n C i b=true)
    (hneg:∀ i∈I, wire n C i C.output=false)
    (hfresh:∀ i∈I, ∀ u, n≤u→u < b→
      2≤readsIn C (Finset.range C.gates.length) u→wire n C i u=false):
    ∃ Z:Finset ℕ,
      b∉Z∧C.output∉Z∧
      (∀ u∈Z, n≤u∧u < b∧readsIn C (Finset.range C.gates.length) u≤1)∧
      (∀ u∈Z, ∀ v, AT n C u v→v∈Z∨v=b)∧
      (∀ i∈I, ∃ q, AT n C i.val q∧(q∈Z∨q=b)):=by
  classical
  have hex:∀ i:Fin n, ∃ Z:Finset ℕ, i∈I→
      b∉Z∧C.output∉Z∧
      (∀ u∈Z, n≤u∧u < b∧readsIn C (Finset.range C.gates.length) u≤1)∧
      (∀ u∈Z, ∀ v, AT n C u v→v∈Z∨v=b)∧
      (∃ q, AT n C i.val q∧(q∈Z∨q=b)):=by
    intro i
    by_cases hi:i∈I
    · obtain ⟨q, hread, _, hchain, _⟩:=EJ hb hmono hbinary
        i b hbgate (hpos i hi) (hneg i hi) (hfresh i hi)
      have hqgate:n≤q:=by
        obtain ⟨j, hj, rfl, _⟩:=hread
        omega
      obtain ⟨Z, hq, hbZ, houtZ, hbound, hclosed⟩:=
        Dw hb hqgate hchain
      exact ⟨Z, fun _=>⟨hbZ, houtZ, hbound, hclosed, q, hread, hq⟩⟩
    · exact ⟨∅, fun h=>(hi h).elim⟩
  choose parts hparts using hex
  let Z:=I.biUnion parts
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbZ
    obtain ⟨i, hi, hbi⟩:=Finset.mem_biUnion.mp hbZ
    exact (hparts i hi).1 hbi
  · intro houtZ
    obtain ⟨i, hi, houti⟩:=Finset.mem_biUnion.mp houtZ
    exact (hparts i hi).2.1 houti
  · intro u huZ
    obtain ⟨i, hi, hui⟩:=Finset.mem_biUnion.mp huZ
    exact (hparts i hi).2.2.1 u hui
  · intro u huZ v huv
    obtain ⟨i, hi, hui⟩:=Finset.mem_biUnion.mp huZ
    rcases (hparts i hi).2.2.2.1 u hui v huv with hvi | hvb
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩)
    · exact Or.inr hvb
  · intro i hi
    obtain ⟨q, hread, hq⟩:=(hparts i hi).2.2.2.2
    refine ⟨q, hread, ?_⟩
    rcases hq with hqi | hqb
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hi, hqi⟩)
    · exact Or.inr hqb
end Ag
namespace Ah
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover Ag
def Gm (n:ℕ) (C:Circuit) (F Z:Finset ℕ):Circuit:=
  ⟨C.gates.mapIdx (fun j g=>
    if n+j∈F then ⟨.and, []⟩ else if n+j∈Z then ⟨.or, []⟩ else g), C.output⟩
lemma Gq (n:ℕ) (C:Circuit) (F Z:Finset ℕ):
    (Gm n C F Z).gates.length=C.gates.length:=by simp [Gm]
lemma Gp (n:ℕ) (C:Circuit) (F Z:Finset ℕ) (j:ℕ)
    (hj:j < C.gates.length):
    (Gm n C F Z).gates[j]'(by simpa [Gm] using hj)=
      if n+j∈F then ⟨.and, []⟩ else if n+j∈Z then ⟨.or, []⟩ else C.gates[j]:=by
  simp [Gm]
lemma Gt {n:ℕ} {C:Circuit} (hb:ReadsBack n C) (F Z:Finset ℕ):
    ReadsBack n (Gm n C F Z):=by
  intro j hj u hu
  have hjC:j < C.gates.length:=by simpa [Gm] using hj
  rw [EN _ _ hj, Gp n C F Z j hjC] at hu
  split_ifs at hu with hF hZ
  · simp at hu
  · simp at hu
  · exact hb j hjC u (by simpa only [EN C j hjC] using hu)
lemma Gr {n:ℕ} {C:Circuit}
    (hm:PEqualNP.MetaComplexity.Monotone2 C) (F Z:Finset ℕ):
    PEqualNP.MetaComplexity.Monotone2 (Gm n C F Z):=by
  intro g hg
  obtain ⟨j, hj, rfl⟩:=List.mem_iff_getElem.mp hg
  have hjC:j < C.gates.length:=by simpa [Gm] using hj
  rw [Gp n C F Z j hjC]
  split_ifs with hF hZ
  · simp
  · simp
  · exact hm _ (List.getElem_mem hjC)
lemma Kr (C:Circuit) (x:List Bool):
    (C.wires x).length=x.length+C.gates.length:=
  Ec C.gates x
def AI (n:ℕ) (C:Circuit) (F Z:Finset ℕ):Prop:=
  ∀ j, ∀ hj:j < C.gates.length, ∀ u∈C.gates[j].inputs,
    u∈Z→n+j∈Z∨n+j∈F
lemma Gs {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (F Z:Finset ℕ) (hc:AI n C F Z)
    (x:List Bool) (hx:x.length=n) (w:ℕ) (hw:w∉Z):
    ((Gm n C F Z).wires x).getD w false=
      ((Gm n C F ∅).wires x).getD w false:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    by_cases hraw:w < n
    · change ((Gm n C F Z).gates.foldl step x).getD w false=
        ((Gm n C F ∅).gates.foldl step x).getD w false
      rw [Eb _ _ _ (by omega), Eb _ _ _ (by omega)]
    · by_cases hlen:w < n+C.gates.length
      · let j:=w-n
        have hj:j < C.gates.length:=by dsimp [j]; omega
        have he:w=n+j:=by dsimp [j]; omega
        rw [he, EW n _ (Gt hb F Z) j (by simpa [Gm] using hj) x hx,
          EW n _ (Gt hb F ∅) j (by simpa [Gm] using hj) x hx,
          Gp n C F Z j hj, Gp n C F ∅ j hj]
        by_cases hF:n+j∈F
        · simp [hF, GateOp.eval]
        · have hZ:n+j∉Z:=he ▸ hw
          simp only [hF, hZ, Finset.notMem_empty, ite_false]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hul:u < w:=by
            rw [he]
            exact hb j hj u (by simpa only [EN C j hj] using hu)
          have huZ:u∉Z:=by
            intro huZ
            rcases hc j hj u hu huZ with hz | hf
            · exact hZ hz
            · exact hF hf
          exact ih u hul huZ
      · rw [List.getD_eq_default _ _ (by
          rw [Kr, Gq, hx]; omega),
          List.getD_eq_default _ _ (by
          rw [Kr, Gq, hx]; omega)]
lemma Go {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (F Z:Finset ℕ) (hc:AI n C F Z) (ho:C.output∉Z)
    (x:List Bool) (hx:x.length=n):
    (Gm n C F Z).eval x=(Gm n C F ∅).eval x:=
  Gs hb F Z hc x hx C.output ho
lemma Gu (n:ℕ) (C:Circuit) (F Z:Finset ℕ) (u:ℕ):
    readsIn (Gm n C F Z) (Finset.range C.gates.length) u≤
      readsIn C (Finset.range C.gates.length) u:=by
  apply Finset.sum_le_sum
  intro j hj
  have hjC:=Finset.mem_range.mp hj
  rw [EN _ j (by simpa [Gm] using hjC), EN C j hjC,
    Gp n C F Z j hjC]
  split_ifs <;> simp
lemma Gv (n:ℕ) (C:Circuit) (F Z:Finset ℕ) (u j:ℕ)
    (hj:j < C.gates.length) (hu:u∈C.gates[j].inputs)
    (hcut:n+j∈F∨n+j∈Z):
    readsIn (Gm n C F Z) (Finset.range C.gates.length) u <
      readsIn C (Finset.range C.gates.length) u:=by
  apply Finset.sum_lt_sum
  · intro k hk
    have hkC:=Finset.mem_range.mp hk
    rw [EN _ k (by simpa [Gm] using hkC), EN C k hkC,
      Gp n C F Z k hkC]
    split_ifs <;> simp
  · refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    rw [EN _ j (by simpa [Gm] using hj), EN C j hj,
      Gp n C F Z j hj]
    have hp:0 < C.gates[j].inputs.count u:=List.count_pos_iff.mpr hu
    rcases hcut with hF | hZ
    · simpa [hF] using hp
    · by_cases hF:n+j∈F <;> simpa [hF, hZ] using hp
end Ah
namespace Ag
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Ah
lemma EL {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (hmono:AndOrOnly C) (hbinary:∀ g∈C.gates, g.inputs.length=2)
    (I:Finset (Fin n)) (b:ℕ) (hbgate:n≤b)
    (hpos:∀ i∈I, wire n C i b=true)
    (hneg:∀ i∈I, wire n C i C.output=false)
    (hfresh:∀ i∈I, ∀ u, n≤u→u < b→
      2≤readsIn C (Finset.range C.gates.length) u→wire n C i u=false):
    ∃ (Z:Finset ℕ) (D:Circuit),
      D=Gm n C {b} Z∧
      D.gates.length=C.gates.length∧D.output=C.output∧
      Monotone2 D∧ReadsBack n D∧
      (∀ u, readsIn D (Finset.range D.gates.length) u≤
        readsIn C (Finset.range C.gates.length) u)∧
      (∀ i∈I, readsIn D (Finset.range D.gates.length) i.val <
          readsIn C (Finset.range C.gates.length) i.val∧
        (readsIn C (Finset.range C.gates.length) i.val≤2→
          readsIn D (Finset.range D.gates.length) i.val≤1))∧
      (∀ x:List Bool, x.length=n→
        D.eval x=(Gm n C {b} ∅).eval x)∧
      (∀ u, 2≤readsIn C (Finset.range C.gates.length) u→
        ∀ x:List Bool, x.length=n→
          (D.wires x).getD u false=((Gm n C {b} ∅).wires x).getD u false):=by
  classical
  obtain ⟨Z, hbZ, houtZ, hbound, hclosed, hremoved⟩:=
    EK hb hmono hbinary I b hbgate hpos hneg hfresh
  have hc:AI n C {b} Z:=by
    intro j hj u hu huZ
    rcases hclosed u huZ (n+j) ⟨j, hj, rfl, hu⟩ with hjZ | hjb
    · exact Or.inl hjZ
    · exact Or.inr (Finset.mem_singleton.mpr hjb)
  have hm:Monotone2 C:=by
    intro g hg
    exact ⟨hmono g hg, by rw [hbinary g hg]⟩
  let D:=Gm n C {b} Z
  have hlen:D.gates.length=C.gates.length:=Gq n C {b} Z
  have hstrict:∀ i∈I, readsIn D (Finset.range D.gates.length) i.val <
      readsIn C (Finset.range C.gates.length) i.val:=by
    intro i hi
    obtain ⟨q, hread, hq⟩:=hremoved i hi
    obtain ⟨j, hj, rfl, hu⟩:=hread
    rw [hlen]
    apply Gv n C {b} Z i.val j hj hu
    rcases hq with hjZ | hjb
    · exact Or.inr hjZ
    · exact Or.inl (Finset.mem_singleton.mpr hjb)
  refine ⟨Z, D, rfl, hlen, rfl, Gr hm {b} Z,
    Gt hb {b} Z, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [hlen]
    exact Gu n C {b} Z u
  · intro i hi
    have hs:=hstrict i hi
    exact ⟨hs, fun hr=>by omega⟩
  · intro x hx
    exact Go hb {b} Z hc houtZ x hx
  · intro u hu x hx
    have huZ:u∉Z:=by
      intro huZ
      have:=(hbound u huZ).2.2
      omega
    exact Gs hb {b} Z hc x hx u huZ
end Ag
namespace Ai
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Bb (x y:List Bool):Prop:=
  ∀ i, x.getD i false=true→y.getD i false=true
def run (gs:List Gate) (x:List Bool):List Bool:=
  gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) x
def Gw (gs:List Gate):Prop:=
  ∀ g∈gs, g.op=.and∨g.op=.or
def singleton {n:ℕ} (i:Fin n):Fin n→Bool:=
  fun j=>decide (j=i)
lemma Ke (x:List Bool):Bb x x:=by
  intro i hi
  exact hi
lemma Kd {x y:List Bool} {a b:Bool}
    (hab:a=true→b=true) (hxy:Bb x y):Bb (a::x) (b::y):=by
  intro i hi
  cases i with
  | zero=>exact hab hi
  | succ i=>exact hxy i hi
lemma Kc {x y:List Bool} (hlen:x.length=y.length)
    (hxy:Bb x y) {a b:Bool} (hab:a=true→b=true):
    Bb (x++[a]) (y++[b]):=by
  induction x generalizing y with
  | nil=>
    cases y with
    | nil=>exact Kd hab (Ke [])
    | cons c y=>simp at hlen
  | cons c x ih=>
    cases y with
    | nil=>simp at hlen
    | cons d y=>
      apply Kd (fun hc=>hxy 0 hc)
      apply ih (by simpa using hlen)
      intro i hi
      exact hxy (i+1) hi
lemma Fa {g:Gate} (hg:g.op=.and∨g.op=.or)
    {x y:List Bool} (hxy:Bb x y):
    g.op.eval (g.inputs.map fun i=>x.getD i false)=true→
    g.op.eval (g.inputs.map fun i=>y.getD i false)=true:=by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, List.all_eq_true]
    intro h i hi
    exact hxy i (h i hi)
  · simp only [hg, GateOp.eval, List.any_map, List.any_eq_true]
    rintro ⟨i, hi, hit⟩
    exact ⟨i, hi, hxy i hit⟩
lemma run_mono (gs:List Gate) (hgs:Gw gs) {x y:List Bool}
    (hlen:x.length=y.length) (hxy:Bb x y):
    Bb (run gs x) (run gs y):=by
  induction gs generalizing x y with
  | nil=>exact hxy
  | cons g gs ih=>
    change Bb (run gs (x++[_])) (run gs (y++[_]))
    apply ih
    · intro h hh
      exact hgs h (List.mem_cons_of_mem g hh)
    · simp [hlen]
    · exact Kc hlen hxy (Fa (hgs g (List.mem_cons_self ..)) hxy)
lemma GV {n:ℕ} {x y:Fin n→Bool}
    (hxy:∀ i, x i=true→y i=true):Bb (List.ofFn x) (List.ofFn y):=by
  intro i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
  split at hi <;> rename_i h
  · simp only [h, ↓reduceDIte, Option.getD_some]
    exact hxy ⟨i, h⟩ hi
  · simp at hi
end Ai
namespace Ai
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover Ag As
 def value {n:ℕ} (C:Circuit) (x:Fin n→Bool) (w:ℕ):Bool:=
  (C.wires (List.ofFn x)).getD w false
lemma JU {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (x y:Fin n→Bool) (hxy:∀ i, x i=true→y i=true) (w:ℕ):
    value C x w=true→value C y w=true:=
  run_mono C.gates hmono (by simp) (GV hxy) w
lemma JT {n:ℕ} (C:Circuit) (x:Fin n→Bool) (w:ℕ) (hw:w < n):
    value C x w=x ⟨w, hw⟩:=by
  unfold value
  change (C.gates.foldl Ag.step (List.ofFn x)).getD w false=_
  rw [Eb _ _ _ (by simpa only [List.length_ofFn] using hw)]
  simp [List.getD_eq_getElem?_getD, hw]
lemma JS {n:ℕ} (C:Circuit) (x:Fin n→Bool) (w:ℕ)
    (hw:n+C.gates.length≤w):value C x w=false:=by
  unfold value
  apply List.getD_eq_default
  rw [Kq, List.length_ofFn]
  exact hw
lemma JR {n:ℕ} (C:Circuit) (x:Fin n→Bool) (j:ℕ)
    (hj:j < C.gates.length):value C x (n+j)=
      C.gates[j].op.eval (C.gates[j].inputs.map fun a=>
        if a < n+j then value C x a else false):=by
  have he:=Aj.If C.gates (List.ofFn x) j hj
  simpa only [List.length_ofFn, Aj.run, Circuit.wires, value] using he
def AH (n:ℕ) (C:Circuit) (a b:ℕ):Prop:=
  ∃ j, ∃ hj:j < C.gates.length,
    b=n+j∧a < n+j∧a∈C.gates[j].inputs
lemma BK {n:ℕ} {C:Circuit} {a b:ℕ} (h:AH n C a b):a < b:=by
  obtain ⟨j, hj, rfl, ha, _⟩:=h
  exact ha
def JO (n:ℕ) (C:Circuit) (a:ℕ):Finset (Fin C.gates.length):=
  Finset.univ.filter fun j=>a < n+j.val∧a∈C.gates[j.val].inputs
lemma JP (n:ℕ) (C:Circuit) (a:ℕ):
    (JO n C a).card≤JI C n a:=by
  classical
  calc
    _=∑ j∈JO n C a, (1:ℕ):=by simp
    _≤∑ j∈JO n C a, JN C n j a:=by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨ha, hm⟩:=(Finset.mem_filter.mp hj).2
      apply List.count_pos_iff.mpr
      exact List.mem_filter.mpr ⟨hm, by simp [ha]⟩
    _≤∑ j:Fin C.gates.length, JN C n j a:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact Nat.zero_le _
    _=_:=rfl
lemma BL {n:ℕ} {C:Circuit} {a b c:ℕ}
    (hf:JI C n a≤1)
    (hb:AH n C a b) (hc:AH n C a c):b=c:=by
  obtain ⟨j, hj, rfl, haj, hmj⟩:=hb
  obtain ⟨k, hk, rfl, hak, hmk⟩:=hc
  have hcard:=(JP n C a).trans hf
  have hjmem:(⟨j, hj⟩:Fin C.gates.length)∈JO n C a:=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, haj, hmj⟩
  have hkmem:(⟨k, hk⟩:Fin C.gates.length)∈JO n C a:=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hak, hmk⟩
  have he:=Finset.card_le_one.mp hcard _ hjmem _ hkmem
  have hv:=congrArg Fin.val he
  change j=k at hv
  omega
lemma BN {n:ℕ} {C:Circuit} (x y:Fin n→Bool) (i:Fin n)
    (hxy:∀ k, k≠i→x k=y k) (w:ℕ)
    (hw:value C x w≠value C y w):
    Relation.ReflTransGen (fun a b=>AH n C a b∧value C x b≠value C y b)
      i.val w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    by_cases hraw:w < n
    · rw [JT C x w hraw, JT C y w hraw] at hw
      have he:(⟨w, hraw⟩:Fin n)=i:=by
        by_contra hn
        exact hw (hxy _ hn)
      have hv:=congrArg Fin.val he
      change w=i.val at hv
      rw [hv]
    · by_cases hlen:w < n+C.gates.length
      · let j:=w-n
        have hj:j < C.gates.length:=by dsimp [j]; omega
        have hwj:w=n+j:=by dsimp [j]; omega
        have hd:=hw
        rw [hwj, JR C x j hj, JR C y j hj] at hd
        have hex:∃ a∈C.gates[j].inputs,
            a < n+j∧value C x a≠value C y a:=by
          by_contra hn
          apply hd
          congr 1
          apply List.map_congr_left
          intro a ha
          by_cases hlt:a < n+j
          · have he:value C x a=value C y a:=by
              by_contra hne
              exact hn ⟨a, ha, hlt, hne⟩
            simp only [hlt, ite_true, he]
          · simp only [hlt, ite_false]
        obtain ⟨a, ha, hlt, hdiff⟩:=hex
        exact (ih a (by omega) hdiff).tail ⟨⟨j, hj, hwj, hlt, ha⟩, hw⟩
      · exact (hw (by rw [JS C x w (by omega), JS C y w (by omega)])).elim
def AV {n:ℕ} (C:Circuit) (i:Fin n) (w:ℕ):Prop:=
  value C (fun _:Fin n=>false) w≠value C (singleton i) w
def AW {n:ℕ} (C:Circuit) (i:Fin n) (a b:ℕ):Prop:=
  AH n C a b∧AV C i a∧JI C n a≤1
def AJ (n:ℕ) (C:Circuit) (b a:ℕ):Prop:=
  b=a∨¬ Relation.ReflTransGen (fun u v=>AH n C u v∧v≠b) a C.output
lemma BM {n:ℕ} {C:Circuit} (i:Fin n)
    (hout:¬ AV C i C.output) {a b:ℕ}
    (hchain:Relation.ReflTransGen (AW C i) a b):
    AJ n C b a:=by
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl=>exact Or.inl rfl
  | @head a c hstep hrest ih=>
    by_cases hba:b=a
    · exact Or.inl hba
    · right
      intro hp
      rcases hp.cases_head with he | ⟨c', hs, hr⟩
      · apply hout
        rw [← he]
        exact hstep.2.1
      · have hcc:=BL hstep.2.2 hstep.1 hs.1
        subst c'
        rcases ih with rfl | hi
        · exact hs.2 rfl
        · exact hi hr
lemma HG {α:Type} {R S:α→α→Prop}
    (hRS:∀ a b, R a b→S a b) {a b:α} (h:Relation.ReflTransGen R a b):
    Relation.ReflTransGen S a b:=by
  induction h with
  | refl=>exact .refl
  | tail h hs ih=>exact ih.tail (hRS _ _ hs)
lemma Dm {n:ℕ} {C:Circuit} (x y:Fin n→Bool) (i:Fin n)
    (hxy:∀ k, k≠i→x k=y k) (b:ℕ)
    (hdom:AJ n C b i.val) (hb:value C x b=value C y b):
    value C x C.output=value C y C.output:=by
  by_contra hout
  rcases hdom with rfl | hd
  · rw [JT C x i.val i.isLt, JT C y i.val i.isLt] at hb
    have he:x=y:=by
      funext k
      by_cases hk:k=i
      · subst k
        exact hb
      · exact hxy k hk
    exact hout (by rw [he])
  · apply hd
    have hp:=BN x y i hxy C.output hout
    exact HG
      (fun a c h=>⟨h.1, fun he=>h.2 (by rw [he]; exact hb)⟩) hp
end Ai
namespace Ai
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover Ag As
lemma JV {n:ℕ} (C:Circuit) (i:Fin n) (w:ℕ):
    value C (singleton i) w=wire n C i w:=rfl
lemma Iu {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (i:Fin n) (w:ℕ) (h:AV C i w):wire n C i w=true:=by
  have hm:=JU hmono (fun _:Fin n=>false) (singleton i)
    (by intro k hk; contradiction) w
  have hbool:∀ a b:Bool, (a=true→b=true)→a≠b→b=true:=by decide
  exact hbool _ _ hm h
lemma HJ {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (i:Fin n) (hneg:wire n C i C.output=false):¬ AV C i C.output:=by
  intro h
  have hp:=Iu hmono i C.output h
  rw [hneg] at hp
  contradiction
lemma Cg {n:ℕ} {C:Circuit} {i:Fin n} {a b:ℕ}
    (h:Relation.ReflTransGen (fun a b=>AH n C a b∧AV C i b) a b):
    a≤b:=by
  induction h with
  | refl=>exact le_rfl
  | tail h hs ih=>exact ih.trans (Nat.le_of_lt (BK hs.1))
lemma Ch {n:ℕ} {C:Circuit} {i:Fin n} {a b:ℕ}
    (h:Relation.ReflTransGen (fun a b=>AH n C a b∧AV C i b) a b)
    (hsmall:∀ u, u < b→AV C i u→JI C n u≤1)
    (ha:AV C i a):Relation.ReflTransGen (AW C i) a b:=by
  revert ha
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl=>intro _; exact .refl
  | @head a c hs hrest ih=>
    intro ha
    have hab:a < b:=(BK hs.1).trans_le (Cg hrest)
    exact Relation.ReflTransGen.head ⟨hs.1, ha, hsmall a hab ha⟩ (ih hs.2)
lemma Ir {n:ℕ} {C:Circuit} (i:Fin n) (b:ℕ)
    (hs:AV C i b)
    (hsmall:∀ u, u < b→AV C i u→JI C n u≤1):
    Relation.ReflTransGen (AW C i) i.val b:=by
  have hpath:=BN (fun _:Fin n=>false) (singleton i) i
    (by intro k hk; simp [singleton, hk]) b hs
  apply Ch hpath hsmall
  unfold AV
  rw [JT C (fun _:Fin n=>false) i.val i.isLt,
    JT C (singleton i) i.val i.isLt]
  simp [singleton]
def FL {n:ℕ} (X:Finset (Fin n)) (C:Circuit) (w:ℕ):Finset (Fin n):=
  X.filter fun i=>wire n C i w=true
lemma Dl {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (X:Finset (Fin n)) (i:Fin n) (b:ℕ)
    (hdom:AJ n C b i.val)
    (hneg:∀ j∈X, wire n C j C.output=false)
    (hpair:∀ j∈X, j≠i→value C (pairInput i j) C.output=true):
    FL X C b⊆{i}:=by
  intro j hj
  obtain ⟨hjX, hjtrue⟩:=Finset.mem_filter.mp hj
  apply Finset.mem_singleton.mpr
  by_contra hji
  have hp:value C (pairInput i j) b=true:=
    JU hmono (singleton j) (pairInput i j)
      (by
        intro k hk
        simp only [singleton, decide_eq_true_eq] at hk
        simp [pairInput, hk]) b hjtrue
  have hagree:∀ k:Fin n, k≠i→singleton j k=pairInput i j k:=by
    intro k hk
    simp [singleton, pairInput, hk]
  have he:=Dm (singleton j) (pairInput i j) i hagree b hdom
    (by rw [JV, hjtrue, hp])
  rw [JV, hneg j hjX, hpair j hjX hji] at he
  contradiction
lemma Bu {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (X:Finset (Fin n)) (i:Fin n) (hiX:i∈X) (b:ℕ)
    (hs:AV C i b)
    (hsmall:∀ u, u < b→AV C i u→JI C n u≤1)
    (hneg:∀ j∈X, wire n C j C.output=false)
    (hpair:∀ j∈X, j≠i→value C (pairInput i j) C.output=true):
    FL X C b={i}:=by
  have hdom:=BM i (HJ hmono i (hneg i hiX))
    (Ir i b hs hsmall)
  apply Finset.Subset.antisymm (Dl hmono X i b hdom hneg hpair)
  apply Finset.singleton_subset_iff.mpr
  exact Finset.mem_filter.mpr ⟨hiX, Iu hmono i b hs⟩
lemma DZ {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (X:Finset (Fin n)) (i:Fin n) (hiX:i∈X) (B:Finset ℕ) (b:ℕ)
    (hs:AV C i b)
    (hfirst:∀ u∈B, u < b→¬ AV C i u)
    (hraw:JI C n i.val≤1)
    (houtside:∀ u, n≤u→u∉B→JI C n u≤1)
    (hneg:∀ j∈X, wire n C j C.output=false)
    (hpair:∀ j∈X, j≠i→value C (pairInput i j) C.output=true):
    FL X C b={i}:=by
  apply Bu hmono X i hiX b hs _ hneg hpair
  intro u hub hus
  by_cases hu:u < n
  · have he:=(Kh C i u hu).mp (Iu hmono i u hus)
    rw [he]
    exact hraw
  · by_cases huB:u∈B
    · exact (hfirst u huB hub hus).elim
    · exact houtside u (by omega) huB
lemma Bt {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (X:Finset (Fin n)) (b:ℕ) (hzero:value C (fun _:Fin n=>false) b=true):
    FL X C b=X:=by
  apply Finset.filter_eq_self.mpr
  intro i _
  exact JU hmono (fun _:Fin n=>false) (singleton i)
    (by intro k hk; contradiction) b hzero
lemma Hw {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (X:Finset (Fin n)) (i:Fin n) (b:ℕ)
    (hi:i∈FL X C b) (hproper:FL X C b≠X):
    AV C i b:=by
  have hiTrue:value C (singleton i) b=true:=(Finset.mem_filter.mp hi).2
  have hzero:value C (fun _:Fin n=>false) b=false:=by
    cases hz:value C (fun _:Fin n=>false) b with
    | false=>rfl
    | true=>exact (hproper (Bt hmono X b hz)).elim
  unfold AV
  rw [hzero, hiTrue]
  decide
lemma DY {n:ℕ} {C:Circuit} (hmono:AndOrOnly C)
    (X:Finset (Fin n)) (hX:2≤X.card) (i:Fin n) (hiX:i∈X)
    (B:Finset ℕ) (b:ℕ) (hbB:b∈B)
    (hi:i∈FL X C b) (hproper:FL X C b≠X)
    (hfirst:∀ a∈B, a < b→i∈FL X C a→FL X C a=X)
    (hraw:JI C n i.val≤1)
    (houtside:∀ u, n≤u→u∉B→JI C n u≤1)
    (hneg:∀ j∈X, wire n C j C.output=false)
    (hpair:∀ j∈X, j≠i→value C (pairInput i j) C.output=true):
    FL X C b={i}:=by
  classical
  have hs:=Hw hmono X i b hi hproper
  have hex:∃ a, a∈B∧AV C i a:=⟨b, hbB, hs⟩
  obtain ⟨hcB, hcs⟩:=Nat.find_spec hex
  have hcpure:=DZ hmono X i hiX B (Nat.find hex) hcs
    (by
      intro u hu huc hus
      exact Nat.find_min hex huc ⟨hu, hus⟩)
    hraw houtside hneg hpair
  have hcle:Nat.find hex≤b:=Nat.find_min' hex ⟨hbB, hs⟩
  have hceq:Nat.find hex=b:=by
    by_contra hne
    have hclt:Nat.find hex < b:=by omega
    have hfull:=hfirst (Nat.find hex) hcB hclt (by rw [hcpure]; simp)
    have hcard:X.card=1:=by rw [← hfull, hcpure]; simp
    omega
  simpa only [hceq] using hcpure
end Ai
namespace Ah
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover Ag
lemma Et {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (F:Finset ℕ) (x:List Bool) (hx:x.length=n)
    (hF:∀ b∈F, (C.wires x).getD b false=true) (w:ℕ):
    ((Gm n C F ∅).wires x).getD w false=(C.wires x).getD w false:=by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
    by_cases hraw:w < n
    · change ((Gm n C F ∅).gates.foldl step x).getD w false=
        (C.gates.foldl step x).getD w false
      rw [Eb _ _ _ (by omega), Eb _ _ _ (by omega)]
    · by_cases hlen:w < n+C.gates.length
      · let j:=w-n
        have hj:j < C.gates.length:=by dsimp [j]; omega
        have he:w=n+j:=by dsimp [j]; omega
        by_cases hwF:w∈F
        · rw [he, EW n _ (Gt hb F ∅) j
            (by simpa [Gm] using hj) x hx, Gp n C F ∅ j hj]
          have hh:n+j∈F:=he ▸ hwF
          rw [if_pos hh]
          simpa [GateOp.eval, ← he] using (hF w hwF).symm
        · rw [he, EW n _ (Gt hb F ∅) j
            (by simpa [Gm] using hj) x hx, Gp n C F ∅ j hj,
            EW n C hb j hj x hx]
          have hh:n+j∉F:=he ▸ hwF
          simp only [hh, Finset.notMem_empty, ite_false]
          congr 1
          apply List.map_congr_left
          intro u hu
          exact ih u (by rw [he]; exact hb j hj u (by
            simpa only [EN C j hj] using hu))
      · rw [List.getD_eq_default _ _ (by
          rw [Kr, Gq, hx]; omega),
          List.getD_eq_default _ _ (by rw [Kr, hx]; omega)]
lemma Es {n:ℕ} {C:Circuit} (hb:ReadsBack n C)
    (F:Finset ℕ) (x:List Bool) (hx:x.length=n)
    (hF:∀ b∈F, (C.wires x).getD b false=true):
    (Gm n C F ∅).eval x=C.eval x:=
  Et hb F x hx hF C.output
end Ah
namespace Ag
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover As
lemma JJ {n:ℕ} {C:Circuit} (hb:ReadsBack n C) (w:ℕ):
    JI C n w=readsIn C (Finset.range C.gates.length) w:=by
  unfold JI readsIn
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro g _
  rw [EN C g.val g.isLt]
  unfold JN
  congr 1
  apply List.filter_eq_self.mpr
  intro a ha
  apply decide_eq_true
  apply hb g.val g.isLt a
  simpa only [EN C g.val g.isLt] using ha
end Ag
namespace Ah
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover Ag
lemma Gn {n:ℕ} {C:Circuit} (hm:AndOrOnly C) (F Z:Finset ℕ):
    AndOrOnly (Gm n C F Z):=by
  intro g hg
  obtain ⟨j, hj, rfl⟩:=List.mem_iff_getElem.mp hg
  have hjC:j < C.gates.length:=by simpa [Gm] using hj
  rw [Gp n C F Z j hjC]
  split_ifs with hF hZ
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact hm _ (List.getElem_mem hjC)
end Ah
namespace Ai
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover Ag Ah As
lemma GZ {n:ℕ} {C:Circuit}
    (hb:ReadsBack n C) (hmono:AndOrOnly C)
    (hbinary:∀ g∈C.gates, g.inputs.length=2)
    (X:Finset (Fin n)) (hX:2≤X.card) (i:Fin n) (hiX:i∈X)
    (B:Finset ℕ) (b:ℕ) (hbgate:n≤b)
    (hforce:∀ j∈X, wire n C j b=true)
    (hfresh:∀ u, n≤u→u < b→
      2≤readsIn C (Finset.range C.gates.length) u→wire n C i u=false)
    (hraw:readsIn C (Finset.range C.gates.length) i.val≤2)
    (hbranch:∀ a∈B, 2≤readsIn C (Finset.range C.gates.length) a)
    (houtside:∀ u, n≤u→u∉B→
      readsIn C (Finset.range C.gates.length) u≤1)
    (hneg:∀ j∈X, wire n C j C.output=false)
    (hpair:∀ j∈X, j≠i→value C (pairInput i j) C.output=true)
    (c:ℕ) (hcB:c∈B) (hic:i∈FL X C c)
    (hproper:FL X C c≠X)
    (hfirst:∀ a∈B, a < c→i∈FL X C a→FL X C a=X):
    FL X C c={i}:=by
  classical
  obtain ⟨Z, D, hD, hlen, hout, hmD, hbD, hreads, hdrop, heval, hvalues⟩:=
    EL hb hmono hbinary {i} b hbgate
      (by intro j hj; have he:=Finset.mem_singleton.mp hj; subst j; exact hforce i hiX)
      (by intro j hj; have he:=Finset.mem_singleton.mp hj; subst j; exact hneg i hiX)
      (by intro j hj; have he:=Finset.mem_singleton.mp hj; subst j; exact hfresh)
  have hmonoD:AndOrOnly D:=by
    rw [hD]
    exact Gn hmono {b} Z
  have hFs:∀ j∈X, ∀ w∈({b}:Finset ℕ),
      (C.wires (Ag.singleton j)).getD w false=true:=by
    intro j hj w hw
    have he:=Finset.mem_singleton.mp hw
    subst w
    exact hforce j hj
  have hBvalues:∀ a∈B, ∀ j∈X, wire n D j a=wire n C j a:=by
    intro a ha j hj
    unfold wire
    rw [hvalues a (hbranch a ha) _ (by simp [Ag.singleton])]
    exact Et hb {b} (Ag.singleton j)
      (by simp [Ag.singleton]) (hFs j hj) a
  have hBsupport:∀ a∈B, FL X D a=FL X C a:=by
    intro a ha
    unfold FL
    apply Finset.filter_congr
    intro j hj
    rw [hBvalues a ha j hj]
  have hnegD:∀ j∈X, wire n D j D.output=false:=by
    intro j hj
    change D.eval (Ag.singleton j)=false
    rw [heval _ (by simp [Ag.singleton])]
    rw [Es hb {b} _ (by simp [Ag.singleton]) (hFs j hj)]
    exact hneg j hj
  have hpairD:∀ j∈X, j≠i→value D (pairInput i j) D.output=true:=by
    intro j hj hji
    have hpb:value C (pairInput i j) b=true:=
      JU hmono (singleton i) (pairInput i j)
        (by
          intro k hk
          simp only [singleton, decide_eq_true_eq] at hk
          simp [pairInput, hk]) b (hforce i hiX)
    have hFp:∀ w∈({b}:Finset ℕ),
        (C.wires (List.ofFn (pairInput i j))).getD w false=true:=by
      intro w hw
      have he:=Finset.mem_singleton.mp hw
      subst w
      exact hpb
    change D.eval (List.ofFn (pairInput i j))=true
    rw [heval _ (by simp)]
    rw [Es hb {b} _ (by simp) hFp]
    exact hpair j hj hji
  have hrawD:JI D n i.val≤1:=by
    rw [JJ hbD]
    exact (hdrop i (Finset.mem_singleton_self i)).2 hraw
  have houtsideD:∀ u, n≤u→u∉B→JI D n u≤1:=by
    intro u hu huB
    rw [JJ hbD]
    exact (hreads u).trans (houtside u hu huB)
  have hresult:=DY hmonoD X hX i hiX B c hcB
    (by rw [hBsupport c hcB]; exact hic)
    (by rw [hBsupport c hcB]; exact hproper)
    (by
      intro a ha hac hia
      rw [hBsupport a ha] at hia ⊢
      exact hfirst a ha hac hia)
    hrawD houtsideD hnegD hpairD
  rwa [hBsupport c hcB] at hresult
end Ai
namespace Ai
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover Ag
lemma Ha {n:ℕ} {C:Circuit}
    (hb:ReadsBack n C) (hmono:AndOrOnly C)
    (hbinary:∀ g∈C.gates, g.inputs.length=2)
    (X:Finset (Fin n)) (hX:2≤X.card) (i:Fin n) (hiX:i∈X)
    (B:Finset ℕ) (hBgates:∀ a∈B, n≤a) (b:ℕ) (hbgate:n≤b)
    (hforce:∀ j∈X, wire n C j b=true)
    (hfresh:∀ u, n≤u→u < b→
      2≤readsIn C (Finset.range C.gates.length) u→wire n C i u=false)
    (hraw:readsIn C (Finset.range C.gates.length) i.val≤2)
    (hbranch:∀ a∈B, 2≤readsIn C (Finset.range C.gates.length) a)
    (houtside:∀ u, n≤u→u∉B→
      readsIn C (Finset.range C.gates.length) u≤1)
    (hneg:∀ j∈X, wire n C j C.output=false)
    (hpair:∀ j∈X, j≠i→value C (pairInput i j) C.output=true)
    (c:ℕ) (hcB:c∈B) (hic:i∈FL X C c)
    (hproper:FL X C c≠X)
    (hfirst:∀ a∈B, b < a→a < c→
      i∈FL X C a→FL X C a=X):
    b < c∧FL X C c={i}:=by
  have hfull:FL X C b=X:=Finset.filter_eq_self.mpr hforce
  have hbefore:∀ a∈B, a < b→i∉FL X C a:=by
    intro a ha hab hia
    have hp:=(Finset.mem_filter.mp hia).2
    rw [hfresh a (hBgates a ha) hab (hbranch a ha)] at hp
    contradiction
  have hbc:b < c:=by
    by_contra hn
    by_cases hcb:c < b
    · exact hbefore c hcB hcb hic
    · have he:c=b:=by omega
      exact hproper (he ▸ hfull)
  refine ⟨hbc, ?_⟩
  apply GZ hb hmono hbinary X hX i hiX B b hbgate
    hforce hfresh hraw hbranch houtside hneg hpair c hcB hic hproper
  intro a ha hac hia
  by_cases hab:a < b
  · exact (hbefore a ha hab hia).elim
  · by_cases he:a=b
    · simpa only [he] using hfull
    · exact hfirst a ha (by omega) hac hia
end Ai
namespace Ai
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover Ag
lemma Hb {n:ℕ} {C:Circuit}
    (hb:ReadsBack n C) (hmono:AndOrOnly C)
    (hbinary:∀ g∈C.gates, g.inputs.length=2)
    (X:Finset (Fin n)) (hX:2≤X.card) (i:Fin n) (hiX:i∈X)
    (B:Finset ℕ) (hBgates:∀ a∈B, n≤a) (b:ℕ) (hbgate:n≤b)
    (hforce:∀ j∈X, wire n C j b=true)
    (hfresh:∀ u, n≤u→u < b→
      2≤readsIn C (Finset.range C.gates.length) u→wire n C i u=false)
    (hraw:readsIn C (Finset.range C.gates.length) i.val≤2)
    (hbranch:∀ a∈B, 2≤readsIn C (Finset.range C.gates.length) a)
    (houtside:∀ u, n≤u→u∉B→
      readsIn C (Finset.range C.gates.length) u≤1)
    (hneg:∀ j∈X, wire n C j C.output=false)
    (hpair:∀ j∈X, j≠i→value C (pairInput i j) C.output=true)
    (c:ℕ) (hcB:c∈B) (hbc:b < c) (hic:i∈FL X C c)
    (hproper:FL X C c≠X):
    FL X C c={i}∨
      ∃ a∈B, b < a∧a < c∧FL X C a={i}:=by
  classical
  have hex:∃ a:ℕ, a∈B∧b < a∧i∈FL X C a∧
      FL X C a≠X:=⟨c, hcB, hbc, hic, hproper⟩
  obtain ⟨haB, hba, hia, haProper⟩:=Nat.find_spec hex
  have hac:Nat.find hex≤c:=Nat.find_min' hex ⟨hcB, hbc, hic, hproper⟩
  have hfirst:∀ d∈B, b < d→d < Nat.find hex→
      i∈FL X C d→FL X C d=X:=by
    intro d hd hbd hda hid
    by_contra hproperD
    exact Nat.find_min hex hda ⟨hd, hbd, hid, hproperD⟩
  have hpure:=(Ha hb hmono hbinary
    X hX i hiX B hBgates b hbgate hforce hfresh hraw hbranch houtside hneg hpair
    (Nat.find hex) haB hia haProper hfirst).2
  by_cases he:Nat.find hex=c
  · exact Or.inl (by simpa only [he] using hpure)
  · exact Or.inr ⟨Nat.find hex, haB, hba, by omega, hpure⟩
end Ai
namespace Ar
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Jf (n:ℕ) (hn:2≤n) (C:Circuit)
    (ht:IW n C) (i:Fin n):
    ∃ j:Fin C.gates.length, i.val∈C.gates[j.val].inputs:=by
  classical
  by_contra hnone
  have havoid:∀ g∈C.gates, i.val∉g.inputs:=by
    intro g hg hi
    obtain ⟨j, hj, hgj⟩:=List.mem_iff_getElem.mp hg
    exact hnone ⟨⟨j,hj⟩, by simpa [hgj] using hi⟩
  have hother:∃ k:Fin n, i≠k:=by
    let z:Fin n:=⟨0, by omega⟩
    by_cases hiz:i=z
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro heq
      have hv:=congrArg Fin.val heq
      simp [hiz, z] at hv
    · exact ⟨z, hiz⟩
  obtain ⟨k, hik⟩:=hother
  have heq:=Ak.HY C.gates i.val
    (List.ofFn (Ak.singleton k))
    (List.ofFn (Ak.pair i k)) (by simp)
    (Ak.IE i k) havoid C.output
    (Aw.Je n C ht i)
  change C.eval (List.ofFn (Ak.singleton k))=
    C.eval (List.ofFn (Ak.pair i k)) at heq
  have hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card):=by
    intro S
    simpa using ht (fun t=>decide (t∈S))
  have hsingle:C.eval (List.ofFn (Ak.singleton k))=false:=by
    change C.eval (List.ofFn (fun t:Fin n=>decide (t=k)))=false
    simpa using hcorrect ({k}:Finset (Fin n))
  have hpair:C.eval (List.ofFn (Ak.pair i k))=true:=by
    change C.eval (List.ofFn (fun t:Fin n=>decide (t=i∨t=k)))=true
    simpa [hik] using hcorrect ({i,k}:Finset (Fin n))
  rw [hsingle, hpair] at heq
  exact Bool.false_ne_true heq
lemma Gl (n:ℕ) (hn:2≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C)
    (hsecondary:∀ E:Circuit, Monotone2 E→circuitFun n E=circuitFun n C→
      E.size=C.size→IB n C≤IB n E)
    (i:Fin n):
    (∃ j k:Fin C.gates.length, j≠k∧
      i.val∈C.gates[j.val].inputs∧i.val∈C.gates[k.val].inputs)∨
    (∃ j:Fin C.gates.length, i.val∈C.gates[j.val].inputs∧
      C.gates[j.val].op=GateOp.and∧
      ∀ k:Fin C.gates.length, i.val∈C.gates[k.val].inputs→k=j):=by
  classical
  by_cases htwo:∃ j k:Fin C.gates.length, j≠k∧
      i.val∈C.gates[j.val].inputs∧i.val∈C.gates[k.val].inputs
  · exact Or.inl htwo
  obtain ⟨j, hread⟩:=Jf n hn C ht i
  have hunique:∀ k:Fin C.gates.length, i.val∈C.gates[k.val].inputs→k=j:=by
    intro k hk
    by_contra hkj
    exact htwo ⟨j,k,Ne.symm hkj,hread,hk⟩
  have huniqueNat:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j.val:=by
    intro t ht hreadt
    exact congrArg Fin.val (hunique ⟨t,ht⟩ hreadt)
  have hop:=Aw.Gf n hn C hmin ht
    hsecondary i j.val j.isLt hread huniqueNat
  exact Or.inr ⟨j,hread,hop,hunique⟩
lemma DD
    (n:ℕ) (hn:2≤n) (C:Circuit) (hC:Monotone2 C) (htC:IW n C):
    ∃ D:Circuit, circuitFun n D=circuitFun n C∧D.size≤C.size∧
      IsMinimalMonoCircuit n D∧IW n D∧
      (∀ E:Circuit, Monotone2 E→circuitFun n E=circuitFun n D→
        E.size=D.size→IB n D≤IB n E)∧
      (∀ (t:ℕ) (ht:t < D.gates.length),
        ∃ a b, D.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)∧
      ∀ i:Fin n,
        (∃ j k:Fin D.gates.length, j≠k∧
          i.val∈D.gates[j.val].inputs∧i.val∈D.gates[k.val].inputs)∨
        (∃ j:Fin D.gates.length, i.val∈D.gates[j.val].inputs∧
          D.gates[j.val].op=GateOp.and∧
          ∀ k:Fin D.gates.length, i.val∈D.gates[k.val].inputs→k=j):=by
  obtain ⟨D, hfun, hsize, hmin, htD, hsecondary, hshape, hreader⟩:=
    DC n hn C hC htC
  exact ⟨D,hfun,hsize,hmin,htD,hsecondary,hshape,
    Gl n hn D hmin htD hsecondary⟩
end Ar
namespace Ap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
def Hy (C:Circuit) (i:ℕ):Finset (Fin C.gates.length):=
  Finset.univ.filter (fun j=>i∈C.gates[j.val].inputs)
lemma FT (C:Circuit) (i:ℕ) (j:Fin C.gates.length):
    j∈Hy C i↔i∈C.gates[j.val].inputs:=by
  simp [Hy]
lemma HE {X:Type} (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)
    (i:Fin n) (src:X→List Bool)
    (hsrc:∀ x, (src x).length=n)
    (hfalse:∀ x, (src x).getD i.val false=false)
    (j:Fin C.gates.length) (hread:j∈Hy C i.val):
    (∃ b, ∀ x, (run C.gates (src x)).getD (n+j.val) false=b)∨
      ∃ w < n+j.val, ∀ x, (run C.gates (src x)).getD (n+j.val) false=
        (run C.gates (src x)).getD w false:=by
  have hmem:=(FT C i.val j).mp hread
  obtain ⟨a,b,hports,hdist,ha,hb⟩:=hshape j.val j.isLt
  have hmember:i.val=a∨i.val=b:=by simpa [hports] using hmem
  have hop:C.gates[j.val].op=GateOp.and∨C.gates[j.val].op=GateOp.or:=by
    have hg:=hC C.gates[j.val] (List.getElem_mem j.isLt)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  have hi:i.val < n+j.val:=by omega
  have hraw (x:X):(run C.gates (src x)).getD i.val false=false:=by
    rw [Ig C.gates (src x) i.val (by rw [hsrc]; exact i.isLt)]
    exact hfalse x
  rcases hop with hop | hop
  · left
    refine ⟨false, fun x=>?_⟩
    have he:=If C.gates (src x) j.val j.isLt
    rw [hsrc x] at he
    rw [he, hop, hports]
    rcases hmember with rfl | rfl <;> simp only [List.map_cons, List.map_nil, ha, hb, ite_true, GateOp.eval, List.all_cons, List.all_nil, id_eq, hraw, Bool.false_and, Bool.and_false, Bool.and_true]
  · right
    rcases hmember with hai | hbi
    · refine ⟨b, hb, fun x=>?_⟩
      have he:=If C.gates (src x) j.val j.isLt
      rw [hsrc x] at he
      rw [he, hop, hports, ← hai]
      simp only [List.map_cons, List.map_nil, hi, hb, ite_true, GateOp.eval, List.any_cons, List.any_nil, id_eq, hraw, Bool.false_or, Bool.or_false]
    · refine ⟨a, ha, fun x=>?_⟩
      have he:=If C.gates (src x) j.val j.isLt
      rw [hsrc x] at he
      rw [he, hop, hports, ← hbi]
      simp only [List.map_cons, List.map_nil, hi, ha, ite_true, GateOp.eval, List.any_cons, List.any_nil, id_eq, hraw, Bool.false_or, Bool.or_false]
lemma Di {X:Type} (n M:ℕ) (C:Circuit)
    (hC:Monotone2 C)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)
    (i:Fin n) (src tgt:X→List Bool)
    (hsrc:∀ x, (src x).length=n) (htgt:∀ x, (tgt x).length=M)
    (hfalse:∀ x, (src x).getD i.val false=false)
    (h0:∀ w < n,
      (∃ b, ∀ x, (src x).getD w false=b)∨
        ∃ t, t < M∧∀ x, (src x).getD w false=(tgt x).getD t false)
    (hne:¬∃ b, ∀ x, C.eval (src x)=b):
    ∃ D:Circuit, Monotone2 D∧D.size+(Hy C i.val).card≤C.size∧
      ∀ x, D.eval (tgt x)=C.eval (src x):=by
  let F:Finset ℕ:=(Hy C i.val).image Fin.val
  have hcard:F.card=(Hy C i.val).card:=
    Finset.card_image_of_injective _ Fin.val_injective
  have hF:∀ j∈F, j < C.gates.length∧
      ((∃ b, ∀ x, (run C.gates (src x)).getD (n+j) false=b)∨
        ∃ w < n+j, ∀ x, (run C.gates (src x)).getD (n+j) false=
          (run C.gates (src x)).getD w false):=by
    intro j hj
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hj
    exact ⟨k.isLt, HE n C hC hshape i src hsrc hfalse k hk⟩
  obtain ⟨D,hD,hsize,heval⟩:=Dq n M C src tgt hsrc htgt F hC h0 hne hF
  exact ⟨D,hD,by simpa only [hcard] using hsize,heval⟩
end Ap
namespace Ap
open PEqualNP.CircuitLowerBounds Aj
def HO {m:ℕ} (i:Fin (m+1)) (z:Fin m→Bool):Fin (m+1)→Bool:=
  Fin.insertNth i false z
lemma HP {m:ℕ} (i:Fin (m+1)) (z:Fin m→Bool):
    HO i z i=false:=by simp [HO]
lemma HR {m:ℕ} (i:Fin (m+1)) (z:Fin m→Bool) (k:Fin m):
    HO i z (i.succAbove k)=z k:=by simp [HO]
lemma Cp {m:ℕ} (i:Fin (m+1)) (z:Fin m→Bool):
    (List.ofFn (HO i z)).count true=(List.ofFn z).count true:=by
  classical
  rw [List.count_ofFn, List.count_ofFn]
  change (Finset.univ.filter (fun k=>HO i z k=true)).card=
    (Finset.univ.filter (fun k=>z k=true)).card
  symm
  apply Finset.card_bij (fun k _=>i.succAbove k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    simpa [HO] using hk
  · intro a ha b hb hab
    exact Fin.succAbove_right_injective hab
  · intro b hb
    have hbi:b≠i:=by
      intro h
      subst b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simpa [HO] using hb
    obtain ⟨a, ha⟩:=Fin.exists_succAbove_eq hbi
    refine ⟨a, ?_, ha⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    simpa [← ha, HO] using hb
lemma GT {m:ℕ} (z:Fin m→Bool) (k:Fin m):
    (List.ofFn z).getD k.val false=z k:=by
  simp [List.getD_eq_getElem?_getD]
lemma HU {m:ℕ} (i:Fin (m+1)):
    ∀ w < m+1,
      (∃ b, ∀ z:Fin m→Bool, (List.ofFn (HO i z)).getD w false=b)∨
      ∃ t, t < m∧∀ z:Fin m→Bool,
        (List.ofFn (HO i z)).getD w false=(List.ofFn z).getD t false:=by
  intro w hw
  rcases Fin.eq_self_or_eq_succAbove i ⟨w,hw⟩ with h | ⟨t,ht⟩
  · left
    refine ⟨false, ?_⟩
    intro z
    have hwval:w=i.val:=congrArg Fin.val h
    rw [hwval, GT, HP]
  · right
    refine ⟨t.val, t.isLt, ?_⟩
    intro z
    have hwval:w=(i.succAbove t).val:=congrArg Fin.val ht
    rw [hwval, GT, GT, HR]
lemma HW {m:ℕ} (i:Fin (m+1)) (z:Fin m→Bool):
    (List.ofFn (HO i z)).getD i.val false=false:=by
  rw [GT, HP]
lemma Jg {m:ℕ} (i:Fin (m+1)) (C:Circuit)
    (ht:IW (m+1) C) (z:Fin m→Bool):
    C.eval (List.ofFn (HO i z))=decide (2≤(List.ofFn z).count true):=by
  rw [ht, Cp]
lemma HV (m:ℕ) (hm:2≤ m) (i:Fin (m+1)) (C:Circuit)
    (ht:IW (m+1) C):
    ¬∃ b, ∀ z:Fin m→Bool, C.eval (List.ofFn (HO i z))=b:=by
  rintro ⟨b,hb⟩
  have hzero:=hb (fun _=>false)
  have hone:=hb (fun _=>true)
  rw [Jg i C ht] at hzero hone
  simp only [List.count_ofFn, Bool.false_eq_true, Finset.filter_false, Finset.card_empty,
    Nat.reduceLeDiff, decide_false] at hzero
  simp only [List.count_ofFn, Finset.filter_true, Finset.card_univ, Fintype.card_fin,
    hm, decide_true] at hone
  exact Bool.false_ne_true (hzero.trans hone.symm)
end Ap
namespace Ap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma GB (m:ℕ) (hm:2≤ m) (C:Circuit)
    (hC:Monotone2 C) (ht:IW (m+1) C)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < (m+1)+t∧b < (m+1)+t)
    (i:Fin (m+1)):
    ∃ D:Circuit, Monotone2 D∧D.size+(Hy C i.val).card≤C.size∧
      IW m D:=by
  obtain ⟨D,hD,hsize,heval⟩:=Di (m+1) m C hC hshape i
    (fun z=>List.ofFn (HO i z)) List.ofFn
    (fun _=>List.length_ofFn) (fun _=>List.length_ofFn)
    (HW i) (HU i) (HV m hm i C ht)
  exact ⟨D,hD,hsize,fun z=>(heval z).trans (Jg i C ht z)⟩
lemma GA (n:ℕ) (hn:3≤n) (C:Circuit)
    (hC:Monotone2 C) (ht:IW n C)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)
    (i:Fin n):
    ∃ D:Circuit, Monotone2 D∧D.size+(Hy C i.val).card≤C.size∧
      IW (n-1) D:=by
  cases n with
  | zero=>omega
  | succ m=>
      simpa using GB m (by omega) C hC ht hshape i
lemma Ge (n:ℕ) (hn:3≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C) (i:Fin n):
    ∃ D:Circuit, Monotone2 D∧D.size+(Hy C i.val).card≤C.size∧
      IW (n-1) D:=by
  exact GA n hn C hmin.1 ht
    (Ao.Gh n (by omega) C hmin ht) i
lemma Gg (n:ℕ) (hn:3≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C) (i:Fin n)
    (hthree:3≤(Hy C i.val).card):
    ∃ D:Circuit, Monotone2 D∧IW (n-1) D∧D.size+3≤C.size:=by
  obtain ⟨D,hD,hsize,htD⟩:=Ge n hn C hmin ht i
  exact ⟨D,hD,htD,by omega⟩
end Ap
namespace Am
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Ar
def Hx (C:Circuit) (i:ℕ):Finset (Fin C.gates.length):=
  Finset.univ.filter (fun j=>i∈C.gates[j.val].inputs)
def AO (n:ℕ) (C:Circuit):Prop:=
  ∀ (t:ℕ) (ht:t < C.gates.length),
    ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t
def AZ:Prop:=
  ∀ (n:ℕ), 3≤n→∀ C:Circuit,
    IsMinimalMonoCircuit n C→IW n C→AO n C→
    ∀ i:Fin n, 3≤(Hx C i.val).card→
      ∃ D:Circuit, Monotone2 D∧IW (n-1) D∧D.size+3≤C.size
def Ba:Prop:=
  ∀ (n:ℕ), 3≤n→∀ C:Circuit,
    IsMinimalMonoCircuit n C→IW n C→AO n C→
    ∀ (i:Fin n) (j:Fin C.gates.length),
      i.val∈C.gates[j.val].inputs→C.gates[j.val].op=GateOp.and→
      (∀ k:Fin C.gates.length, i.val∈C.gates[k.val].inputs→k=j)→
      ∃ D:Circuit, Monotone2 D∧IW (n-1) D∧D.size+3≤C.size
lemma Cl
    (hthree:AZ) (hone:Ba)
    (n₀:ℕ) (C₀:Circuit) (hC₀:Monotone2 C₀) (ht₀:IW n₀ C₀)
    (hbudget₀:C₀.size+8≤3*n₀):
    ∃ (n:ℕ) (C:Circuit), 3≤n∧n≤n₀∧
      IsMinimalMonoCircuit n C∧IW n C∧C.size+8≤3*n∧
      AO n C∧
      (∀ E:Circuit, Monotone2 E→circuitFun n E=circuitFun n C→
        E.size=C.size→IB n C≤IB n E)∧
      (∀ i:Fin n, (Hx C i.val).card=2)∧
      (∀ (m:ℕ), m < n→∀ E:Circuit, Monotone2 E→IW m E→
        3*m < E.size+8):=by
  classical
  let P:ℕ→Prop:=fun n=>
    ∃ C:Circuit, Monotone2 C∧IW n C∧C.size+8≤3*n
  have hex:∃ n, P n:=⟨n₀, C₀, hC₀, ht₀, hbudget₀⟩
  let n:=Nat.find hex
  obtain ⟨B, hB, htB, hbudgetB⟩:=Nat.find_spec hex
  have hn:3≤n:=by change B.size+8≤3*n at hbudgetB; omega
  have hnn₀:n≤n₀:=Nat.find_min' hex ⟨C₀, hC₀, ht₀, hbudget₀⟩
  have hleast:∀ (m:ℕ), m < n→∀ E:Circuit, Monotone2 E→IW m E→
      3*m < E.size+8:=by
    intro m hmn E hE htE
    by_contra hbudget
    have hP:P m:=⟨E,hE,htE,by omega⟩
    have hnm:n≤ m:=Nat.find_min' hex hP
    omega
  obtain ⟨C, hfun, hsize, hmin, htC, hsecondary, hshape, halternatives⟩:=
    DD n (by omega) B hB htB
  have hbudgetC:C.size+8≤3*n:=by omega
  have hnormalized:AO n C:=hshape
  have hnodelete:¬∃ D:Circuit,
      Monotone2 D∧IW (n-1) D∧D.size+3≤C.size:=by
    rintro ⟨D,hD,htD,hdrop⟩
    have hstrict:=hleast (n-1) (by omega) D hD htD
    omega
  have htwo:∀ i:Fin n, (Hx C i.val).card=2:=by
    intro i
    have hle:(Hx C i.val).card≤2:=by
      by_contra hnot
      exact hnodelete (hthree n hn C hmin htC hnormalized i (by omega))
    rcases halternatives i with ⟨j,k,hjk,hj,hk⟩ | ⟨j,hj,hop,hunique⟩
    · have hsubset:({j,k}:Finset (Fin C.gates.length))⊆Hx C i.val:=by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · simp [Hx,hj]
        · simp [Hx,hk]
      have hge:=Finset.card_le_card hsubset
      have hpair:({j,k}:Finset (Fin C.gates.length)).card=2:=by simp [hjk]
      omega
    · exact False.elim (hnodelete (hone n hn C hmin htC hnormalized i j hj hop hunique))
  exact ⟨n,C,hn,hnn₀,hmin,htC,hbudgetC,hnormalized,hsecondary,htwo,hleast⟩
end Am
namespace Am
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Ar
lemma IV:AZ:=by
  intro n hn C hmin ht hshape i hthree
  exact Ap.Gg n hn C hmin ht i hthree
end Am
namespace AA
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Am
open scoped BigOperators
lemma HD (n:ℕ) (C:Circuit) (hshape:AO n C)
    (i:ℕ):AE.JW C i=(Hx C i).card:=by
  classical
  unfold AE.JW Hx
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  change (C.gates[j.val].inputs.map fun w=>if w=i then 1 else 0).sum=
    if i∈C.gates[j.val].inputs then 1 else 0
  obtain ⟨a,b,hports,hab,ha,hb⟩:=hshape j.val j.isLt
  simp only [hports, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.mem_cons, List.not_mem_nil, or_false, add_zero]
  split_ifs <;> omega
lemma Gz (n:ℕ) (hn:2≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C)
    (hshape:AO n C)
    (hraw:∀ i:Fin n, (Hx C i.val).card=2):
    (∑ h, Af.credit C n h)+2*n=C.size+1:=by
  have hne:=Jb n hn C ht
  refine Af.Jj C n ?_ ?_ ?_ ?_ ?_
  · intro j
    change C.gates[j.val].inputs.length=2
    obtain ⟨a,b,hports,_,_,_⟩:=hshape j.val j.isLt
    simp [hports]
  · intro j w hw
    change w∈C.gates[j.val].inputs at hw
    obtain ⟨a,b,hports,_,ha,hb⟩:=hshape j.val j.isLt
    simp only [hports, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  · intro i
    rw [HD n C hshape]
    exact hraw i
  · have ho:=Al.Jd n hn C ht
    refine ⟨⟨C.output-n, by change _ < C.size; omega⟩, ?_⟩
    change C.output=n+(C.output-n)
    omega
  · intro h
    exact (Ay.Ga n C hmin hne h).symm
lemma Gi (n:ℕ) (hn:2≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C):
    C.output+1=n+C.size:=by
  have ho:=Al.Jd n hn C ht
  have hsize:0 < C.gates.length:=by change 0 < C.size; omega
  let j:Fin C.gates.length:=⟨C.gates.length-1, by omega⟩
  rcases Ay.Gb n C hmin
    (Jb n hn C ht) j with hout | ⟨k,hjk,_⟩
  · change C.output=n+(C.gates.length-1) at hout
    unfold Circuit.size
    omega
  · have hk:=k.isLt
    change C.gates.length-1 < k.val at hjk
    omega
lemma GD (n:ℕ) (hn:2≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C)
    (hshape:AO n C)
    (hraw:∀ i:Fin n, (Hx C i.val).card=2)
    (hbudget:C.size+8≤3*n):
    7≤n∧(∑ h, Af.credit C n h)≤n-7:=by
  have h:=Gz n hn C hmin ht hshape hraw
  omega
end AA
namespace As
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma run_true_mono (gs:List Gate) (x y:List Bool) (hl:x.length=y.length)
    (h:∀ i, x.getD i false=true→y.getD i false=true)
    (hg:∀ g∈gs, g.op=GateOp.and∨g.op=GateOp.or):
    ∀ i, (run gs x).getD i false=true→(run gs y).getD i false=true:=by
  induction gs using List.reverseRecOn with
  | nil=>intro i hi; exact h i hi
  | append_singleton gs g ih=>
    intro i hi
    have ih':=ih (fun g hg'=>hg g (by simp [hg']))
    have l1:=run_length gs x
    have l2:=run_length gs y
    rw [Il] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length+gs.length) with hlt | heq | hgt
    · rw [Fh _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1:i=(run gs x).length:=by omega
      have e2:i=(run gs y).length:=by omega
      have hi':g.op.eval (g.inputs.map fun i=>(run gs x).getD i false)=true:=by
        rw [← Ff (run gs x) (g.op.eval (g.inputs.map fun i=>(run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, Ff]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq=>ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩:=hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi
lemma Cb (C:Circuit) (hC:Monotone2 C)
    (lo hi:List Bool) (hlen:lo.length=hi.length)
    (hmono:∀ w, lo.getD w false=true→hi.getD w false=true):
    ∀ w, (C.wires lo).getD w false=true→(C.wires hi).getD w false=true:=by
  exact run_true_mono C.gates lo hi hlen hmono (fun g hg=>(hC g hg).1)
lemma BT (C:Circuit) (hC:Monotone2 C)
    (lo hi:List Bool) (hlen:lo.length=hi.length)
    (hmono:∀ w, lo.getD w false=true→hi.getD w false=true):
    C.eval lo=true→C.eval hi=true:=
  Cb C hC lo hi hlen hmono C.output
lemma BQ (C:Circuit) (hC:Monotone2 C)
    (lo hi:List Bool) (hlen:lo.length=hi.length)
    (hmono:∀ w, lo.getD w false=true→hi.getD w false=true)
    (hfalse:C.eval hi=false):C.eval lo=false:=by
  cases he:C.eval lo with
  | false=>rfl
  | true=>
    have ht:=BT C hC lo hi hlen hmono he
    rw [hfalse] at ht
    contradiction
lemma GU {n:ℕ} (x y:Fin n→Bool)
    (hxy:∀ i, x i=true→y i=true):
    ∀ w, (List.ofFn x).getD w false=true→(List.ofFn y).getD w false=true:=by
  intro w hw
  by_cases hwn:w < n
  · have hx:x ⟨w,hwn⟩=true:=by simpa [List.getD_eq_getElem?_getD, hwn] using hw
    simpa [List.getD_eq_getElem?_getD, hwn] using hxy ⟨w,hwn⟩ hx
  · simp [List.getD_eq_getElem?_getD, hwn] at hw
end As
namespace Ap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj As
lemma HS {m:ℕ} (i:Fin (m+1)) (x y:Fin m→Bool)
    (hxy:∀ t, x t=true→y t=true):
    ∀ t, HO i x t=true→HO i y t=true:=by
  intro t ht
  rcases Fin.eq_self_or_eq_succAbove i t with rfl | ⟨r,rfl⟩
  · simpa [HO] using ht
  · simpa only [HR] using hxy r (by simpa only [HR] using ht)
lemma HQ {m:ℕ} (i:Fin (m+1)) (t:Fin m):
    HO i (fun r=>decide (r=t))=(fun s=>decide (s=i.succAbove t)):=by
  funext s
  rcases Fin.eq_self_or_eq_succAbove i s with hsi | ⟨r,hr⟩
  · rw [hsi, HP]
    simp [Ne.symm (Fin.succAbove_ne i t)]
  · rw [hr, HR]
    simp only [Fin.succAbove_right_inj]
lemma HT {m:ℕ} (i:Fin (m+1)) (C:Circuit)
    (hC:Monotone2 C) (w:ℕ)
    (hcomp:∀ t:Fin m,
      (C.wires (List.ofFn (HO i (fun r=>decide (r=t))))).getD w false=true)
    (z:Fin m→Bool) (hz:∃ t, z t=true):
    (C.wires (List.ofFn (HO i z))).getD w false=true:=by
  obtain ⟨t,ht⟩:=hz
  apply Cb C hC
    (List.ofFn (HO i (fun r=>decide (r=t))))
    (List.ofFn (HO i z)) (by simp) _ w (hcomp t)
  apply GU
  apply HS
  intro r hr
  have hrt:r=t:=of_decide_eq_true hr
  simpa only [hrt] using ht
lemma Ep {m:ℕ} (i:Fin (m+1)) (C:Circuit)
    (hC:Monotone2 C) (k:ℕ)
    (hcomp:∀ t:Fin m,
      (C.wires (List.ofFn (HO i (fun r=>decide (r=t))))).getD ((m+1)+k) false=true)
    (z:Fin m→Bool) (hz:∃ t, z t=true):
    (Ee C {k}).eval (List.ofFn (HO i z))=
      C.eval (List.ofFn (HO i z)):=by
  apply Ef
  intro j hj hjbound
  have hjk:j=k:=by simpa only [Finset.mem_singleton] using hj
  subst j
  simpa only [List.length_ofFn] using
    HT i C hC ((m+1)+k) hcomp z hz
lemma Eq (m:ℕ) (hm:2≤ m)
    (i:Fin (m+1)) (C:Circuit) (hC:Monotone2 C) (ht:IW (m+1) C)
    (k:ℕ)
    (hcomp:∀ t:Fin m,
      (C.wires (List.ofFn (HO i (fun r=>decide (r=t))))).getD ((m+1)+k) false=true):
    ∀ z:Fin m→Bool,
      (Ee C {k}).eval (List.ofFn (HO i z))=
        decide (2≤(List.ofFn z).count true):=by
  intro z
  by_cases hz:∃ t, z t=true
  · exact (Ep i C hC k hcomp z hz).trans
      (Jg i C ht z)
  · have hzfalse:z=(fun _=>false):=by
      funext t
      cases ht:z t with
      | false=>rfl
      | true=>exact False.elim (hz ⟨t,ht⟩)
    subst z
    let t:Fin m:=⟨0,by omega⟩
    let s:Fin m→Bool:=fun r=>decide (r=t)
    have hs:(List.ofFn s).count true=1:=by
      rw [List.count_ofFn]
      change (Finset.univ.filter (fun r:Fin m=>s r=true)).card=1
      have he:(Finset.univ.filter (fun r:Fin m=>s r=true))={t}:=by
        ext r
        simp [s]
      rw [he, Finset.card_singleton]
    have hp:=Ep i C hC k hcomp s ⟨t,by simp [s]⟩
    have hsfalse:(Ee C {k}).eval (List.ofFn (HO i s))=false:=by
      rw [hp, Jg i C ht s, hs]
      rfl
    have hzero:(Ee C {k}).eval (List.ofFn (HO i (fun _=>false)))=false:=by
      apply BQ (Ee C {k}) (Ek C {k} hC)
        (List.ofFn (HO i (fun _=>false)))
        (List.ofFn (HO i s)) (by simp) _ hsfalse
      apply GU
      apply HS
      intro r hr
      contradiction
    rw [hzero, List.count_ofFn]
    simp
end Ap
namespace Au
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Bn {X:Type} (n:ℕ) (C:Circuit)
    (src:X→List Bool) (hsrc:∀ x, (src x).length=n)
    (j:ℕ) (hj:j < C.gates.length) (a b:ℕ)
    (ha:a < n+j) (hb:b < n+j)
    (hports:C.gates[j].inputs=[a,b]∨C.gates[j].inputs=[b,a])
    (hop:C.gates[j].op=GateOp.and)
    (hfalse:∀ x, (run C.gates (src x)).getD a false=false):
    ∀ x, (run C.gates (src x)).getD (n+j) false=false:=by
  intro x
  have he:=If C.gates (src x) j hj
  rw [hsrc x] at he
  rw [he, hop]
  rcases hports with hp | hp <;> rw [hp] <;>
    simp only [List.map_cons, List.map_nil, ha, hb, ite_true, GateOp.eval,
      List.all_cons, List.all_nil, id_eq, hfalse, Bool.false_and, Bool.and_false, Bool.and_true]
lemma Bw {X:Type} (n:ℕ) (C:Circuit)
    (hC:Monotone2 C) (src:X→List Bool) (hsrc:∀ x, (src x).length=n)
    (j:ℕ) (hj:j < C.gates.length) (a b:ℕ)
    (ha:a < n+j) (hb:b < n+j)
    (hports:C.gates[j].inputs=[a,b]∨C.gates[j].inputs=[b,a])
    (hfalse:∀ x, (run C.gates (src x)).getD a false=false):
    (∃ c, ∀ x, (run C.gates (src x)).getD (n+j) false=c)∨
      ∃ w < n+j, ∀ x, (run C.gates (src x)).getD (n+j) false=
        (run C.gates (src x)).getD w false:=by
  have hop:C.gates[j].op=GateOp.and∨C.gates[j].op=GateOp.or:=by
    have hg:=hC C.gates[j] (List.getElem_mem hj)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  rcases hop with hop | hop
  · exact Or.inl ⟨false, Bn n C src hsrc j hj a b ha hb hports hop hfalse⟩
  · right
    refine ⟨b,hb,fun x=>?_⟩
    have he:=If C.gates (src x) j hj
    rw [hsrc x] at he
    rw [he, hop]
    rcases hports with hp | hp <;> rw [hp] <;>
      simp only [List.map_cons, List.map_nil, ha, hb, ite_true, GateOp.eval,
        List.any_cons, List.any_nil, id_eq, hfalse, Bool.false_or, Bool.or_false]
lemma IU {X:Type} (n M:ℕ) (C:Circuit)
    (hC:Monotone2 C) (src tgt:X→List Bool)
    (hsrc:∀ x, (src x).length=n) (htgt:∀ x, (tgt x).length=M)
    (h0:∀ w < n,
      (∃ b, ∀ x, (src x).getD w false=b)∨
        ∃ t, t < M∧∀ x, (src x).getD w false=(tgt x).getD t false)
    (hne:¬∃ b, ∀ x, C.eval (src x)=b)
    (k j t:ℕ) (hkj:k < j) (hjt:j < t) (ht:t < C.gates.length)
    (htruek:∀ x, (run C.gates (src x)).getD (n+k) false=true)
    (hfalsej:∀ x, (run C.gates (src x)).getD (n+j) false=false)
    (b:ℕ) (hb:b < n+t)
    (hports:C.gates[t].inputs=[n+j,b]∨C.gates[t].inputs=[b,n+j]):
    ∃ D:Circuit, Monotone2 D∧D.size+3≤C.size∧
      ∀ x, D.eval (tgt x)=C.eval (src x):=by
  let F:Finset ℕ:={k,j,t}
  have hcard:F.card=3:=by
    simp [F, Nat.ne_of_lt hkj, Nat.ne_of_lt hjt, Nat.ne_of_lt (lt_trans hkj hjt)]
  have hF:∀ q∈F, q < C.gates.length∧
      ((∃ c, ∀ x, (run C.gates (src x)).getD (n+q) false=c)∨
        ∃ w < n+q, ∀ x, (run C.gates (src x)).getD (n+q) false=
          (run C.gates (src x)).getD w false):=by
    intro q hq
    have hmem:q=k∨q=j∨q=t:=by simpa [F] using hq
    rcases hmem with hq | hq | hq
    · subst q
      exact ⟨by omega, Or.inl ⟨true,htruek⟩⟩
    · subst q
      exact ⟨by omega, Or.inl ⟨false,hfalsej⟩⟩
    · subst q
      exact ⟨ht,Bw n C hC src hsrc t ht (n+j) b
        (by omega) hb hports hfalsej⟩
  obtain ⟨D,hD,hsize,heval⟩:=Dq n M C src tgt hsrc htgt F hC h0 hne hF
  exact ⟨D,hD,by simpa only [hcard] using hsize,heval⟩
end Au
namespace Au
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Ap As
lemma Er (m:ℕ) (hm:2≤ m) (C:Circuit)
    (hC:Monotone2 C) (htC:IW (m+1) C)
    (hshape:∀ (q:ℕ) (hq:q < C.gates.length),
      ∃ a b, C.gates[q].inputs=[a,b]∧a≠b∧a < (m+1)+q∧b < (m+1)+q)
    (i:Fin (m+1)) (k j t:Fin C.gates.length)
    (hkj:k.val < j.val) (hjt:j.val < t.val)
    (hopj:C.gates[j.val].op=GateOp.and)
    (hportsj:C.gates[j.val].inputs=[i.val,(m+1)+k.val]∨
      C.gates[j.val].inputs=[(m+1)+k.val,i.val])
    (hcomp:∀ v:Fin m,
      (C.wires (List.ofFn (HO i (fun r=>decide (r=v))))).getD ((m+1)+k.val) false=true)
    (hreadt:(m+1)+j.val∈C.gates[t.val].inputs):
    ∃ D:Circuit, Monotone2 D∧IW m D∧D.size+3≤C.size:=by
  let E:=Ee C {k.val}
  let src:(Fin m→Bool)→List Bool:=fun z=>List.ofFn (HO i z)
  have hE:Monotone2 E:=Ek C {k.val} hC
  have hsrc:∀ z, (src z).length=m+1:=by intro z; simp [src]
  have hlen:E.gates.length=C.gates.length:=Ej C {k.val}
  have hjE:j.val < E.gates.length:=by rw [hlen]; exact j.isLt
  have htE:t.val < E.gates.length:=by rw [hlen]; exact t.isLt
  have hgatej:E.gates[j.val]=C.gates[j.val]:=by
    rw [Eg C {k.val} j.val j.isLt]
    simp only [Finset.mem_singleton, Nat.ne_of_gt hkj, ite_false]
  have hgatet:E.gates[t.val]=C.gates[t.val]:=by
    rw [Eg C {k.val} t.val t.isLt]
    simp only [Finset.mem_singleton, Nat.ne_of_gt (lt_trans hkj hjt), ite_false]
  have htruek:∀ z, (run E.gates (src z)).getD ((m+1)+k.val) false=true:=by
    intro z
    exact Ei (m+1) C {k.val} k (by simp) (src z) (hsrc z)
  have hraw:∀ z, (run E.gates (src z)).getD i.val false=false:=by
    intro z
    rw [Ig E.gates (src z) i.val (by rw [hsrc]; exact i.isLt)]
    exact HW i z
  have hfalsej:∀ z, (run E.gates (src z)).getD ((m+1)+j.val) false=false:=
    Bn (m+1) E src hsrc j.val hjE i.val ((m+1)+k.val)
      (by omega) (by omega) (by simpa only [hgatej] using hportsj)
      (by simpa only [hgatej] using hopj) hraw
  obtain ⟨a,b,hports,hdist,ha,hb⟩:=hshape t.val t.isLt
  have hmem:(m+1)+j.val=a∨(m+1)+j.val=b:=by simpa [hports] using hreadt
  obtain ⟨q,hq,hportst⟩:∃ q, q < (m+1)+t.val∧
      (E.gates[t.val].inputs=[(m+1)+j.val,q]∨
        E.gates[t.val].inputs=[q,(m+1)+j.val]):=by
    rw [hgatet]
    rcases hmem with hja | hjb
    · exact ⟨b,hb,Or.inl (by simpa [hja] using hports)⟩
    · exact ⟨a,ha,Or.inr (by simpa [hjb] using hports)⟩
  have htRestricted:∀ z:Fin m→Bool,
      E.eval (src z)=decide (2≤(List.ofFn z).count true):=
    Eq m hm i C hC htC k.val hcomp
  have hne:¬∃ b, ∀ z:Fin m→Bool, E.eval (src z)=b:=by
    rintro ⟨b,hb⟩
    have hzero:=htRestricted (fun _=>false)
    have hone:=htRestricted (fun _=>true)
    rw [hb] at hzero hone
    simp [List.ofFn_const, List.count_replicate] at hzero
    simp [List.ofFn_const, List.count_replicate, hm] at hone
    exact Bool.false_ne_true (hzero.symm.trans hone)
  obtain ⟨D,hD,hsize,heval⟩:=IU (m+1) m E hE src List.ofFn
    hsrc (fun _=>List.length_ofFn) (HU i) hne
    k.val j.val t.val hkj hjt htE htruek hfalsej q hq hportst
  refine ⟨D,hD,fun z=>(heval z).trans (htRestricted z),?_⟩
  simpa only [Circuit.size, hlen] using hsize
lemma IS (m:ℕ) (hm:2≤ m) (C:Circuit)
    (hC:Monotone2 C) (htC:IW (m+1) C)
    (hshape:∀ (q:ℕ) (hq:q < C.gates.length),
      ∃ a b, C.gates[q].inputs=[a,b]∧a≠b∧a < (m+1)+q∧b < (m+1)+q)
    (i:Fin (m+1)) (k j t:Fin C.gates.length)
    (hkj:k.val < j.val) (hjt:j.val < t.val)
    (hopj:C.gates[j.val].op=GateOp.and)
    (hportsj:C.gates[j.val].inputs=[i.val,(m+1)+k.val]∨
      C.gates[j.val].inputs=[(m+1)+k.val,i.val])
    (hcomp:∀ v:Fin (m+1), v≠i→
      (C.wires (List.ofFn (Ak.singleton v))).getD ((m+1)+k.val) false=true)
    (hreadt:(m+1)+j.val∈C.gates[t.val].inputs):
    ∃ D:Circuit, Monotone2 D∧IW m D∧D.size+3≤C.size:=by
  apply Er m hm C hC htC hshape i k j t hkj hjt hopj hportsj _ hreadt
  intro v
  rw [HQ]
  exact hcomp (i.succAbove v) (Fin.succAbove_ne i v)
end Au
namespace Av
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma GC (n:ℕ) (C:Circuit)
    (hshape:∀ (t:ℕ) (ht:t < C.gates.length),
      ∃ a b, C.gates[t].inputs=[a,b]∧a≠b∧a < n+t∧b < n+t)
    (w:ℕ) (j:Fin C.gates.length) (hread:w∈C.gates[j.val].inputs):
    ∃ a, (C.gates[j.val].inputs=[w,a]∨C.gates[j.val].inputs=[a,w])∧
      a≠w∧a < n+j.val:=by
  obtain ⟨a,b,hab,hdist,ha,hb⟩:=hshape j.val j.isLt
  have hmember:w=a∨w=b:=by simpa [hab] using hread
  rcases hmember with hwa | hwb
  · refine ⟨b,Or.inl ?_,?_,hb⟩
    · simpa [hwa] using hab
    · simpa [hwa] using Ne.symm hdist
  · refine ⟨a,Or.inr ?_,?_,ha⟩
    · simpa [hwb] using hab
    · simpa [hwb] using hdist
end Av
namespace Av
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma II (n:ℕ) (hn:3≤n) (C:Circuit)
    (i:Fin n) (a:ℕ)
    (hsupport:∀ k:Fin n, k≠i→
      (C.wires (List.ofFn (Ak.singleton k))).getD a false=true):
    n≤a:=by
  by_contra hnot
  have ha:a < n:=by omega
  let q:Fin n:=⟨a,ha⟩
  obtain ⟨k,hki,hkq⟩:=Fin.exists_ne_and_ne_of_two_lt i q (by omega)
  have hs:=hsupport k hki
  change (run C.gates (List.ofFn (Ak.singleton k))).getD a false=true at hs
  rw [Ig C.gates _ a (by simpa using ha)] at hs
  change (List.ofFn (Ak.singleton k)).getD q.val false=true at hs
  rw [Ak.HH] at hs
  simp [Ak.singleton, Ne.symm hkq] at hs
lemma Jh (n:ℕ) (hn:3≤n)
    (C:Circuit) (ht:IW n C) (j:ℕ) (hj:j < C.gates.length)
    (i:Fin n) (a:ℕ) (hai:a≠i.val) (ha:a < n+j)
    (hports:C.gates[j].inputs=[i.val,a]∨C.gates[j].inputs=[a,i.val])
    (hunique:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j)
    (hop:C.gates[j].op=GateOp.and):
    ∃ k:Fin C.gates.length, k.val < j∧a=n+k.val:=by
  have hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card):=by
    intro S
    simpa using ht (fun t=>decide (t∈S))
  have hs:=Ak.IX C j hj i a hai ha
    hports hunique (Aw.Je n C ht i) hcorrect hop
  have han:=II n hn C i a hs
  refine ⟨⟨a-n,by omega⟩,?_,?_⟩
  · change a-n < j
    omega
  · change a=n+(a-n)
    omega
lemma IY (n:ℕ) (hn:3≤n)
    (C:Circuit) (ht:IW n C) (j:ℕ) (hj:j < C.gates.length)
    (i:Fin n) (a:ℕ)
    (hports:C.gates[j].inputs=[i.val,a]∨C.gates[j].inputs=[a,i.val])
    (hop:C.gates[j].op=GateOp.and):C.output≠n+j:=by
  obtain ⟨k,hki,_⟩:=Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  obtain ⟨l,hli,hlk⟩:=Fin.exists_ne_and_ne_of_two_lt i k (by omega)
  have hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun t=>decide (t∈S)))=decide (2≤S.card):=by
    intro S
    simpa using ht (fun t=>decide (t∈S))
  have heval:C.eval (List.ofFn (Ak.pair k l))=true:=by
    change C.eval (List.ofFn (fun t=>decide (t=k∨t=l)))=true
    simpa [Ne.symm hlk] using hcorrect ({k,l}:Finset (Fin n))
  have hraw:(run C.gates (List.ofFn (Ak.pair k l))).getD i.val false=false:=by
    rw [Ig C.gates _ i.val (by simpa using i.isLt), Ak.HH]
    simp [Ak.pair, Ne.symm hki, Ne.symm hli]
  have hi:i.val < n+j:=by omega
  have hgate:=If C.gates (List.ofFn (Ak.pair k l)) j hj
  simp only [List.length_ofFn] at hgate
  have hgatefalse:(run C.gates (List.ofFn (Ak.pair k l))).getD (n+j) false=false:=by
    rw [hgate,hop]
    rcases hports with hports | hports <;>
      simp only [hports,List.map_cons,List.map_nil,hi,ite_true,GateOp.eval,
        List.all_cons,List.all_nil,id_eq,hraw,Bool.false_and,Bool.and_false,Bool.and_true]
  intro hout
  change (run C.gates (List.ofFn (Ak.pair k l))).getD C.output false=true at heval
  rw [hout,hgatefalse] at heval
  contradiction
end Av
namespace Av
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Gk (n:ℕ) (hn:3≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C)
    (i:Fin n) (j:Fin C.gates.length)
    (hread:i.val∈C.gates[j.val].inputs) (hop:C.gates[j.val].op=GateOp.and)
    (hunique:∀ t:Fin C.gates.length, i.val∈C.gates[t.val].inputs→t=j):
    ∃ k t:Fin C.gates.length, k.val < j.val∧j.val < t.val∧
      (C.gates[j.val].inputs=[i.val,n+k.val]∨C.gates[j.val].inputs=[n+k.val,i.val])∧
      (∀ v:Fin n, v≠i→
        (C.wires (List.ofFn (fun u:Fin n=>decide (u=v)))).getD (n+k.val) false=true)∧
      C.output≠n+j.val∧n+j.val∈C.gates[t.val].inputs:=by
  have hshape:=Ao.Gh
    n (by omega) C hmin ht
  obtain ⟨a,hports,hai,ha⟩:=GC n C hshape i.val j hread
  have huniqueNat:∀ (t:ℕ) (ht:t < C.gates.length),
      i.val∈C.gates[t].inputs→t=j.val:=by
    intro t ht hreadt
    exact congrArg Fin.val (hunique ⟨t,ht⟩ hreadt)
  obtain ⟨k,hkj,hak⟩:=Jh n hn C ht j.val j.isLt
    i a hai ha hports huniqueNat hop
  have hout:=IY n hn C ht j.val j.isLt i a hports hop
  obtain ⟨t,hjt,hreadt⟩:=
    (Ay.Gb n C hmin
      (Jb n (by omega) C ht) j).resolve_left hout
  have hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn (fun u=>decide (u∈S)))=decide (2≤S.card):=by
    intro S
    simpa using ht (fun u=>decide (u∈S))
  have hs:=Ak.IX C j.val j.isLt i a hai ha
    hports huniqueNat (Aw.Je n C ht i) hcorrect hop
  refine ⟨k,t,hkj,hjt,?_,?_,hout,hreadt⟩
  · simpa only [hak] using hports
  · intro v hvi
    change (C.wires (List.ofFn (Ak.singleton v))).getD (n+k.val) false=true
    rw [← hak]
    exact hs v hvi
end Av
namespace Au
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
lemma Gj (n:ℕ) (hn:3≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:IW n C)
    (i:Fin n) (j:Fin C.gates.length)
    (hread:i.val∈C.gates[j.val].inputs) (hop:C.gates[j.val].op=GateOp.and)
    (hunique:∀ t:Fin C.gates.length, i.val∈C.gates[t.val].inputs→t=j):
    ∃ D:Circuit, Monotone2 D∧IW (n-1) D∧D.size+3≤C.size:=by
  obtain ⟨k,t,hkj,hjt,hports,hcomp,hout,hreadt⟩:=
    Av.Gk n hn C hmin ht i j hread hop hunique
  have hshape:=Ao.Gh
    n (by omega) C hmin ht
  cases n with
  | zero=>omega
  | succ m=>
      simpa using IS m (by omega) C hmin.1 ht hshape
        i k j t hkj hjt hop hports hcomp hreadt
end Au
namespace Am
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Aj
open Ar
lemma Jt:Ba:=by
  intro n hn C hmin ht hshape i j hread hop hunique
  exact Au.Gj n hn C hmin ht
    i j hread hop hunique
lemma Dz
    (n₀:ℕ) (C₀:Circuit) (hC₀:Monotone2 C₀) (ht₀:IW n₀ C₀)
    (hbudget₀:C₀.size+8≤3*n₀):
    ∃ (n:ℕ) (C:Circuit), 3≤n∧n≤n₀∧
      IsMinimalMonoCircuit n C∧IW n C∧C.size+8≤3*n∧
      AO n C∧
      (∀ E:Circuit, Monotone2 E→circuitFun n E=circuitFun n C→
        E.size=C.size→IB n C≤IB n E)∧
      (∀ i:Fin n, (Hx C i.val).card=2)∧
      (∀ (m:ℕ), m < n→∀ E:Circuit, Monotone2 E→IW m E→
        3*m < E.size+8):=by
  exact Cl
    IV Jt n₀ C₀ hC₀ ht₀ hbudget₀
end Am
namespace Ab
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open AD
open AE
open Af
open Ac
open AF
open Am
lemma Iy (n:ℕ) (C:Circuit) (hshape:AO n C):ReadsBack n C:=by
  intro j hj w hw
  rw [Ag.EN C j hj] at hw
  obtain ⟨a, b, hab, hne, ha, hb⟩:=hshape j hj
  rw [hab] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ha
  · exact hb
lemma Ix (n:ℕ) (C:Circuit) (hshape:AO n C):
    ∀ g∈C.gates, g.inputs.length=2:=by
  intro g hg
  obtain ⟨j, hj, rfl⟩:=List.mem_iff_getElem.mp hg
  obtain ⟨a, b, hab, hne, ha, hb⟩:=hshape j hj
  simp [hab]
lemma JM (n:ℕ) (C:Circuit) (w:ℕ) (hw:n+C.gates.length≤w):
    As.JI C n w=0:=by
  unfold As.JI
  apply Finset.sum_eq_zero
  intro j hj
  unfold As.JN
  rw [Cq]
  have hz:∀ a:ℕ, (if a=w∧a < n+j.val then 1 else 0:ℕ)=0:=by
    intro a
    have hn:¬ (a=w∧a < n+j.val):=by have hjlt:=j.isLt; omega
    simp [hn]
  simp [hz]
lemma He (n:ℕ) (C:Circuit)
    (hout:C.output+1=n+C.size) (h:Fin C.gates.length)
    (hh:C.output=n+h.val):(∑ j, ET C n j h)=0:=by
  apply Finset.sum_eq_zero
  intro j hj
  have hn:¬ h.val < j.val:=by
    have hjlt:=j.isLt
    unfold Circuit.size at hout
    omega
  have hz:JQ n j.val h.val=fun _=>0:=by
    funext w
    simp [JQ, hn]
  simp [ET, hz]
lemma Dc (n:ℕ) (C:Circuit)
    (hout:C.output+1=n+C.size) (h:Fin C.gates.length):
    0 < credit C n h↔2≤As.JI C n (n+h.val):=by
  rw [JK]
  by_cases hh:C.output=n+h.val
  · have hz:=He n C hout h hh
    simp [credit, Hc, hh, hz]
  · simp only [credit, Hc, ite_eq_right hh, Nat.add_zero]
    omega
lemma Db (n:ℕ) (C:Circuit) (hb:ReadsBack n C)
    (hout:C.output+1=n+C.size) (h:Fin C.gates.length):
    0 < credit C n h↔2≤readsIn C (Finset.range C.gates.length) (n+h.val):=by
  rw [← Ag.JJ hb]
  exact Dc n C hout h
lemma Kj (n:ℕ) (C:Circuit) (i:Fin n) (h:Fin C.gates.length):
    Ag.wire n C i (n+h.val)=true↔h∈rows n C i:=by
  exact (FU n C i h).symm
lemma FM (n:ℕ) (C:Circuit) (b h:Fin C.gates.length):
    Ai.FL (IQ (rows n C) b) C (n+h.val)=
      IQ (rows n C) b∩IQ (rows n C) h:=by
  ext i
  simp [Ai.FL, IQ, rows, Ag.wire,
    Ag.singleton, Iz]
lemma IR (n:ℕ) (C:Circuit) (i:Fin n) (j k:Fin C.gates.length)
    (hji:j∈rows n C i) (hki:k∈rows n C i)
    (hproper:IQ (rows n C) j∩IQ (rows n C) k≠IQ (rows n C) j):
    2≤(IQ (rows n C) j).card:=by
  let X:=IQ (rows n C) j
  have hi:i∈X:=by simpa [X, IQ] using hji
  by_contra hsmall
  have hc:X.card≤1:=by dsimp [X]; omega
  have hx:X={i}:=(Finset.eq_of_subset_of_card_le
    (Finset.singleton_subset_iff.mpr hi) (by simpa using hc)).symm
  have hsub:X⊆IQ (rows n C) k:=by
    intro t ht
    rw [hx] at ht
    have he:t=i:=Finset.mem_singleton.mp ht
    subst t
    simpa [IQ] using hki
  exact hproper (Finset.inter_eq_left.mpr hsub)
def BF (n:ℕ) (C:Circuit):Finset ℕ:=
  (Finset.univ.filter fun h:Fin C.gates.length=>0 < credit C n h).image
    (fun h=>n+h.val)
lemma FQ (n:ℕ) (C:Circuit) (w:ℕ):
    w∈BF n C↔∃ h:Fin C.gates.length, 0 < credit C n h∧n+h.val=w:=by
  simp [BF]
lemma Bd (n:ℕ) (C:Circuit) (hC:Monotone2 C)
    (hshape:AO n C)
    (hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn fun t=>decide (t∈S))=decide (2≤S.card))
    (hraw:∀ i:Fin n, JW C i≤2)
    (hout:C.output+1=n+C.size):
    Hs (credit C n) (rows n C):=by
  have hb:=Iy n C hshape
  have hmono:AndOrOnly C:=by
    intro g hg
    exact (hC g hg).1
  have hbinary:=Ix n C hshape
  intro i j k hjpos hkpos hji hfresh hjk hki hproper
  let X:=IQ (rows n C) j
  have hiX:i∈X:=by simpa [X, IQ] using hji
  have hX:2≤X.card:=IR n C i j k hji hki hproper
  have hBgates:∀ a∈BF n C, n≤a:=by
    intro a ha
    obtain ⟨h, hh, he⟩:=(FQ n C a).mp ha
    omega
  have hbranch:∀ a∈BF n C,
      2≤readsIn C (Finset.range C.gates.length) a:=by
    intro a ha
    obtain ⟨h, hh, he⟩:=(FQ n C a).mp ha
    rw [← he]
    exact (Db n C hb hout h).mp hh
  have houtside:∀ u, n≤u→u∉BF n C→
      readsIn C (Finset.range C.gates.length) u≤1:=by
    intro u hnu hnot
    by_contra hn
    have hu2:2≤readsIn C (Finset.range C.gates.length) u:=by omega
    by_cases hul:u < n+C.gates.length
    · let h:Fin C.gates.length:=⟨u - n, by omega⟩
      have he:n+h.val=u:=by dsimp [h]; omega
      have hp:0 < credit C n h:=
        (Db n C hb hout h).mpr (by simpa only [he] using hu2)
      exact hnot ((FQ n C u).mpr ⟨h, hp, he⟩)
    · have hz:readsIn C (Finset.range C.gates.length) u=0:=by
        rw [← Ag.JJ hb]
        exact JM n C u (by omega)
      omega
  have hforce:∀ l∈X, Ag.wire n C l (n+j.val)=true:=by
    intro l hl
    apply (Kj n C l j).mpr
    simpa [X, IQ] using hl
  have hfr:∀ u, n≤u→u < n+j.val→
      2≤readsIn C (Finset.range C.gates.length) u→Ag.wire n C i u=false:=by
    intro u hnu huj hu2
    let h:Fin C.gates.length:=⟨u - n, by have hjlt:=j.isLt; omega⟩
    have he:n+h.val=u:=by dsimp [h]; omega
    have hhj:h < j:=by change h.val < j.val; dsimp [h]; omega
    have hp:0 < credit C n h:=
      (Db n C hb hout h).mpr (by simpa only [he] using hu2)
    have hn:Ag.wire n C i u≠true:=by
      intro htrue
      apply hfresh h hhj hp
      apply (Kj n C i h).mp
      simpa only [he] using htrue
    cases hv:Ag.wire n C i u with
    | false=>rfl
    | true=>exact (hn hv).elim
  have hraw':readsIn C (Finset.range C.gates.length) i.val≤2:=by
    rw [← Ag.JJ hb, JL]
    exact hraw i
  have hneg:∀ l∈X, Ag.wire n C l C.output=false:=by
    intro l hl
    change C.eval (List.ofFn fun t:Fin n=>decide (t=l))=false
    simpa using hcorrect {l}
  have hpair:∀ l∈X, l≠i→
      Ai.value C (PEqualNP.EdgeOwnership.pairInput i l) C.output=true:=by
    intro l hl hli
    change C.eval (List.ofFn fun t:Fin n=>decide (t=i∨t=l))=true
    simpa [Ne.symm hli] using hcorrect {i,l}
  have hcB:n+k.val∈BF n C:=(FQ n C _).mpr ⟨k, hkpos, rfl⟩
  have hbc:n+j.val < n+k.val:=by have hjkv:j.val < k.val:=hjk; omega
  have hlocal:Ai.FL X C (n+k.val)=
      IQ (rows n C) j∩IQ (rows n C) k:=FM n C j k
  have hic:i∈Ai.FL X C (n+k.val):=by
    rw [hlocal]
    exact Finset.mem_inter.mpr ⟨hiX, by simpa [IQ] using hki⟩
  have hlocalproper:Ai.FL X C (n+k.val)≠X:=by
    intro he
    exact hproper (hlocal.symm.trans he)
  obtain hs | ⟨a, haB, hba, hak, hs⟩:=
    Ai.Hb hb hmono hbinary X hX i hiX
      (BF n C) hBgates (n+j.val) (by omega) hforce hfr hraw' hbranch houtside
      hneg hpair (n+k.val) hcB hbc hic hlocalproper
  · refine ⟨k, hkpos, hjk, le_rfl, ?_⟩
    rw [← FM n C j k]
    exact hs
  · obtain ⟨h, hhpos, hha⟩:=(FQ n C a).mp haB
    refine ⟨h, hhpos, ?_, ?_, ?_⟩
    · change j.val < h.val
      omega
    · change h.val≤k.val
      omega
    · rw [← FM n C j h]
      simpa only [hha] using hs
lemma Gd (n:ℕ) (hn:2≤n) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:Aj.IW n C)
    (hshape:AO n C) (hraw:∀ i:Fin n, JW C i≤2):
    Hs (credit C n) (rows n C):=by
  apply Bd n C hmin.1 hshape
  · intro S
    simpa using ht (fun t=>decide (t∈S))
  · exact hraw
  · exact AA.Gi n hn C hmin ht
end Ab
namespace Ab
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open AE
open Af
open Ac
open Am
lemma regular_minimum_slots (n:ℕ) (hn:2≤n) (_hupper:n≤12) (C:Circuit)
    (hmin:IsMinimalMonoCircuit n C) (ht:Aj.IW n C)
    (hshape:AO n C)
    (hraw:∀ i:Fin n, (Hx C i.val).card=2)
    (hsize:C.size+8≤3*n):
    7≤n∧∃ slots:Fin n→Finset (Fin (n - 7)),
      (∑ i, (1 / 2:ℚ)^(2+(slots i).card)≤1)∧
      (∀ F:Finset (Fin (n - 7)), F.Nonempty→
        (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)∧
      Az.BO slots:=by
  have hb:=AA.GD n hn C hmin ht hshape hraw hsize
  have hports:∀ i:Fin n, JW C i=2:=by
    intro i
    rw [AA.HD n C hshape]
    exact hraw i
  have hrawle:∀ i:Fin n, JW C i≤2:=fun i=>(hports i).le
  have hcorrect:∀ S:Finset (Fin n),
      C.eval (List.ofFn fun t=>decide (t∈S))=decide (2≤S.card):=by
    intro S
    simpa using ht (fun t=>decide (t∈S))
  refine ⟨hb.1, ?_⟩
  apply AF.Dy (credit C n) hb.2 (rows n C)
  · exact Fk n C hmin.1 hcorrect hrawle
  · intro J hJ hpositive
    exact GE n C hmin.1 hshape hcorrect hrawle J hJ
  · exact Gd n hn C hmin ht hshape hrawle
end Ab
def uniform0NatProfile (c:Fin 1→Nat):Prop:=
  let n0:Nat:=c 0
  (c 0≤7)∧
  (n0=7)∧
  (n0≤4)
def uniform1NatProfile (c:Fin 2→Nat):Prop:=
  let n0:Nat:=c 0
  let n1:Nat:=c 1
  let S0:Nat:=n1
  (c 0≤8)∧
  (c 1≤8)∧
  ((n0+n1)=8)∧
  ((2*n0+n1)≤8)∧
  (4*n1≤8)
def uniform2NatProfile (c:Fin 4→Nat):Prop:=
  let n0:Nat:=c 0
  let n1:Nat:=c 1
  let n2:Nat:=c 2
  let n3:Nat:=c 3
  let S0:Nat:=(n1+n3)
  let H0_1:Nat:=n3
  let S1:Nat:=(n2+n3)
  (c 0≤9)∧
  (c 1≤9)∧
  (c 2≤9)∧
  (c 3≤9)∧
  ((n0+n1+n2+n3)=9)∧
  ((4*n0+2*n1+2*n2+n3)≤16)∧
  ((8*n1+4*n3)≤16)∧
  ((8*n2+4*n3)≤16)∧
  (8*n3≤16)∧
  (((0 < c 3∧2≤H0_1∧H0_1 < S0)→False))
def uniform3NatProfile (c:Fin 8→Nat):Prop:=
  let n0:Nat:=c 0
  let n1:Nat:=c 1
  let n2:Nat:=c 2
  let n3:Nat:=c 3
  let n4:Nat:=c 4
  let n5:Nat:=c 5
  let n6:Nat:=c 6
  let n7:Nat:=c 7
  let S0:Nat:=(n1+n3+n5+n7)
  let H0_1:Nat:=(n3+n7)
  let H0_2:Nat:=(n5+n7)
  let S1:Nat:=(n2+n3+n6+n7)
  let H1_2:Nat:=(n6+n7)
  let S2:Nat:=(n4+n5+n6+n7)
  (c 0≤10)∧
  (c 1≤10)∧
  (c 2≤10)∧
  (c 3≤10)∧
  (c 4≤10)∧
  (c 5≤10)∧
  (c 6≤10)∧
  (c 7≤10)∧
  ((n0+n1+n2+n3+n4+n5+n6+n7)=10)∧
  ((8*n0+4*n1+4*n2+2*n3+4*n4+2*n5+2*n6+n7)≤32)∧
  ((16*n1+8*n3+8*n5+4*n7)≤32)∧
  ((16*n2+8*n3+8*n6+4*n7)≤32)∧
  ((16*n3+8*n7)≤32)∧
  ((16*n4+8*n5+8*n6+4*n7)≤32)∧
  ((16*n5+8*n7)≤32)∧
  ((16*n6+8*n7)≤32)∧
  (16*n7≤32)∧
  (((0 < c 3∧2≤H0_1∧H0_1 < S0)→False))∧
  (((0 < c 7∧2≤H0_1∧H0_1 < S0)→False))∧
  (((0 < c 5∧2≤H0_2∧H0_2 < S0)→False))∧
  (((0 < c 7∧2≤H0_2∧H0_2 < S0)→(H0_1=1∧H0_1 < S0)))∧
  (((0 < c 6∧2≤H1_2∧H1_2 < S1)→False))
def uniform4NatProfile (c:Fin 16→Nat):Prop:=
  let n0:Nat:=c 0
  let n1:Nat:=c 1
  let n2:Nat:=c 2
  let n3:Nat:=c 3
  let n4:Nat:=c 4
  let n5:Nat:=c 5
  let n6:Nat:=c 6
  let n7:Nat:=c 7
  let n8:Nat:=c 8
  let n9:Nat:=c 9
  let n10:Nat:=c 10
  let n11:Nat:=c 11
  let n12:Nat:=c 12
  let n13:Nat:=c 13
  let n14:Nat:=c 14
  let n15:Nat:=c 15
  let S0:Nat:=(n1+n3+n5+n7+n9+n11+n13+n15)
  let H0_1:Nat:=(n3+n7+n11+n15)
  let H0_2:Nat:=(n5+n7+n13+n15)
  let H0_3:Nat:=(n9+n11+n13+n15)
  let S1:Nat:=(n2+n3+n6+n7+n10+n11+n14+n15)
  let H1_2:Nat:=(n6+n7+n14+n15)
  let H1_3:Nat:=(n10+n11+n14+n15)
  let S2:Nat:=(n4+n5+n6+n7+n12+n13+n14+n15)
  let H2_3:Nat:=(n12+n13+n14+n15)
  let S3:Nat:=(n8+n9+n10+n11+n12+n13+n14+n15)
  (c 0≤11)∧
  (c 1≤11)∧
  (c 2≤11)∧
  (c 3≤11)∧
  (c 4≤11)∧
  (c 5≤11)∧
  (c 6≤11)∧
  (c 7≤11)∧
  (c 8≤11)∧
  (c 9≤11)∧
  (c 10≤11)∧
  (c 11≤11)∧
  (c 12≤11)∧
  (c 13≤11)∧
  (c 14≤11)∧
  (c 15≤11)∧
  ((n0+n1+n2+n3+n4+n5+n6+n7+n8+n9+n10+n11+n12+n13+n14+n15)=11)∧
  ((16*n0+8*n1+8*n2+4*n3+8*n4+4*n5+4*n6+2*n7+8*n8+4*n9+4*n10+2*n11+4*n12+2*n13+2*n14+n15)≤64)∧
  ((32*n1+16*n3+16*n5+8*n7+16*n9+8*n11+8*n13+4*n15)≤64)∧
  ((32*n2+16*n3+16*n6+8*n7+16*n10+8*n11+8*n14+4*n15)≤64)∧
  ((32*n3+16*n7+16*n11+8*n15)≤64)∧
  ((32*n4+16*n5+16*n6+8*n7+16*n12+8*n13+8*n14+4*n15)≤64)∧
  ((32*n5+16*n7+16*n13+8*n15)≤64)∧
  ((32*n6+16*n7+16*n14+8*n15)≤64)∧
  ((32*n7+16*n15)≤64)∧
  ((32*n8+16*n9+16*n10+8*n11+16*n12+8*n13+8*n14+4*n15)≤64)∧
  ((32*n9+16*n11+16*n13+8*n15)≤64)∧
  ((32*n10+16*n11+16*n14+8*n15)≤64)∧
  ((32*n11+16*n15)≤64)∧
  ((32*n12+16*n13+16*n14+8*n15)≤64)∧
  ((32*n13+16*n15)≤64)∧
  ((32*n14+16*n15)≤64)∧
  (32*n15≤64)∧
  (((0 < c 3∧2≤H0_1∧H0_1 < S0)→False))∧
  (((0 < c 7∧2≤H0_1∧H0_1 < S0)→False))∧
  (((0 < c 11∧2≤H0_1∧H0_1 < S0)→False))∧
  (((0 < c 15∧2≤H0_1∧H0_1 < S0)→False))∧
  (((0 < c 5∧2≤H0_2∧H0_2 < S0)→False))∧
  (((0 < c 7∧2≤H0_2∧H0_2 < S0)→(H0_1=1∧H0_1 < S0)))∧
  (((0 < c 13∧2≤H0_2∧H0_2 < S0)→False))∧
  (((0 < c 15∧2≤H0_2∧H0_2 < S0)→(H0_1=1∧H0_1 < S0)))∧
  (((0 < c 9∧2≤H0_3∧H0_3 < S0)→False))∧
  (((0 < c 11∧2≤H0_3∧H0_3 < S0)→(H0_1=1∧H0_1 < S0)))∧
  (((0 < c 13∧2≤H0_3∧H0_3 < S0)→(H0_2=1∧H0_2 < S0)))∧
  (((0 < c 15∧2≤H0_3∧H0_3 < S0)→((H0_1=1∧H0_1 < S0)∨(H0_2=1∧H0_2 < S0))))∧
  (((0 < c 6∧2≤H1_2∧H1_2 < S1)→False))∧
  (((0 < c 14∧2≤H1_2∧H1_2 < S1)→False))∧
  (((0 < c 10∧2≤H1_3∧H1_3 < S1)→False))∧
  (((0 < c 14∧2≤H1_3∧H1_3 < S1)→(H1_2=1∧H1_2 < S1)))∧
  (((0 < c 12∧2≤H2_3∧H2_3 < S2)→False))
namespace Az
open MaskDecode
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def maskTable0:Fin 1→Finset (Fin 0):=![∅]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma decode_table0:∀ s:Fin 1, decode 0 s=maskTable0 s:=by
  decide+kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma maskSum0 (f:Fin 1→ℕ):(∑ s, f s)=f 0:=by
  simp [Fin.sum_univ_succ, Nat.add_assoc]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma profile_explicit0 (c:Fin 1→ℕ) (h:profile 0 7 c):uniform0NatProfile c:=by
  rcases h with ⟨hb, hc, hg, hf, ht⟩
  have hS:∀ j:Fin 0, FP 0 c j=∑ s:Fin 1, if j∈decode 0 s then c s else 0:=by intro j; rfl
  have hH:∀ j k:Fin 0, FN 0 c j k=∑ s:Fin 1, if j∈decode 0 s∧k∈decode 0 s then c s else 0:=by intro j k; rfl
  unfold uniform0NatProfile
  refine ⟨hb 0, ?_, ?_⟩
  · change (∑ s:Fin 1, c s)=7 at hc
    simpa [maskSum0, Nat.add_assoc] using hc
  · change (∑ s:Fin 1, 2^(0 - (decode 0 s).card)*c s)≤4 at hg
    rw [maskSum0] at hg
    norm_num [decode_table0, maskTable0, hS, hH, maskSum0, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hg ⊢
    exact hg
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def maskTable1:Fin 2→Finset (Fin 1):=![∅, {0}]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma decode_table1:∀ s:Fin 2, decode 1 s=maskTable1 s:=by
  decide+kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma maskSum1 (f:Fin 2→ℕ):(∑ s, f s)=f 0+f 1:=by
  simp [Fin.sum_univ_succ, Nat.add_assoc]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma profile_explicit1 (c:Fin 2→ℕ) (h:profile 1 8 c):uniform1NatProfile c:=by
  rcases h with ⟨hb, hc, hg, hf, ht⟩
  have hS:∀ j:Fin 1, FP 1 c j=∑ s:Fin 2, if j∈decode 1 s then c s else 0:=by intro j; rfl
  have hH:∀ j k:Fin 1, FN 1 c j k=∑ s:Fin 2, if j∈decode 1 s∧k∈decode 1 s then c s else 0:=by intro j k; rfl
  unfold uniform1NatProfile
  refine ⟨hb 0, hb 1, ?_, ?_, ?_⟩
  · change (∑ s:Fin 2, c s)=8 at hc
    simpa [maskSum1, Nat.add_assoc] using hc
  · change (∑ s:Fin 2, 2^(1 - (decode 1 s).card)*c s)≤8 at hg
    rw [maskSum1] at hg
    norm_num [decode_table1, maskTable1, hS, hH, maskSum1, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hg ⊢
    exact hg
  · have hcut:=hf 1 (by decide+kernel)
    change (∑ s:Fin 2, if decode 1 1⊆decode 1 s then (2^((decode 1 1).card+1)*2^(1 - (decode 1 s).card))*c s else 0)≤8 at hcut
    rw [maskSum1] at hcut
    norm_num [decode_table1, maskTable1, hS, hH, maskSum1, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def maskTable2:Fin 4→Finset (Fin 2):=![∅, {0}, {1}, {0, 1}]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma decode_table2:∀ s:Fin 4, decode 2 s=maskTable2 s:=by
  decide+kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma maskSum2 (f:Fin 4→ℕ):(∑ s, f s)=f 0+f 1+f 2+f 3:=by
  simp [Fin.sum_univ_succ, Nat.add_assoc]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma profile_explicit2 (c:Fin 4→ℕ) (h:profile 2 9 c):uniform2NatProfile c:=by
  rcases h with ⟨hb, hc, hg, hf, ht⟩
  have hS:∀ j:Fin 2, FP 2 c j=∑ s:Fin 4, if j∈decode 2 s then c s else 0:=by intro j; rfl
  have hH:∀ j k:Fin 2, FN 2 c j k=∑ s:Fin 4, if j∈decode 2 s∧k∈decode 2 s then c s else 0:=by intro j k; rfl
  unfold uniform2NatProfile
  refine ⟨hb 0, hb 1, hb 2, hb 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (∑ s:Fin 4, c s)=9 at hc
    simpa [maskSum2, Nat.add_assoc] using hc
  · change (∑ s:Fin 4, 2^(2 - (decode 2 s).card)*c s)≤16 at hg
    rw [maskSum2] at hg
    norm_num [decode_table2, maskTable2, hS, hH, maskSum2, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hg ⊢
    exact hg
  · have hcut:=hf 1 (by decide+kernel)
    change (∑ s:Fin 4, if decode 2 1⊆decode 2 s then (2^((decode 2 1).card+1)*2^(2 - (decode 2 s).card))*c s else 0)≤16 at hcut
    rw [maskSum2] at hcut
    norm_num [decode_table2, maskTable2, hS, hH, maskSum2, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 2 (by decide+kernel)
    change (∑ s:Fin 4, if decode 2 2⊆decode 2 s then (2^((decode 2 2).card+1)*2^(2 - (decode 2 s).card))*c s else 0)≤16 at hcut
    rw [maskSum2] at hcut
    norm_num [decode_table2, maskTable2, hS, hH, maskSum2, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 3 (by decide+kernel)
    change (∑ s:Fin 4, if decode 2 3⊆decode 2 s then (2^((decode 2 3).card+1)*2^(2 - (decode 2 s).card))*c s else 0)≤16 at hcut
    rw [maskSum2] at hcut
    norm_num [decode_table2, maskTable2, hS, hH, maskSum2, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have htemp:=ht 3 0 1 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum2] at htemp
    norm_num [decode_table2, maskTable2, hS, hH, maskSum2, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def maskTable3:Fin 8→Finset (Fin 3):=![∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma decode_table3:∀ s:Fin 8, decode 3 s=maskTable3 s:=by
  decide+kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma maskSum3 (f:Fin 8→ℕ):(∑ s, f s)=f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7:=by
  simp [Fin.sum_univ_succ, Nat.add_assoc]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma profile_explicit3 (c:Fin 8→ℕ) (h:profile 3 10 c):uniform3NatProfile c:=by
  rcases h with ⟨hb, hc, hg, hf, ht⟩
  have hS:∀ j:Fin 3, FP 3 c j=∑ s:Fin 8, if j∈decode 3 s then c s else 0:=by intro j; rfl
  have hH:∀ j k:Fin 3, FN 3 c j k=∑ s:Fin 8, if j∈decode 3 s∧k∈decode 3 s then c s else 0:=by intro j k; rfl
  unfold uniform3NatProfile
  refine ⟨hb 0, hb 1, hb 2, hb 3, hb 4, hb 5, hb 6, hb 7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (∑ s:Fin 8, c s)=10 at hc
    simpa [maskSum3, Nat.add_assoc] using hc
  · change (∑ s:Fin 8, 2^(3 - (decode 3 s).card)*c s)≤32 at hg
    rw [maskSum3] at hg
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hg ⊢
    exact hg
  · have hcut:=hf 1 (by decide+kernel)
    change (∑ s:Fin 8, if decode 3 1⊆decode 3 s then (2^((decode 3 1).card+1)*2^(3 - (decode 3 s).card))*c s else 0)≤32 at hcut
    rw [maskSum3] at hcut
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 2 (by decide+kernel)
    change (∑ s:Fin 8, if decode 3 2⊆decode 3 s then (2^((decode 3 2).card+1)*2^(3 - (decode 3 s).card))*c s else 0)≤32 at hcut
    rw [maskSum3] at hcut
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 3 (by decide+kernel)
    change (∑ s:Fin 8, if decode 3 3⊆decode 3 s then (2^((decode 3 3).card+1)*2^(3 - (decode 3 s).card))*c s else 0)≤32 at hcut
    rw [maskSum3] at hcut
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 4 (by decide+kernel)
    change (∑ s:Fin 8, if decode 3 4⊆decode 3 s then (2^((decode 3 4).card+1)*2^(3 - (decode 3 s).card))*c s else 0)≤32 at hcut
    rw [maskSum3] at hcut
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 5 (by decide+kernel)
    change (∑ s:Fin 8, if decode 3 5⊆decode 3 s then (2^((decode 3 5).card+1)*2^(3 - (decode 3 s).card))*c s else 0)≤32 at hcut
    rw [maskSum3] at hcut
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 6 (by decide+kernel)
    change (∑ s:Fin 8, if decode 3 6⊆decode 3 s then (2^((decode 3 6).card+1)*2^(3 - (decode 3 s).card))*c s else 0)≤32 at hcut
    rw [maskSum3] at hcut
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 7 (by decide+kernel)
    change (∑ s:Fin 8, if decode 3 7⊆decode 3 s then (2^((decode 3 7).card+1)*2^(3 - (decode 3 s).card))*c s else 0)≤32 at hcut
    rw [maskSum3] at hcut
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have htemp:=ht 3 0 1 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum3] at htemp
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 7 0 1 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum3] at htemp
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 5 0 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum3] at htemp
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 7 0 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum3] at htemp
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 6 1 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum3] at htemp
    norm_num [decode_table3, maskTable3, hS, hH, maskSum3, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def maskTable4:Fin 16→Finset (Fin 4):=![∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {1, 3}, {0, 1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma decode_table4:∀ s:Fin 16, decode 4 s=maskTable4 s:=by
  decide+kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma maskSum4 (f:Fin 16→ℕ):(∑ s, f s)=f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10+f 11+f 12+f 13+f 14+f 15:=by
  rw [Fin.sum_univ_add (a:=8) (b:=8)]
  simp [Fin.sum_univ_succ, Nat.add_assoc]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma profile_explicit4 (c:Fin 16→ℕ) (h:profile 4 11 c):uniform4NatProfile c:=by
  rcases h with ⟨hb, hc, hg, hf, ht⟩
  have hS:∀ j:Fin 4, FP 4 c j=∑ s:Fin 16, if j∈decode 4 s then c s else 0:=by intro j; rfl
  have hH:∀ j k:Fin 4, FN 4 c j k=∑ s:Fin 16, if j∈decode 4 s∧k∈decode 4 s then c s else 0:=by intro j k; rfl
  unfold uniform4NatProfile
  refine ⟨hb 0, hb 1, hb 2, hb 3, hb 4, hb 5, hb 6, hb 7, hb 8, hb 9, hb 10, hb 11, hb 12, hb 13, hb 14, hb 15, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (∑ s:Fin 16, c s)=11 at hc
    simpa [maskSum4, Nat.add_assoc] using hc
  · change (∑ s:Fin 16, 2^(4 - (decode 4 s).card)*c s)≤64 at hg
    rw [maskSum4] at hg
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hg ⊢
    exact hg
  · have hcut:=hf 1 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 1⊆decode 4 s then (2^((decode 4 1).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 2 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 2⊆decode 4 s then (2^((decode 4 2).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 3 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 3⊆decode 4 s then (2^((decode 4 3).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 4 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 4⊆decode 4 s then (2^((decode 4 4).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 5 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 5⊆decode 4 s then (2^((decode 4 5).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 6 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 6⊆decode 4 s then (2^((decode 4 6).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 7 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 7⊆decode 4 s then (2^((decode 4 7).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 8 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 8⊆decode 4 s then (2^((decode 4 8).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 9 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 9⊆decode 4 s then (2^((decode 4 9).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 10 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 10⊆decode 4 s then (2^((decode 4 10).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 11 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 11⊆decode 4 s then (2^((decode 4 11).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 12 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 12⊆decode 4 s then (2^((decode 4 12).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 13 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 13⊆decode 4 s then (2^((decode 4 13).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 14 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 14⊆decode 4 s then (2^((decode 4 14).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have hcut:=hf 15 (by decide+kernel)
    change (∑ s:Fin 16, if decode 4 15⊆decode 4 s then (2^((decode 4 15).card+1)*2^(4 - (decode 4 s).card))*c s else 0)≤64 at hcut
    rw [maskSum4] at hcut
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at hcut ⊢
    exact hcut
  · have htemp:=ht 3 0 1 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 7 0 1 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 11 0 1 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 15 0 1 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 5 0 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 7 0 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 13 0 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 15 0 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 9 0 3 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 11 0 3 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 13 0 3 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 15 0 3 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 6 1 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 14 1 2 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 10 1 3 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 14 1 3 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
  · have htemp:=ht 12 2 3 (by unfold FO; decide+kernel) (by decide+kernel) (by decide+kernel)
    simp only [Fin.exists_fin_succ] at htemp
    simp only [hS, hH, maskSum4] at htemp
    norm_num [decode_table4, maskTable4, hS, hH, maskSum4, Fin.sum_univ_succ, Fin.exists_fin_succ, Nat.add_assoc, ← Nat.mul_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.eq_singleton_iff_unique_mem] at htemp ⊢
    exact htemp
end Az
namespace Az
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma uniform0NatProfileFalse (c:Fin 1→Nat)
    (h:uniform0NatProfile c):False:=by
  unfold uniform0NatProfile at h
  omega
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma uniform1NatProfileFalse (c:Fin 2→Nat)
    (h:uniform1NatProfile c):False:=by
  unfold uniform1NatProfile at h
  omega
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma uniform2NatProfileFalse (c:Fin 4→Nat)
    (h:uniform2NatProfile c):False:=by
  unfold uniform2NatProfile at h
  omega
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma uniform3NatProfileFalse (c:Fin 8→Nat)
    (h:uniform3NatProfile c):False:=by
  unfold uniform3NatProfile at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
  linarith only [h8, h9, h10, h11, h12, h13, h14, h15, h16]
lemma uniformNatSplit (n k:Nat):n≤k∨k+1≤n:=by
  omega
lemma uniformTemporalCases {a b c:Nat} {P:Prop}
    (h:(0 < a∧2≤b∧b < c)→P):
    a=0∨b≤1∨c≤b∨P:=by
  by_cases ha:a=0
  · exact Or.inl ha
  · by_cases hb:b≤1
    · exact Or.inr (Or.inl hb)
    · by_cases hc:c≤b
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr (h ⟨by omega, by omega, by omega⟩)))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma uniformDpll4False (c:Fin 16→Nat)
    (h:uniform4NatProfile c):False:=by
  unfold uniform4NatProfile at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49⟩
  have z0:0≤c 0:=Nat.zero_le _
  have z1:0≤c 1:=Nat.zero_le _
  have z2:0≤c 2:=Nat.zero_le _
  have z3:0≤c 3:=Nat.zero_le _
  have z4:0≤c 4:=Nat.zero_le _
  have z5:0≤c 5:=Nat.zero_le _
  have z6:0≤c 6:=Nat.zero_le _
  have z7:0≤c 7:=Nat.zero_le _
  have z8:0≤c 8:=Nat.zero_le _
  have z9:0≤c 9:=Nat.zero_le _
  have z10:0≤c 10:=Nat.zero_le _
  have z11:0≤c 11:=Nat.zero_le _
  have z12:0≤c 12:=Nat.zero_le _
  have z13:0≤c 13:=Nat.zero_le _
  have z14:0≤c 14:=Nat.zero_le _
  have z15:0≤c 15:=Nat.zero_le _
  have split1:=uniformTemporalCases h34
  rcases split1 with b1_0_0 | b1_1_0 | b1_2_0 | bad1
  ·
    have split2:=uniformTemporalCases h33
    rcases split2 with b2_0_0 | b2_1_0 | b2_2_0 | bad2
    ·
      have split3:=uniformTemporalCases h35
      rcases split3 with b3_0_0 | b3_1_0 | b3_2_0 | bad3
      ·
        have split100000:=uniformNatSplit (c 1) 0
        rcases split100000 with i100000_0 | i100000_1
        ·
          have split100001:=uniformNatSplit (c 2) 0
          rcases split100001 with i100001_0 | i100001_1
          ·
            have split100002:=uniformNatSplit (c 0) 2
            rcases split100002 with i100002_0 | i100002_1
            ·
              linarith only [h16, h21, h22, h23, h25, h26, h27, h32, b1_0_0, b2_0_0, b3_0_0, i100000_0, i100001_0, i100002_0]
            ·
              linarith only [z1, z2, z4, z5, z8, h16, h17, h22, h31, h32, b3_0_0, i100002_1]
          ·
            have split100003:=uniformNatSplit (c 4) 0
            rcases split100003 with i100003_0 | i100003_1
            ·
              have split100004:=uniformNatSplit (c 8) 0
              rcases split100004 with i100004_0 | i100004_1
              ·
                have split100005:=uniformNatSplit (c 5) 1
                rcases split100005 with i100005_0 | i100005_1
                ·
                  linarith only [h16, h17, h19, h22, h26, h29, h31, h32, b1_0_0, b3_0_0, i100000_0, i100001_1, i100003_0, i100004_0, i100005_0]
                ·
                  linarith only [z7, z13, h16, h17, h19, h22, h26, h29, h31, b3_0_0, i100000_0, i100001_1, i100003_0, i100004_0, i100005_1]
              ·
                linarith only [z9, z10, z12, h16, h17, h19, h22, h25, h32, b1_0_0, i100000_0, i100001_1, i100003_0, i100004_1]
            ·
              linarith only [z5, z6, z12, h16, h17, h19, h21, h25, h26, h32, b1_0_0, b2_0_0, b3_0_0, i100000_0, i100001_1, i100003_1]
        ·
          have split100006:=uniformNatSplit (c 0) 1
          rcases split100006 with i100006_0 | i100006_1
          ·
            linarith only [h16, h18, h19, h21, h25, h30, h31, h32, b1_0_0, b3_0_0, i100006_0]
          ·
            have split100007:=uniformNatSplit (c 4) 0
            rcases split100007 with i100007_0 | i100007_1
            ·
              have split100008:=uniformNatSplit (c 2) 0
              rcases split100008 with i100008_0 | i100008_1
              ·
                have split100009:=uniformNatSplit (c 8) 0
                rcases split100009 with i100009_0 | i100009_1
                ·
                  have split100010:=uniformNatSplit (c 5) 0
                  rcases split100010 with i100010_0 | i100010_1
                  ·
                    linarith only [z8, h16, h17, h18, h23, h25, h27, h29, h30, h32, b1_0_0, b2_0_0, b3_0_0, i100007_0, i100008_0, i100010_0]
                  ·
                    linarith only [z4, h16, h17, h18, h21, h23, h27, h29, h30, h32, b1_0_0, b3_0_0, i100000_1, i100008_0, i100009_0, i100010_1]
                ·
                  linarith only [z9, h16, h17, h18, h23, h25, h27, h29, h30, h32, b1_0_0, b3_0_0, i100007_0, i100000_1, i100008_0, i100009_1]
              ·
                linarith only [z3, z12, h16, h17, h18, h19, h29, h32, b1_0_0, b3_0_0, i100006_1, i100000_1, i100008_1]
            ·
              linarith only [z5, z12, h16, h17, h18, h21, h27, h29, h32, b1_0_0, b3_0_0, i100006_1, i100000_1, i100007_1]
      ·
        have split100011:=uniformNatSplit (c 2) 0
        rcases split100011 with i100011_0 | i100011_1
        ·
          have split100012:=uniformNatSplit (c 1) 0
          rcases split100012 with i100012_0 | i100012_1
          ·
            linarith only [z4, z8, z12, h16, h17, h21, h25, h26, h27, h30, h31, b1_0_0, b2_0_0, i100011_0, b3_1_0, i100012_0]
          ·
            linarith only [h16, h17, h18, h21, h23, h25, h27, h29, h30, i100011_0, b3_1_0, i100012_1]
        ·
          have split100013:=uniformNatSplit (c 1) 0
          rcases split100013 with i100013_0 | i100013_1
          ·
            linarith only [z4, z8, z15, h16, h17, h19, h21, h22, h25, h26, h30, h31, b2_0_0, b3_1_0, i100013_0, i100011_1]
          ·
            linarith only [z3, h16, h17, h18, h19, h21, h25, h29, h30, h31, b3_1_0, i100013_1, i100011_1]
      ·
        linarith only [z6, h16, h17, h19, h21, h23, h25, h27, h28, h29, h32, b1_0_0, b2_0_0, b3_2_0]
      · exact bad3
    ·
      have split7:=uniformTemporalCases h37
      rcases split7 with b7_0_0 | b7_1_0 | b7_2_0 | bad7
      ·
        have split100014:=uniformNatSplit (c 2) 0
        rcases split100014 with i100014_0 | i100014_1
        ·
          have split100015:=uniformNatSplit (c 1) 0
          rcases split100015 with i100015_0 | i100015_1
          ·
            linarith only [z2, z4, z8, z11, z15, h16, h17, h19, h21, h25, h26, h30, h31, b1_0_0, b2_1_0, b7_0_0, i100015_0]
          ·
            linarith only [h16, h17, h18, h21, h23, h25, h27, h29, h30, b2_1_0, i100014_0, i100015_1]
        ·
          linarith only [z3, h16, h17, h18, h19, h21, h25, h26, h29, h30, h31, b1_0_0, b2_1_0, b7_0_0, i100014_1]
      ·
        linarith only [z3, z5, z7, z8, z15, h16, h17, h18, h19, h21, h23, h25, h31, b2_1_0, b7_1_0]
      ·
        linarith only [z12, h16, h17, h19, h21, h22, h23, h25, h27, h29, h30, h32, b1_0_0, b7_2_0]
      · exact bad7
    ·
      linarith only [z2, h16, h17, h19, h20, h21, h25, h28, h29, h31, h32, b1_0_0, b2_2_0]
    · exact bad2
  ·
    have split12:=uniformTemporalCases h37
    rcases split12 with b12_0_0 | b12_1_0 | b12_2_0 | bad12
    ·
      have split100016:=uniformNatSplit (c 1) 0
      rcases split100016 with i100016_0 | i100016_1
      ·
        linarith only [z8, z11, z12, z15, h16, h17, h19, h21, h23, h25, h26, h29, h30, b1_1_0, b12_0_0, i100016_0]
      ·
        have split100017:=uniformNatSplit (c 2) 0
        rcases split100017 with i100017_0 | i100017_1
        ·
          linarith only [h16, h17, h18, h21, h23, h25, h27, h29, h30, b1_1_0, i100017_0, i100016_1]
        ·
          linarith only [z3, z7, z11, z12, h16, h17, h18, h19, h21, h25, h29, b1_1_0, i100017_1, i100016_1]
    ·
      linarith only [z7, z15, h16, h17, h18, h19, h21, h23, h25, h26, h27, h29, h31, b1_1_0, b12_1_0]
    ·
      linarith only [z3, z11, h16, h17, h19, h21, h22, h23, h25, h27, h29, h30, h31, b1_1_0, b12_2_0]
    · exact bad12
  ·
    have split100018:=uniformNatSplit (c 3) 0
    rcases split100018 with i100018_0 | i100018_1
    ·
      linarith only [h16, h17, h19, h21, h23, h24, h25, h27, h28, h29, h31, b1_2_0, i100018_0]
    ·
      linarith only [h16, h17, h19, h20, h21, h23, h25, h27, h29, h31, h32, i100018_1, b1_2_0]
  · exact bad1
lemma no_profile_small {r:ℕ} (hr:r≤4) (c:Fin (2^r)→ℕ):
    ¬ profile r (r+7) c:=by
  intro h
  interval_cases r
  · exact uniform0NatProfileFalse c (profile_explicit0 c h)
  · exact uniform1NatProfileFalse c (profile_explicit1 c h)
  · exact uniform2NatProfileFalse c (profile_explicit2 c h)
  · exact uniform3NatProfileFalse c (profile_explicit3 c h)
  · exact uniformDpll4False c (profile_explicit4 c h)
end Az
namespace Helper4ClosingCertificate
open scoped BigOperators
def credit:List ℕ→ℕ→ℕ
  | [], _=>0
  | c::cs, m=>(if m.testBit 0 then c else 0)+credit cs (m / 2)
def weight (m:ℕ):ℕ:=2^(5 - credit [1, 1, 1, 1, 1] m)
def totalWeight (rows:List ℕ):ℕ:=(rows.map weight).sum
def uniformWeight (sub:ℕ) (rows:List ℕ):ℕ:=
  (rows.map fun m=>if Nat.land m sub=sub then
    weight m*2^(credit [1, 1, 1, 1, 1] sub+1) else 0).sum
def profileTable:List (List ℕ):=
  [
    [],
    [1],
    [3],
    [5],
    [7],
    [9],
    [11],
    [13],
    [15],
    [17],
    [19],
    [21],
    [23],
    [25],
    [27],
    [29],
    [31],
    [1, 1],
    [1, 3],
    [1, 5],
    [1, 7],
    [1, 9],
    [1, 11],
    [1, 13],
    [1, 15],
    [1, 17],
    [1, 19],
    [1, 21],
    [1, 23],
    [1, 25],
    [1, 27],
    [1, 29],
    [1, 31],
    [3, 3],
    [3, 5],
    [3, 7],
    [3, 9],
    [3, 11],
    [3, 13],
    [3, 15],
    [3, 17],
    [3, 19],
    [3, 21],
    [3, 23],
    [3, 25],
    [3, 27],
    [3, 29],
    [3, 31],
    [5, 5],
    [5, 7],
    [5, 9],
    [5, 11],
    [5, 13],
    [5, 15],
    [5, 17],
    [5, 19],
    [5, 21],
    [5, 23],
    [5, 25],
    [5, 27],
    [5, 29],
    [5, 31],
    [7, 7],
    [7, 9],
    [7, 11],
    [7, 13],
    [7, 15],
    [7, 17],
    [7, 19],
    [7, 21],
    [7, 23],
    [7, 25],
    [7, 27],
    [7, 29],
    [7, 31],
    [9, 9],
    [9, 11],
    [9, 13],
    [9, 15],
    [9, 17],
    [9, 19],
    [9, 21],
    [9, 23],
    [9, 25],
    [9, 27],
    [9, 29],
    [9, 31],
    [11, 11],
    [11, 13],
    [11, 15],
    [11, 17],
    [11, 19],
    [11, 21],
    [11, 23],
    [11, 25],
    [11, 27],
    [11, 29],
    [11, 31],
    [13, 13],
    [13, 15],
    [13, 17],
    [13, 19],
    [13, 21],
    [13, 23],
    [13, 25],
    [13, 27],
    [13, 29],
    [13, 31],
    [15, 15],
    [15, 17],
    [15, 19],
    [15, 21],
    [15, 23],
    [15, 25],
    [15, 27],
    [15, 29],
    [15, 31],
    [17, 17],
    [17, 19],
    [17, 21],
    [17, 23],
    [17, 25],
    [17, 27],
    [17, 29],
    [17, 31],
    [19, 19],
    [19, 21],
    [19, 23],
    [19, 25],
    [19, 27],
    [19, 29],
    [19, 31],
    [21, 21],
    [21, 23],
    [21, 25],
    [21, 27],
    [21, 29],
    [21, 31],
    [23, 23],
    [23, 25],
    [23, 27],
    [23, 29],
    [23, 31],
    [25, 25],
    [25, 27],
    [25, 29],
    [25, 31],
    [27, 27],
    [27, 29],
    [27, 31],
    [29, 29],
    [29, 31],
    [31, 31],
    [1, 3, 5],
    [1, 3, 9],
    [1, 3, 13],
    [1, 3, 17],
    [1, 3, 21],
    [1, 3, 25],
    [1, 3, 29],
    [1, 5, 9],
    [1, 5, 11],
    [1, 5, 17],
    [1, 5, 19],
    [1, 5, 25],
    [1, 5, 27],
    [1, 7, 9],
    [1, 7, 17],
    [1, 7, 25],
    [1, 9, 17],
    [1, 9, 19],
    [1, 9, 21],
    [1, 9, 23],
    [1, 11, 13],
    [1, 11, 17],
    [1, 11, 21],
    [1, 11, 29],
    [1, 13, 17],
    [1, 13, 19],
    [1, 13, 27],
    [1, 15, 17],
    [1, 19, 21],
    [1, 19, 25],
    [1, 19, 29],
    [1, 21, 25],
    [1, 21, 27],
    [1, 23, 25],
    [1, 27, 29],
    [3, 5, 9],
    [3, 5, 17],
    [3, 5, 25],
    [3, 7, 11],
    [3, 7, 19],
    [3, 7, 27],
    [3, 9, 17],
    [3, 9, 21],
    [3, 11, 19],
    [3, 11, 23],
    [3, 13, 17],
    [3, 15, 19],
    [3, 21, 25],
    [3, 23, 27],
    [5, 7, 13],
    [5, 7, 21],
    [5, 7, 29],
    [5, 9, 17],
    [5, 9, 19],
    [5, 11, 17],
    [5, 13, 21],
    [5, 13, 23],
    [5, 15, 21],
    [5, 19, 25],
    [5, 23, 29],
    [7, 9, 17],
    [7, 11, 19],
    [7, 13, 21],
    [7, 15, 23],
    [9, 11, 13],
    [9, 11, 25],
    [9, 11, 29],
    [9, 13, 25],
    [9, 13, 27],
    [9, 15, 25],
    [9, 19, 21],
    [9, 27, 29],
    [11, 13, 17],
    [11, 13, 25],
    [11, 15, 27],
    [13, 15, 29],
    [17, 19, 21],
    [17, 19, 25],
    [17, 19, 29],
    [17, 21, 25],
    [17, 21, 27],
    [17, 23, 25],
    [17, 27, 29],
    [19, 21, 25],
    [19, 23, 27],
    [21, 23, 29],
    [25, 27, 29],
    [1, 3, 21, 25],
    [1, 5, 19, 25],
    [1, 9, 19, 21],
    [1, 11, 13, 17],
    [1, 19, 21, 25],
    [3, 5, 9, 17],
    [],
    [2],
    [6],
    [10],
    [14],
    [18],
    [22],
    [26],
    [30],
    [2, 2],
    [2, 6],
    [2, 10],
    [2, 14],
    [2, 18],
    [2, 22],
    [2, 26],
    [2, 30],
    [6, 6],
    [6, 10],
    [6, 14],
    [6, 18],
    [6, 22],
    [6, 26],
    [6, 30],
    [10, 10],
    [10, 14],
    [10, 18],
    [10, 22],
    [10, 26],
    [10, 30],
    [14, 14],
    [14, 18],
    [14, 22],
    [14, 26],
    [14, 30],
    [18, 18],
    [18, 22],
    [18, 26],
    [18, 30],
    [22, 22],
    [22, 26],
    [22, 30],
    [26, 26],
    [26, 30],
    [30, 30],
    [2, 6, 10],
    [2, 6, 18],
    [2, 6, 26],
    [2, 10, 18],
    [2, 10, 22],
    [2, 14, 18],
    [2, 22, 26],
    [6, 10, 18],
    [6, 14, 22],
    [10, 14, 26],
    [18, 22, 26],
    [],
    [4],
    [12],
    [20],
    [28],
    [4, 4],
    [4, 12],
    [4, 20],
    [4, 28],
    [12, 12],
    [12, 20],
    [12, 28],
    [20, 20],
    [20, 28],
    [28, 28],
    [4, 12, 20],
    [],
    [8],
    [24],
    [8, 8],
    [8, 24],
    [24, 24],
    [],
    [16],
    [16, 16]
  ]
def groupTable:List ℕ:=[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4]
def profile (p:Fin 327):List ℕ:=profileTable[p.val]!
def groupIndex (p:Fin 327):ℕ:=groupTable[p.val]!
def groupCost (j:ℕ):ℕ:=[23472, 23520, 11504, 1344, 0][j]!
def compatibilityCoefficients:List ℕ:=[3600, 4384, 64, 1616, 944, 2608, 1600, 912, 1856, 1344, 1344, 1376, 1008, 2320, 2384, 336, 976, 3360]
def compatibilityCoefficient (r:Fin 18):ℕ:=compatibilityCoefficients[r.val]!
def compatibilityTable:List (ℕ × ℕ × List ℕ):=
  [
    (280, 0, [3, 7, 11, 19, 23, 27, 31]),
    (299, 0, [3, 11, 15, 19, 23, 27, 31]),
    (300, 0, [3, 7, 15, 19, 23, 27, 31]),
    (313, 0, [5, 6, 7, 21, 22, 23, 29, 30, 31]),
    (315, 1, [5, 6, 7, 13, 14, 15, 29, 30, 31]),
    (316, 0, [5, 6, 7, 13, 14, 15, 21, 22, 23, 29, 30, 31]),
    (316, 1, [5, 6, 7, 13, 14, 15, 21, 22, 23, 29, 30, 31]),
    (317, 0, [13, 14, 15, 21, 22, 23, 29, 30, 31]),
    (317, 1, [13, 14, 15, 21, 22, 23, 29, 30, 31]),
    (321, 0, [9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31]),
    (322, 1, [25, 26, 27, 28, 29, 30, 31]),
    (323, 0, [9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31]),
    (323, 1, [9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31]),
    (323, 2, [9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31]),
    (326, 0, [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
    (326, 1, [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
    (326, 2, [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
    (326, 3, [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])
  ]
def compatibilityRow (r:Fin 18) (p:Fin 327):ℕ:=
  let data:=compatibilityTable[r.val]!
  if p.val=data.1 then 1 else
    if groupIndex p=data.2.1 && (profile p).any (fun m=>decide (m∈data.2.2))
      then 1 else 0
def columnCost (p:Fin 327):ℕ:=
  504*totalWeight (profile p)+57*uniformWeight 4 (profile p)+
    105*uniformWeight 8 (profile p)+126*uniformWeight 16 (profile p)+
    (∑ r:Fin 18, compatibilityCoefficient r*compatibilityRow r p)+
    groupCost (groupIndex p)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma column_certificate:∀ p:Fin 327, 16128*(profile p).length≤columnCost p:=by
  intro p
  fin_cases p <;> decide+kernel
lemma profile_count_bound
    (f:Fin 5→Fin 327) (z:ℕ)
    (hg:∀ j:Fin 5, groupIndex (f j)=j.val)
    (hw:32*z+∑ j:Fin 5, totalWeight (profile (f j))≤128)
    (hu4:(∑ j:Fin 5, uniformWeight 4 (profile (f j)))≤128)
    (hu8:(∑ j:Fin 5, uniformWeight 8 (profile (f j)))≤128)
    (hu16:(∑ j:Fin 5, uniformWeight 16 (profile (f j)))≤128)
    (hc:∀ r:Fin 18, (∑ j:Fin 5, compatibilityRow r (f j))≤1):
    z+(∑ j:Fin 5, (profile (f j)).length)≤11:=by
  have hs:=Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin 5)))=>
    column_certificate (f j))
  have hcompat:
      (∑ j:Fin 5, ∑ r:Fin 18, compatibilityCoefficient r*compatibilityRow r (f j))≤
        ∑ r:Fin 18, compatibilityCoefficient r:=by
    calc
      _=∑ r:Fin 18, compatibilityCoefficient r*
          (∑ j:Fin 5, compatibilityRow r (f j)):=by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
      _≤∑ r:Fin 18, compatibilityCoefficient r*1:=
        Finset.sum_le_sum (fun r _=>Nat.mul_le_mul_left _ (hc r))
      _=_:=by simp
  have hz:(∑ j:Fin 5, groupCost (groupIndex (f j)))=59840:=by
    simp_rw [hg]
    decide+kernel
  have hcoeff:(∑ r:Fin 18, compatibilityCoefficient r)=32032:=by
    decide+kernel
  rw [hcoeff] at hcompat
  unfold columnCost at hs
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [hz] at hs
  clear hg hc hz hcoeff
  omega
end Helper4ClosingCertificate
namespace Helper4ProfileMembership
def credit:List ℕ→ℕ→ℕ
  | [], _=>0
  | c::cs, m=>(if m.testBit 0 then c else 0)+credit cs (m / 2)
def weight (cs:List ℕ) (m:ℕ):ℕ:=2^(cs.sum - credit cs m)
def totalWeight (cs rows:List ℕ):ℕ:=(rows.map (weight cs)).sum
def residual (cs:List ℕ) (j k:ℕ) (rows:List ℕ):ℕ:=
  (rows.map fun m=>if m.testBit k then
    weight cs m*2^cs[k]!*(if j=k then 2 else 1) else 0).sum
def covered (b j:ℕ) (rows:List ℕ):ℕ:=
  (rows.filter fun m=>(List.range b).any fun k=>
    decide (j < k) && m.testBit k &&
      decide ((rows.filter fun q=>q.testBit k).length=1)).length
def good (cs:List ℕ) (j:ℕ) (rows:List ℕ):Bool:=
  (decide (rows.length≤2) || decide (rows.length≤covered cs.length j rows+1)) &&
  decide (totalWeight cs rows≤2^(cs.sum+2)) &&
  (List.range cs.length).all fun k=>decide (residual cs j k rows≤2^(cs.sum+2))
def encoded (j:ℕ) (entries:List ℕ):List ℕ:=
  entries.filterMap fun a=>if a=0 then none else some (2^j*(2*a - 1))
def columnCount (rows:List ℕ) (k:ℕ):ℕ:=
  (rows.filter fun m=>m.testBit k).length
def temporal (b j:ℕ) (rows:List ℕ):Bool:=
  rows.all fun m=>
    match (List.range b).find? (fun k=>decide (j < k) && m.testBit k &&
        decide (columnCount rows k < rows.length)) with
    | none=>true
    | some k=>decide (columnCount rows k=1)
def introducedBefore (b j k:ℕ) (rows:List ℕ) (m:ℕ):Bool:=
  (List.range b).any fun l=>decide (j < l∧l < k) && m.testBit l &&
    decide (columnCount rows l=1∧1 < rows.length)
def insensitiveFull (b j k:ℕ) (rows:List ℕ):Bool:=
  decide (columnCount rows k=rows.length) &&
    !(rows.all (introducedBefore b j k rows))
def effectiveCredit (cs:List ℕ) (j:ℕ) (rows:List ℕ) (m:ℕ):ℕ:=
  ((List.range cs.length).map fun k=>
    if decide (j < k) && m.testBit k && !(insensitiveFull cs.length j k rows)
      then cs[k]! else 0).sum
def effectiveKraft (cs:List ℕ) (j:ℕ) (rows:List ℕ):Bool:=
  decide ((rows.map fun m=>2^(cs.sum - effectiveCredit cs j rows m)).sum≤
    2^(cs.sum+1))
def strongGood (j:ℕ) (rows:List ℕ):Bool:=
  good [1, 1, 1, 1, 1] j rows && temporal 5 j rows &&
    effectiveKraft [1, 1, 1, 1, 1] j rows
def profiles0:List (List ℕ):=
  [
    [],
    [1],
    [3],
    [5],
    [7],
    [9],
    [11],
    [13],
    [15],
    [17],
    [19],
    [21],
    [23],
    [25],
    [27],
    [29],
    [31],
    [1, 1],
    [1, 3],
    [1, 5],
    [1, 7],
    [1, 9],
    [1, 11],
    [1, 13],
    [1, 15],
    [1, 17],
    [1, 19],
    [1, 21],
    [1, 23],
    [1, 25],
    [1, 27],
    [1, 29],
    [1, 31],
    [3, 3],
    [3, 5],
    [3, 7],
    [3, 9],
    [3, 11],
    [3, 13],
    [3, 15],
    [3, 17],
    [3, 19],
    [3, 21],
    [3, 23],
    [3, 25],
    [3, 27],
    [3, 29],
    [3, 31],
    [5, 5],
    [5, 7],
    [5, 9],
    [5, 11],
    [5, 13],
    [5, 15],
    [5, 17],
    [5, 19],
    [5, 21],
    [5, 23],
    [5, 25],
    [5, 27],
    [5, 29],
    [5, 31],
    [7, 7],
    [7, 9],
    [7, 11],
    [7, 13],
    [7, 15],
    [7, 17],
    [7, 19],
    [7, 21],
    [7, 23],
    [7, 25],
    [7, 27],
    [7, 29],
    [7, 31],
    [9, 9],
    [9, 11],
    [9, 13],
    [9, 15],
    [9, 17],
    [9, 19],
    [9, 21],
    [9, 23],
    [9, 25],
    [9, 27],
    [9, 29],
    [9, 31],
    [11, 11],
    [11, 13],
    [11, 15],
    [11, 17],
    [11, 19],
    [11, 21],
    [11, 23],
    [11, 25],
    [11, 27],
    [11, 29],
    [11, 31],
    [13, 13],
    [13, 15],
    [13, 17],
    [13, 19],
    [13, 21],
    [13, 23],
    [13, 25],
    [13, 27],
    [13, 29],
    [13, 31],
    [15, 15],
    [15, 17],
    [15, 19],
    [15, 21],
    [15, 23],
    [15, 25],
    [15, 27],
    [15, 29],
    [15, 31],
    [17, 17],
    [17, 19],
    [17, 21],
    [17, 23],
    [17, 25],
    [17, 27],
    [17, 29],
    [17, 31],
    [19, 19],
    [19, 21],
    [19, 23],
    [19, 25],
    [19, 27],
    [19, 29],
    [19, 31],
    [21, 21],
    [21, 23],
    [21, 25],
    [21, 27],
    [21, 29],
    [21, 31],
    [23, 23],
    [23, 25],
    [23, 27],
    [23, 29],
    [23, 31],
    [25, 25],
    [25, 27],
    [25, 29],
    [25, 31],
    [27, 27],
    [27, 29],
    [27, 31],
    [29, 29],
    [29, 31],
    [31, 31],
    [1, 3, 5],
    [1, 3, 9],
    [1, 3, 13],
    [1, 3, 17],
    [1, 3, 21],
    [1, 3, 25],
    [1, 3, 29],
    [1, 5, 9],
    [1, 5, 11],
    [1, 5, 17],
    [1, 5, 19],
    [1, 5, 25],
    [1, 5, 27],
    [1, 7, 9],
    [1, 7, 17],
    [1, 7, 25],
    [1, 9, 17],
    [1, 9, 19],
    [1, 9, 21],
    [1, 9, 23],
    [1, 11, 13],
    [1, 11, 17],
    [1, 11, 21],
    [1, 11, 29],
    [1, 13, 17],
    [1, 13, 19],
    [1, 13, 27],
    [1, 15, 17],
    [1, 19, 21],
    [1, 19, 25],
    [1, 19, 29],
    [1, 21, 25],
    [1, 21, 27],
    [1, 23, 25],
    [1, 27, 29],
    [3, 5, 9],
    [3, 5, 17],
    [3, 5, 25],
    [3, 7, 11],
    [3, 7, 19],
    [3, 7, 27],
    [3, 9, 17],
    [3, 9, 21],
    [3, 11, 19],
    [3, 11, 23],
    [3, 13, 17],
    [3, 15, 19],
    [3, 21, 25],
    [3, 23, 27],
    [5, 7, 13],
    [5, 7, 21],
    [5, 7, 29],
    [5, 9, 17],
    [5, 9, 19],
    [5, 11, 17],
    [5, 13, 21],
    [5, 13, 23],
    [5, 15, 21],
    [5, 19, 25],
    [5, 23, 29],
    [7, 9, 17],
    [7, 11, 19],
    [7, 13, 21],
    [7, 15, 23],
    [9, 11, 13],
    [9, 11, 25],
    [9, 11, 29],
    [9, 13, 25],
    [9, 13, 27],
    [9, 15, 25],
    [9, 19, 21],
    [9, 27, 29],
    [11, 13, 17],
    [11, 13, 25],
    [11, 15, 27],
    [13, 15, 29],
    [17, 19, 21],
    [17, 19, 25],
    [17, 19, 29],
    [17, 21, 25],
    [17, 21, 27],
    [17, 23, 25],
    [17, 27, 29],
    [19, 21, 25],
    [19, 23, 27],
    [21, 23, 29],
    [25, 27, 29],
    [1, 3, 21, 25],
    [1, 5, 19, 25],
    [1, 9, 19, 21],
    [1, 11, 13, 17],
    [1, 19, 21, 25],
    [3, 5, 9, 17]
  ]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma profiles0_complete:∀ a:Fin 17, ∀ b:Fin 17, a.val≤b.val→∀ c:Fin 17, b.val≤c.val→∀ d:Fin 17, c.val≤d.val→∀ e:Fin 17, d.val≤e.val→
    strongGood 0 (encoded 0 [a.val, b.val, c.val, d.val, e.val])=true→(encoded 0 [a.val, b.val, c.val, d.val, e.val])∈profiles0:=by
  intro a b
  fin_cases a <;> fin_cases b <;> decide+kernel
def profiles1:List (List ℕ):=
  [
    [],
    [2],
    [6],
    [10],
    [14],
    [18],
    [22],
    [26],
    [30],
    [2, 2],
    [2, 6],
    [2, 10],
    [2, 14],
    [2, 18],
    [2, 22],
    [2, 26],
    [2, 30],
    [6, 6],
    [6, 10],
    [6, 14],
    [6, 18],
    [6, 22],
    [6, 26],
    [6, 30],
    [10, 10],
    [10, 14],
    [10, 18],
    [10, 22],
    [10, 26],
    [10, 30],
    [14, 14],
    [14, 18],
    [14, 22],
    [14, 26],
    [14, 30],
    [18, 18],
    [18, 22],
    [18, 26],
    [18, 30],
    [22, 22],
    [22, 26],
    [22, 30],
    [26, 26],
    [26, 30],
    [30, 30],
    [2, 6, 10],
    [2, 6, 18],
    [2, 6, 26],
    [2, 10, 18],
    [2, 10, 22],
    [2, 14, 18],
    [2, 22, 26],
    [6, 10, 18],
    [6, 14, 22],
    [10, 14, 26],
    [18, 22, 26]
  ]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma profiles1_complete:∀ a:Fin 9, ∀ b:Fin 9, a.val≤b.val→∀ c:Fin 9, b.val≤c.val→∀ d:Fin 9, c.val≤d.val→
    strongGood 1 (encoded 1 [a.val, b.val, c.val, d.val])=true→(encoded 1 [a.val, b.val, c.val, d.val])∈profiles1:=by
  intro a
  fin_cases a <;> decide+kernel
def profiles2:List (List ℕ):=
  [
    [],
    [4],
    [12],
    [20],
    [28],
    [4, 4],
    [4, 12],
    [4, 20],
    [4, 28],
    [12, 12],
    [12, 20],
    [12, 28],
    [20, 20],
    [20, 28],
    [28, 28],
    [4, 12, 20]
  ]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma profiles2_complete:∀ a:Fin 5, ∀ b:Fin 5, a.val≤b.val→∀ c:Fin 5, b.val≤c.val→
    strongGood 2 (encoded 2 [a.val, b.val, c.val])=true→(encoded 2 [a.val, b.val, c.val])∈profiles2:=by
  decide+kernel
def profiles3:List (List ℕ):=
  [
    [],
    [8],
    [24],
    [8, 8],
    [8, 24],
    [24, 24]
  ]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma profiles3_complete:∀ a:Fin 3, ∀ b:Fin 3, a.val≤b.val→
    strongGood 3 (encoded 3 [a.val, b.val])=true→(encoded 3 [a.val, b.val])∈profiles3:=by
  decide+kernel
def profiles4:List (List ℕ):=
  [
    [],
    [16],
    [16, 16]
  ]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma profiles4_complete:∀ a:Fin 2, ∀ b:Fin 2, a.val≤b.val→
    strongGood 4 (encoded 4 [a.val, b.val])=true→(encoded 4 [a.val, b.val])∈profiles4:=by
  decide+kernel
end Helper4ProfileMembership
namespace Helper4CombinedCertificate
open scoped BigOperators
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma table_block0:∀ i:Fin 246,
    Helper4ClosingCertificate.groupIndex (⟨0+i.val, by omega⟩:Fin 327)=0∧
      Helper4ClosingCertificate.profile (⟨0+i.val, by omega⟩:Fin 327)=
        Helper4ProfileMembership.profiles0[i.val]'(by change i.val < 246; exact i.isLt):=by
  intro i
  fin_cases i <;> decide+kernel
set_option maxRecDepth 100000 in
lemma locate0 (rows:List ℕ) (hmem:rows∈Helper4ProfileMembership.profiles0):
    ∃ p:Fin 327, Helper4ClosingCertificate.groupIndex p=0∧
      Helper4ClosingCertificate.profile p=rows:=by
  obtain ⟨i, hi, hrow⟩:=List.mem_iff_getElem.mp hmem
  have hib:i < 246:=by change i < 246 at hi; exact hi
  have ht:=table_block0 ⟨i, hib⟩
  exact ⟨⟨0+i, by omega⟩, ht.1, ht.2.trans hrow⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma table_block1:∀ i:Fin 56,
    Helper4ClosingCertificate.groupIndex (⟨246+i.val, by omega⟩:Fin 327)=1∧
      Helper4ClosingCertificate.profile (⟨246+i.val, by omega⟩:Fin 327)=
        Helper4ProfileMembership.profiles1[i.val]'(by change i.val < 56; exact i.isLt):=by
  intro i
  fin_cases i <;> decide+kernel
set_option maxRecDepth 100000 in
lemma locate1 (rows:List ℕ) (hmem:rows∈Helper4ProfileMembership.profiles1):
    ∃ p:Fin 327, Helper4ClosingCertificate.groupIndex p=1∧
      Helper4ClosingCertificate.profile p=rows:=by
  obtain ⟨i, hi, hrow⟩:=List.mem_iff_getElem.mp hmem
  have hib:i < 56:=by change i < 56 at hi; exact hi
  have ht:=table_block1 ⟨i, hib⟩
  exact ⟨⟨246+i, by omega⟩, ht.1, ht.2.trans hrow⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma table_block2:∀ i:Fin 16,
    Helper4ClosingCertificate.groupIndex (⟨302+i.val, by omega⟩:Fin 327)=2∧
      Helper4ClosingCertificate.profile (⟨302+i.val, by omega⟩:Fin 327)=
        Helper4ProfileMembership.profiles2[i.val]'(by change i.val < 16; exact i.isLt):=by
  intro i
  fin_cases i <;> decide+kernel
set_option maxRecDepth 100000 in
lemma locate2 (rows:List ℕ) (hmem:rows∈Helper4ProfileMembership.profiles2):
    ∃ p:Fin 327, Helper4ClosingCertificate.groupIndex p=2∧
      Helper4ClosingCertificate.profile p=rows:=by
  obtain ⟨i, hi, hrow⟩:=List.mem_iff_getElem.mp hmem
  have hib:i < 16:=by change i < 16 at hi; exact hi
  have ht:=table_block2 ⟨i, hib⟩
  exact ⟨⟨302+i, by omega⟩, ht.1, ht.2.trans hrow⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma table_block3:∀ i:Fin 6,
    Helper4ClosingCertificate.groupIndex (⟨318+i.val, by omega⟩:Fin 327)=3∧
      Helper4ClosingCertificate.profile (⟨318+i.val, by omega⟩:Fin 327)=
        Helper4ProfileMembership.profiles3[i.val]'(by change i.val < 6; exact i.isLt):=by
  intro i
  fin_cases i <;> decide+kernel
set_option maxRecDepth 100000 in
lemma locate3 (rows:List ℕ) (hmem:rows∈Helper4ProfileMembership.profiles3):
    ∃ p:Fin 327, Helper4ClosingCertificate.groupIndex p=3∧
      Helper4ClosingCertificate.profile p=rows:=by
  obtain ⟨i, hi, hrow⟩:=List.mem_iff_getElem.mp hmem
  have hib:i < 6:=by change i < 6 at hi; exact hi
  have ht:=table_block3 ⟨i, hib⟩
  exact ⟨⟨318+i, by omega⟩, ht.1, ht.2.trans hrow⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma table_block4:∀ i:Fin 3,
    Helper4ClosingCertificate.groupIndex (⟨324+i.val, by omega⟩:Fin 327)=4∧
      Helper4ClosingCertificate.profile (⟨324+i.val, by omega⟩:Fin 327)=
        Helper4ProfileMembership.profiles4[i.val]'(by change i.val < 3; exact i.isLt):=by
  intro i
  fin_cases i <;> decide+kernel
set_option maxRecDepth 100000 in
lemma locate4 (rows:List ℕ) (hmem:rows∈Helper4ProfileMembership.profiles4):
    ∃ p:Fin 327, Helper4ClosingCertificate.groupIndex p=4∧
      Helper4ClosingCertificate.profile p=rows:=by
  obtain ⟨i, hi, hrow⟩:=List.mem_iff_getElem.mp hmem
  have hib:i < 3:=by change i < 3 at hi; exact hi
  have ht:=table_block4 ⟨i, hib⟩
  exact ⟨⟨324+i, by omega⟩, ht.1, ht.2.trans hrow⟩
def sourceGroups:List ℕ:=[1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4]
def sourceProfiles:List (List ℕ):=[[14, 30], [6, 14, 22], [10, 14, 26], [12, 28], [20, 28], [28, 28], [28, 28], [4, 12, 20], [4, 12, 20], [8, 8], [8, 24], [24, 24], [24, 24], [24, 24], [16, 16], [16, 16], [16, 16], [16, 16]]
def rowClause (r:Fin 18) (j:ℕ) (rows:List ℕ):ℕ:=
  let data:=Helper4ClosingCertificate.compatibilityTable[r.val]!
  if j=sourceGroups[r.val]! && rows=sourceProfiles[r.val]! then 1 else
    if j=data.2.1 && rows.any (fun m=>decide (m∈data.2.2)) then 1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma row_clause_eq:∀ r:Fin 18, ∀ p:Fin 327,
    rowClause r (Helper4ClosingCertificate.groupIndex p)
      (Helper4ClosingCertificate.profile p)=Helper4ClosingCertificate.compatibilityRow r p:=by
  intro r
  fin_cases r <;> decide+kernel
def Canonical0 (rows:List ℕ):Prop:=
  ∃ a b c d e:Fin 17, a.val≤b.val∧b.val≤c.val∧c.val≤d.val∧d.val≤e.val∧rows=Helper4ProfileMembership.encoded 0 [a.val, b.val, c.val, d.val, e.val]
def Canonical1 (rows:List ℕ):Prop:=
  ∃ a b c d:Fin 9, a.val≤b.val∧b.val≤c.val∧c.val≤d.val∧rows=Helper4ProfileMembership.encoded 1 [a.val, b.val, c.val, d.val]
def Canonical2 (rows:List ℕ):Prop:=
  ∃ a b c:Fin 5, a.val≤b.val∧b.val≤c.val∧rows=Helper4ProfileMembership.encoded 2 [a.val, b.val, c.val]
def Canonical3 (rows:List ℕ):Prop:=
  ∃ a b:Fin 3, a.val≤b.val∧rows=Helper4ProfileMembership.encoded 3 [a.val, b.val]
def Canonical4 (rows:List ℕ):Prop:=
  ∃ a b:Fin 2, a.val≤b.val∧rows=Helper4ProfileMembership.encoded 4 [a.val, b.val]
def Canonical (j:Fin 5) (rows:List ℕ):Prop:=
  match j.val with
  | 0=>Canonical0 rows
  | 1=>Canonical1 rows
  | 2=>Canonical2 rows
  | 3=>Canonical3 rows
  | _=>Canonical4 rows
set_option maxRecDepth 100000 in
lemma canonical_locates (j:Fin 5) (rows:List ℕ)
    (hcan:Canonical j rows)
    (hgood:Helper4ProfileMembership.strongGood j.val rows=true):
    ∃ p:Fin 327, Helper4ClosingCertificate.groupIndex p=j.val∧
      Helper4ClosingCertificate.profile p=rows:=by
  fin_cases j
  · obtain ⟨a, b, c, d, e, h0, h1, h2, h3, rfl⟩:=hcan
    apply locate0
    exact Helper4ProfileMembership.profiles0_complete a b h0 c h1 d h2 e h3 hgood
  · obtain ⟨a, b, c, d, h0, h1, h2, rfl⟩:=hcan
    apply locate1
    exact Helper4ProfileMembership.profiles1_complete a b h0 c h1 d h2 hgood
  · obtain ⟨a, b, c, h0, h1, rfl⟩:=hcan
    apply locate2
    exact Helper4ProfileMembership.profiles2_complete a b h0 c h1 hgood
  · obtain ⟨a, b, h0, rfl⟩:=hcan
    apply locate3
    exact Helper4ProfileMembership.profiles3_complete a b h0 hgood
  · obtain ⟨a, b, h0, rfl⟩:=hcan
    apply locate4
    exact Helper4ProfileMembership.profiles4_complete a b h0 hgood
lemma canonical_mask_bound
    (rows:Fin 5→List ℕ) (z:ℕ)
    (hcan:∀ j:Fin 5, Canonical j (rows j))
    (hgood:∀ j:Fin 5, Helper4ProfileMembership.strongGood j.val (rows j)=true)
    (hw:32*z+∑ j:Fin 5, Helper4ClosingCertificate.totalWeight (rows j)≤128)
    (hu4:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 4 (rows j))≤128)
    (hu8:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 8 (rows j))≤128)
    (hu16:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 16 (rows j))≤128)
    (hc:∀ r:Fin 18, (∑ j:Fin 5, rowClause r j.val (rows j))≤1):
    z+(∑ j:Fin 5, (rows j).length)≤11:=by
  classical
  have hl:∀ j:Fin 5, ∃ p:Fin 327,
      Helper4ClosingCertificate.groupIndex p=j.val∧
        Helper4ClosingCertificate.profile p=rows j:=
    fun j=>canonical_locates j (rows j) (hcan j) (hgood j)
  let f:Fin 5→Fin 327:=fun j=>Classical.choose (hl j)
  have hg:∀ j:Fin 5, Helper4ClosingCertificate.groupIndex (f j)=j.val:=
    fun j=>(Classical.choose_spec (hl j)).1
  have hp:∀ j:Fin 5, Helper4ClosingCertificate.profile (f j)=rows j:=
    fun j=>(Classical.choose_spec (hl j)).2
  have hcc:∀ r:Fin 18,
      (∑ j:Fin 5, Helper4ClosingCertificate.compatibilityRow r (f j))≤1:=by
    intro r
    have heq:(∑ j:Fin 5, Helper4ClosingCertificate.compatibilityRow r (f j))=
        ∑ j:Fin 5, rowClause r j.val (rows j):=by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← row_clause_eq, hg, hp]
    rw [heq]
    exact hc r
  have hh:=Helper4ClosingCertificate.profile_count_bound f z hg
    (by simpa only [hp] using hw) (by simpa only [hp] using hu4)
    (by simpa only [hp] using hu8) (by simpa only [hp] using hu16) hcc
  simpa only [hp] using hh
end Helper4CombinedCertificate
namespace Helper4TemporalCore
def columnCount (rows:List ℕ) (k:ℕ):ℕ:=
  (rows.filter fun m=>m.testBit k).length
abbrev IntroProperty (b j:ℕ) (fresh IP:List ℕ):Prop:=
  ∀ m∈fresh, ∀ k:Fin b, j < k.val→m.testBit k.val=true→
    columnCount IP k.val < IP.length→
    ∃ l:Fin b, j < l.val∧l.val≤k.val∧m.testBit l.val=true∧
      columnCount IP l.val=1
def terminal (b j:ℕ) (IP:List ℕ) (m:ℕ):Bool:=
  decide (∀ k:Fin b, j < k.val→m.testBit k.val=true→
    columnCount IP k.val=IP.length)
abbrev TemporalProperty (b j:ℕ) (fresh IP:List ℕ):Prop:=
  IntroProperty b j fresh IP∧
    (3≤IP.length→(fresh.filter (terminal b j IP)).length≤1)
lemma column_le_length (rows:List ℕ) (k:ℕ):
    columnCount rows k≤rows.length:=List.length_filter_le _ _
lemma column_mono {small large:List ℕ} (h:small.Sublist large) (k:ℕ):
    columnCount small k≤columnCount large k:=
  by
    change (small.filter (fun m:ℕ=>m.testBit k)).length≤
      (large.filter (fun m:ℕ=>m.testBit k)).length
    exact (h.filter (fun m:ℕ=>m.testBit k)).length_le
lemma column_positive {rows:List ℕ} {m k:ℕ} (hm:m∈rows)
    (hk:m.testBit k=true):0 < columnCount rows k:=
  List.length_pos_of_mem (List.mem_filter.mpr ⟨hm, hk⟩)
lemma column_full_mono {small large:List ℕ} (h:small.Sublist large) (k:ℕ)
    (hf:columnCount large k=large.length):columnCount small k=small.length:=by
  apply List.length_filter_eq_length_iff.mpr
  intro m hm
  exact List.length_filter_eq_length_iff.mp hf m (h.subset hm)
lemma filter_length_mono (rows:List ℕ) (p q:ℕ→Bool)
    (h:∀ m∈rows, p m=true→q m=true):
    (rows.filter p).length≤(rows.filter q).length:=by
  induction rows with
  | nil=>simp
  | cons m rows ih=>
    have ht:∀ a∈rows, p a=true→q a=true:=
      fun a ha=>h a (by simp [ha])
    have hh:=ih ht
    have hm:=h m (by simp)
    cases hp:p m <;> cases hq:q m <;>
      simp_all
    omega
lemma temporal_restrict {b j:ℕ} {fresh small large:List ℕ}
    (hsub:small.Sublist large) (hfresh:fresh⊆small)
    (hsmall:3≤ small.length) (h:TemporalProperty b j fresh large):
    TemporalProperty b j fresh small:=by
  constructor
  · intro m hm k hj hk hproper
    have hproperLarge:columnCount large k.val < large.length:=by
      have hle:=column_le_length large k.val
      by_contra hnot
      have he:columnCount large k.val=large.length:=by omega
      have:=column_full_mono hsub k.val he
      omega
    obtain ⟨l, hjl, hlk, hml, hcol⟩:=h.1 m hm k hj hk hproperLarge
    refine ⟨l, hjl, hlk, hml, ?_⟩
    have hle:=column_mono hsub l.val
    have hpos:=column_positive (hfresh hm) hml
    omega
  · intro hthree
    have hlarge:3≤large.length:=le_trans hsmall hsub.length_le
    have hbound:=h.2 hlarge
    apply le_trans (filter_length_mono fresh _ _ ?_) hbound
    intro m hm ht
    have ht':=of_decide_eq_true ht
    change decide (∀ k:Fin b, j < k.val→m.testBit k.val=true→
      columnCount large k.val=large.length)=true
    apply decide_eq_true
    intro k hj hk
    have hle:=column_le_length large k.val
    by_contra hne
    have hproper:columnCount large k.val < large.length:=by omega
    obtain ⟨l, hjl, hlk, hml, hcol⟩:=h.1 m hm k hj hk hproper
    have hy:columnCount small l.val=small.length:=ht' l hjl hml
    have hc:=column_mono hsub l.val
    omega
end Helper4TemporalCore
namespace Helper4TemporalAux
open Helper4TemporalCore
def sourceGroups:List ℕ:=[1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4]
def olderGroups:List ℕ:=[0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 3]
def sourceProfiles:List (List ℕ):=[[14, 30], [6, 14, 22], [10, 14, 26], [12, 28], [20, 28], [28, 28], [28, 28], [4, 12, 20], [4, 12, 20], [8, 8], [8, 24], [24, 24], [24, 24], [24, 24], [16, 16], [16, 16], [16, 16], [16, 16]]
def forbiddenProfiles:List (List ℕ):=[[3, 7, 11, 19, 23, 27, 31], [3, 11, 15, 19, 23, 27, 31], [3, 7, 15, 19, 23, 27, 31], [5, 6, 7, 21, 22, 23, 29, 30, 31], [5, 6, 7, 13, 14, 15, 29, 30, 31], [5, 6, 7, 13, 14, 15, 21, 22, 23, 29, 30, 31], [5, 6, 7, 13, 14, 15, 21, 22, 23, 29, 30, 31], [13, 14, 15, 21, 22, 23, 29, 30, 31], [13, 14, 15, 21, 22, 23, 29, 30, 31], [9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31], [25, 26, 27, 28, 29, 30, 31], [9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31], [9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31], [9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31], [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
def sourceIndex (r:Fin 18):Fin 5:=
  ⟨sourceGroups[r.val]!, by fin_cases r <;> decide⟩
def olderIndex (r:Fin 18):Fin 5:=
  ⟨olderGroups[r.val]!, by fin_cases r <;> decide⟩
def sourceRows (r:Fin 18):List ℕ:=sourceProfiles[r.val]!
def forbidden (r:Fin 18):List ℕ:=forbiddenProfiles[r.val]!
lemma older_lt_source:∀ r:Fin 18, (olderIndex r).val < (sourceIndex r).val:=by
  decide+kernel
lemma source_size:∀ r:Fin 18, 2≤(sourceRows r).length:=by
  decide+kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma forbidden_obstruction:∀ r:Fin 18, ∀ m:Fin 32, m.val∈forbidden r→
    m.val.testBit (sourceIndex r).val=true∧
      ¬ TemporalProperty 5 (sourceIndex r).val (sourceRows r) (sourceRows r++[m.val]):=by
  intro r
  fin_cases r <;> decide+kernel
open scoped BigOperators
def priorRows (rows:Fin 5→List ℕ) (j:Fin 5):List ℕ:=
  ((List.finRange 5).flatMap fun h=>if h.val < j.val then rows h else []).filter
    (fun m=>m.testBit j.val)
def supportRows (rows:Fin 5→List ℕ) (j:Fin 5):List ℕ:=
  rows j++priorRows rows j
lemma mem_priorRows (rows:Fin 5→List ℕ) (h j:Fin 5) (hhj:h.val < j.val)
    (m:ℕ) (hm:m∈rows h) (hbit:m.testBit j.val=true):
    m∈priorRows rows j:=by
  apply List.mem_filter.mpr
  refine ⟨?_, hbit⟩
  apply List.mem_flatMap.mpr
  refine ⟨h, by simp, ?_⟩
  simpa only [hhj, ↓reduceIte] using hm
lemma temporal_forbids (rows:Fin 5→List ℕ)
    (hsmall:∀ j:Fin 5, ∀ m∈rows j, m < 32)
    (ht:∀ j:Fin 5, TemporalProperty 5 j.val (rows j) (supportRows rows j)):
    ∀ r:Fin 18, rows (sourceIndex r)=sourceRows r→
      ∀ m∈rows (olderIndex r), m∉forbidden r:=by
  intro r hsource m hm hforbidden
  have hob:=forbidden_obstruction r ⟨m, hsmall _ _ hm⟩ hforbidden
  have hprior:=mem_priorRows rows (olderIndex r) (sourceIndex r)
    (older_lt_source r) m hm hob.1
  have hsub:(rows (sourceIndex r)++[m]).Sublist (supportRows rows (sourceIndex r)):=
    (List.singleton_sublist.mpr hprior).append_left (rows (sourceIndex r))
  have hlen:3≤(rows (sourceIndex r)++[m]).length:=by
    have hs:=source_size r
    rw [hsource, List.length_append, List.length_singleton]
    omega
  have hrestricted:=temporal_restrict hsub (List.subset_append_left _ _) hlen
    (ht (sourceIndex r))
  rw [hsource] at hrestricted
  exact hob.2 hrestricted
def rowClause (r:Fin 18) (j:ℕ) (rows:List ℕ):ℕ:=
  (if j=(sourceIndex r).val then if rows=sourceRows r then 1 else 0 else 0)+
  (if j=(olderIndex r).val then if rows.any (fun m=>decide (m∈forbidden r)) then 1 else 0
    else 0)
lemma row_clause_bound (rows:Fin 5→List ℕ)
    (hforbid:∀ r:Fin 18, rows (sourceIndex r)=sourceRows r→
      ∀ m∈rows (olderIndex r), m∉forbidden r):
    ∀ r:Fin 18, (∑ j:Fin 5, rowClause r j.val (rows j))≤1:=by
  intro r
  unfold rowClause
  rw [Finset.sum_add_distrib]
  simp only [Fin.val_inj]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hs:rows (sourceIndex r)=sourceRows r
  · have hf:(rows (olderIndex r)).any (fun m=>decide (m∈forbidden r))=false:=by
      apply List.any_eq_false.mpr
      intro m hm
      exact fun he=>hforbid r hs m hm (of_decide_eq_true he)
    simp [hs, hf]
  · cases ha:(rows (olderIndex r)).any (fun m=>decide (m∈forbidden r)) <;>
      simp [hs]
lemma temporal_row_clause_bound (rows:Fin 5→List ℕ)
    (hsmall:∀ j:Fin 5, ∀ m∈rows j, m < 32)
    (ht:∀ j:Fin 5, TemporalProperty 5 j.val (rows j) (supportRows rows j)):
    ∀ r:Fin 18, (∑ j:Fin 5, rowClause r j.val (rows j))≤1:=
  row_clause_bound rows (temporal_forbids rows hsmall ht)
end Helper4TemporalAux
namespace Helper4TemporalAdapter
open scoped BigOperators
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma row_clause_eq:∀ r:Fin 18, ∀ j:Fin 5, ∀ rows:List ℕ,
    Helper4TemporalAux.rowClause r j.val rows=
      Helper4CombinedCertificate.rowClause r j.val rows:=by
  intro r j rows
  fin_cases r <;> fin_cases j <;>
    simp [Helper4TemporalAux.rowClause, Helper4TemporalAux.sourceIndex,
      Helper4TemporalAux.olderIndex, Helper4TemporalAux.sourceGroups,
      Helper4TemporalAux.olderGroups, Helper4TemporalAux.sourceRows,
      Helper4TemporalAux.sourceProfiles, Helper4TemporalAux.forbidden,
      Helper4TemporalAux.forbiddenProfiles, Helper4CombinedCertificate.rowClause,
      Helper4CombinedCertificate.sourceGroups, Helper4CombinedCertificate.sourceProfiles,
      Helper4ClosingCertificate.compatibilityTable]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma all_masks_small:∀ p:Fin 327,
    (Helper4ClosingCertificate.profile p).all (fun m=>decide (m < 32))=true:=by
  intro p
  fin_cases p <;> decide+kernel
set_option maxRecDepth 100000 in
lemma canonical_masks_small (j:Fin 5) (rows:List ℕ)
    (hcan:Helper4CombinedCertificate.Canonical j rows)
    (hgood:Helper4ProfileMembership.strongGood j.val rows=true):
    ∀ m∈rows, m < 32:=by
  obtain ⟨p, hpgroup, hp⟩:=Helper4CombinedCertificate.canonical_locates j rows hcan hgood
  intro m hm
  rw [← hp] at hm
  exact of_decide_eq_true (List.all_eq_true.mp (all_masks_small p) m hm)
lemma temporal_mask_bound
    (rows:Fin 5→List ℕ) (z:ℕ)
    (hcan:∀ j:Fin 5, Helper4CombinedCertificate.Canonical j (rows j))
    (hgood:∀ j:Fin 5, Helper4ProfileMembership.strongGood j.val (rows j)=true)
    (hw:32*z+∑ j:Fin 5, Helper4ClosingCertificate.totalWeight (rows j)≤128)
    (hu4:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 4 (rows j))≤128)
    (hu8:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 8 (rows j))≤128)
    (hu16:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 16 (rows j))≤128)
    (ht:∀ j:Fin 5, Helper4TemporalCore.TemporalProperty 5 j.val (rows j)
      (Helper4TemporalAux.supportRows rows j)):
    z+(∑ j:Fin 5, (rows j).length)≤11:=by
  have hsmall:∀ j:Fin 5, ∀ m∈rows j, m < 32:=
    fun j=>canonical_masks_small j (rows j) (hcan j) (hgood j)
  have ha:=Helper4TemporalAux.temporal_row_clause_bound rows hsmall ht
  have hc:∀ r:Fin 18,
      (∑ j:Fin 5, Helper4CombinedCertificate.rowClause r j.val (rows j))≤1:=by
    intro r
    have heq:(∑ j:Fin 5, Helper4CombinedCertificate.rowClause r j.val (rows j))=
        ∑ j:Fin 5, Helper4TemporalAux.rowClause r j.val (rows j):=by
      apply Finset.sum_congr rfl
      intro j hj
      exact (row_clause_eq r j (rows j)).symm
    rw [heq]
    exact ha r
  exact Helper4CombinedCertificate.canonical_mask_bound rows z hcan hgood hw hu4 hu8 hu16 hc
end Helper4TemporalAdapter
namespace Helper4CanonicalEncoding
abbrev FirstBit (j m:ℕ):Prop:=
  m < 32∧m.testBit j=true∧∀ k:Fin 5, k.val < j→m.testBit k.val=false
def decode (j m:ℕ):ℕ:=(m / 2^j+1) / 2
set_option maxHeartbeats 0 in
lemma decode_valid:∀ j:Fin 5, ∀ m:Fin 32, FirstBit j.val m.val→
    0 < decode j.val m.val∧decode j.val m.val < 2^(4 - j.val)+1∧
      m.val=2^j.val*(2*decode j.val m.val - 1):=by
  intro j m
  fin_cases j <;> fin_cases m <;> decide+kernel
lemma decode_monotone (j a b:ℕ) (hab:a≤b):decode j a≤decode j b:=by
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.div_le_div_right hab) 1)
lemma canonical0_of_sorted (rows:List ℕ) (hlen:rows.length≤5)
    (hsort:rows.Pairwise (·≤·)) (hbits:∀ m∈rows, FirstBit 0 m):
    Helper4CombinedCertificate.Canonical0 rows:=by
  cases rows with
  | nil=>
    refine ⟨(0:Fin 17), (0:Fin 17), (0:Fin 17), (0:Fin 17), (0:Fin 17), ?_⟩
    simp only [Fin.val_zero]
    refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, ?_⟩
    rfl
  | cons x0 t0=>
    cases t0 with
    | nil=>
      have hb0:=hbits x0 (by simp)
      have hd0:=decode_valid ⟨0, by decide⟩ ⟨x0, hb0.1⟩ hb0
      refine ⟨(0:Fin 17), (0:Fin 17), (0:Fin 17), (0:Fin 17), ⟨decode 0 x0, by simpa using hd0.2.1⟩, ?_⟩
      simp only [Fin.val_zero]
      refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, ?_⟩
      simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
      have hn0:decode 0 x0≠0:=Nat.ne_of_gt hd0.1
      simp only [↓reduceIte, hn0]
      congr 1
      exact hd0.2.2
    | cons x1 t1=>
      cases t1 with
      | nil=>
        have hb0:=hbits x0 (by simp)
        have hd0:=decode_valid ⟨0, by decide⟩ ⟨x0, hb0.1⟩ hb0
        have hb1:=hbits x1 (by simp)
        have hd1:=decode_valid ⟨0, by decide⟩ ⟨x1, hb1.1⟩ hb1
        have ho0:decode 0 x0≤decode 0 x1:=
          decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
        refine ⟨(0:Fin 17), (0:Fin 17), (0:Fin 17), ⟨decode 0 x0, by simpa using hd0.2.1⟩, ⟨decode 0 x1, by simpa using hd1.2.1⟩, ?_⟩
        simp only [Fin.val_zero]
        refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, ho0, ?_⟩
        simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
        have hn0:decode 0 x0≠0:=Nat.ne_of_gt hd0.1
        have hn1:decode 0 x1≠0:=Nat.ne_of_gt hd1.1
        simp only [↓reduceIte, hn0, hn1]
        simp only [← hd0.2.2, ← hd1.2.2]
      | cons x2 t2=>
        cases t2 with
        | nil=>
          have hb0:=hbits x0 (by simp)
          have hd0:=decode_valid ⟨0, by decide⟩ ⟨x0, hb0.1⟩ hb0
          have hb1:=hbits x1 (by simp)
          have hd1:=decode_valid ⟨0, by decide⟩ ⟨x1, hb1.1⟩ hb1
          have hb2:=hbits x2 (by simp)
          have hd2:=decode_valid ⟨0, by decide⟩ ⟨x2, hb2.1⟩ hb2
          have ho0:decode 0 x0≤decode 0 x1:=
            decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
          have ho1:decode 0 x1≤decode 0 x2:=
            decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 x2 (by simp))
          refine ⟨(0:Fin 17), (0:Fin 17), ⟨decode 0 x0, by simpa using hd0.2.1⟩, ⟨decode 0 x1, by simpa using hd1.2.1⟩, ⟨decode 0 x2, by simpa using hd2.2.1⟩, ?_⟩
          simp only [Fin.val_zero]
          refine ⟨Nat.zero_le _, Nat.zero_le _, ho0, ho1, ?_⟩
          simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
          have hn0:decode 0 x0≠0:=Nat.ne_of_gt hd0.1
          have hn1:decode 0 x1≠0:=Nat.ne_of_gt hd1.1
          have hn2:decode 0 x2≠0:=Nat.ne_of_gt hd2.1
          simp only [↓reduceIte, hn0, hn1, hn2]
          simp only [← hd0.2.2, ← hd1.2.2, ← hd2.2.2]
        | cons x3 t3=>
          cases t3 with
          | nil=>
            have hb0:=hbits x0 (by simp)
            have hd0:=decode_valid ⟨0, by decide⟩ ⟨x0, hb0.1⟩ hb0
            have hb1:=hbits x1 (by simp)
            have hd1:=decode_valid ⟨0, by decide⟩ ⟨x1, hb1.1⟩ hb1
            have hb2:=hbits x2 (by simp)
            have hd2:=decode_valid ⟨0, by decide⟩ ⟨x2, hb2.1⟩ hb2
            have hb3:=hbits x3 (by simp)
            have hd3:=decode_valid ⟨0, by decide⟩ ⟨x3, hb3.1⟩ hb3
            have ho0:decode 0 x0≤decode 0 x1:=
              decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
            have ho1:decode 0 x1≤decode 0 x2:=
              decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 x2 (by simp))
            have ho2:decode 0 x2≤decode 0 x3:=
              decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2).1 x3 (by simp))
            refine ⟨(0:Fin 17), ⟨decode 0 x0, by simpa using hd0.2.1⟩, ⟨decode 0 x1, by simpa using hd1.2.1⟩, ⟨decode 0 x2, by simpa using hd2.2.1⟩, ⟨decode 0 x3, by simpa using hd3.2.1⟩, ?_⟩
            simp only [Fin.val_zero]
            refine ⟨Nat.zero_le _, ho0, ho1, ho2, ?_⟩
            simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
            have hn0:decode 0 x0≠0:=Nat.ne_of_gt hd0.1
            have hn1:decode 0 x1≠0:=Nat.ne_of_gt hd1.1
            have hn2:decode 0 x2≠0:=Nat.ne_of_gt hd2.1
            have hn3:decode 0 x3≠0:=Nat.ne_of_gt hd3.1
            simp only [↓reduceIte, hn0, hn1, hn2, hn3]
            simp only [← hd0.2.2, ← hd1.2.2, ← hd2.2.2, ← hd3.2.2]
          | cons x4 t4=>
            cases t4 with
            | nil=>
              have hb0:=hbits x0 (by simp)
              have hd0:=decode_valid ⟨0, by decide⟩ ⟨x0, hb0.1⟩ hb0
              have hb1:=hbits x1 (by simp)
              have hd1:=decode_valid ⟨0, by decide⟩ ⟨x1, hb1.1⟩ hb1
              have hb2:=hbits x2 (by simp)
              have hd2:=decode_valid ⟨0, by decide⟩ ⟨x2, hb2.1⟩ hb2
              have hb3:=hbits x3 (by simp)
              have hd3:=decode_valid ⟨0, by decide⟩ ⟨x3, hb3.1⟩ hb3
              have hb4:=hbits x4 (by simp)
              have hd4:=decode_valid ⟨0, by decide⟩ ⟨x4, hb4.1⟩ hb4
              have ho0:decode 0 x0≤decode 0 x1:=
                decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
              have ho1:decode 0 x1≤decode 0 x2:=
                decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 x2 (by simp))
              have ho2:decode 0 x2≤decode 0 x3:=
                decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2).1 x3 (by simp))
              have ho3:decode 0 x3≤decode 0 x4:=
                decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2).2).1 x4 (by simp))
              refine ⟨⟨decode 0 x0, by simpa using hd0.2.1⟩, ⟨decode 0 x1, by simpa using hd1.2.1⟩, ⟨decode 0 x2, by simpa using hd2.2.1⟩, ⟨decode 0 x3, by simpa using hd3.2.1⟩, ⟨decode 0 x4, by simpa using hd4.2.1⟩, ?_⟩
              refine ⟨ho0, ho1, ho2, ho3, ?_⟩
              simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
              have hn0:decode 0 x0≠0:=Nat.ne_of_gt hd0.1
              have hn1:decode 0 x1≠0:=Nat.ne_of_gt hd1.1
              have hn2:decode 0 x2≠0:=Nat.ne_of_gt hd2.1
              have hn3:decode 0 x3≠0:=Nat.ne_of_gt hd3.1
              have hn4:decode 0 x4≠0:=Nat.ne_of_gt hd4.1
              simp only [↓reduceIte, hn0, hn1, hn2, hn3, hn4]
              simp only [← hd0.2.2, ← hd1.2.2, ← hd2.2.2, ← hd3.2.2, ← hd4.2.2]
            | cons x5 t5=>
              simp only [List.length_cons] at hlen
              omega
lemma canonical1_of_sorted (rows:List ℕ) (hlen:rows.length≤4)
    (hsort:rows.Pairwise (·≤·)) (hbits:∀ m∈rows, FirstBit 1 m):
    Helper4CombinedCertificate.Canonical1 rows:=by
  cases rows with
  | nil=>
    refine ⟨(0:Fin 9), (0:Fin 9), (0:Fin 9), (0:Fin 9), ?_⟩
    simp only [Fin.val_zero]
    refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, ?_⟩
    rfl
  | cons x0 t0=>
    cases t0 with
    | nil=>
      have hb0:=hbits x0 (by simp)
      have hd0:=decode_valid ⟨1, by decide⟩ ⟨x0, hb0.1⟩ hb0
      refine ⟨(0:Fin 9), (0:Fin 9), (0:Fin 9), ⟨decode 1 x0, by simpa using hd0.2.1⟩, ?_⟩
      simp only [Fin.val_zero]
      refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, ?_⟩
      simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
      have hn0:decode 1 x0≠0:=Nat.ne_of_gt hd0.1
      simp only [↓reduceIte, hn0]
      congr 1
      exact hd0.2.2
    | cons x1 t1=>
      cases t1 with
      | nil=>
        have hb0:=hbits x0 (by simp)
        have hd0:=decode_valid ⟨1, by decide⟩ ⟨x0, hb0.1⟩ hb0
        have hb1:=hbits x1 (by simp)
        have hd1:=decode_valid ⟨1, by decide⟩ ⟨x1, hb1.1⟩ hb1
        have ho0:decode 1 x0≤decode 1 x1:=
          decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
        refine ⟨(0:Fin 9), (0:Fin 9), ⟨decode 1 x0, by simpa using hd0.2.1⟩, ⟨decode 1 x1, by simpa using hd1.2.1⟩, ?_⟩
        simp only [Fin.val_zero]
        refine ⟨Nat.zero_le _, Nat.zero_le _, ho0, ?_⟩
        simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
        have hn0:decode 1 x0≠0:=Nat.ne_of_gt hd0.1
        have hn1:decode 1 x1≠0:=Nat.ne_of_gt hd1.1
        simp only [↓reduceIte, hn0, hn1]
        simp only [← hd0.2.2, ← hd1.2.2]
      | cons x2 t2=>
        cases t2 with
        | nil=>
          have hb0:=hbits x0 (by simp)
          have hd0:=decode_valid ⟨1, by decide⟩ ⟨x0, hb0.1⟩ hb0
          have hb1:=hbits x1 (by simp)
          have hd1:=decode_valid ⟨1, by decide⟩ ⟨x1, hb1.1⟩ hb1
          have hb2:=hbits x2 (by simp)
          have hd2:=decode_valid ⟨1, by decide⟩ ⟨x2, hb2.1⟩ hb2
          have ho0:decode 1 x0≤decode 1 x1:=
            decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
          have ho1:decode 1 x1≤decode 1 x2:=
            decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 x2 (by simp))
          refine ⟨(0:Fin 9), ⟨decode 1 x0, by simpa using hd0.2.1⟩, ⟨decode 1 x1, by simpa using hd1.2.1⟩, ⟨decode 1 x2, by simpa using hd2.2.1⟩, ?_⟩
          simp only [Fin.val_zero]
          refine ⟨Nat.zero_le _, ho0, ho1, ?_⟩
          simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
          have hn0:decode 1 x0≠0:=Nat.ne_of_gt hd0.1
          have hn1:decode 1 x1≠0:=Nat.ne_of_gt hd1.1
          have hn2:decode 1 x2≠0:=Nat.ne_of_gt hd2.1
          simp only [↓reduceIte, hn0, hn1, hn2]
          simp only [← hd0.2.2, ← hd1.2.2, ← hd2.2.2]
        | cons x3 t3=>
          cases t3 with
          | nil=>
            have hb0:=hbits x0 (by simp)
            have hd0:=decode_valid ⟨1, by decide⟩ ⟨x0, hb0.1⟩ hb0
            have hb1:=hbits x1 (by simp)
            have hd1:=decode_valid ⟨1, by decide⟩ ⟨x1, hb1.1⟩ hb1
            have hb2:=hbits x2 (by simp)
            have hd2:=decode_valid ⟨1, by decide⟩ ⟨x2, hb2.1⟩ hb2
            have hb3:=hbits x3 (by simp)
            have hd3:=decode_valid ⟨1, by decide⟩ ⟨x3, hb3.1⟩ hb3
            have ho0:decode 1 x0≤decode 1 x1:=
              decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
            have ho1:decode 1 x1≤decode 1 x2:=
              decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 x2 (by simp))
            have ho2:decode 1 x2≤decode 1 x3:=
              decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2).1 x3 (by simp))
            refine ⟨⟨decode 1 x0, by simpa using hd0.2.1⟩, ⟨decode 1 x1, by simpa using hd1.2.1⟩, ⟨decode 1 x2, by simpa using hd2.2.1⟩, ⟨decode 1 x3, by simpa using hd3.2.1⟩, ?_⟩
            refine ⟨ho0, ho1, ho2, ?_⟩
            simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
            have hn0:decode 1 x0≠0:=Nat.ne_of_gt hd0.1
            have hn1:decode 1 x1≠0:=Nat.ne_of_gt hd1.1
            have hn2:decode 1 x2≠0:=Nat.ne_of_gt hd2.1
            have hn3:decode 1 x3≠0:=Nat.ne_of_gt hd3.1
            simp only [↓reduceIte, hn0, hn1, hn2, hn3]
            simp only [← hd0.2.2, ← hd1.2.2, ← hd2.2.2, ← hd3.2.2]
          | cons x4 t4=>
            simp only [List.length_cons] at hlen
            omega
lemma canonical2_of_sorted (rows:List ℕ) (hlen:rows.length≤3)
    (hsort:rows.Pairwise (·≤·)) (hbits:∀ m∈rows, FirstBit 2 m):
    Helper4CombinedCertificate.Canonical2 rows:=by
  cases rows with
  | nil=>
    refine ⟨(0:Fin 5), (0:Fin 5), (0:Fin 5), ?_⟩
    simp only [Fin.val_zero]
    refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
    rfl
  | cons x0 t0=>
    cases t0 with
    | nil=>
      have hb0:=hbits x0 (by simp)
      have hd0:=decode_valid ⟨2, by decide⟩ ⟨x0, hb0.1⟩ hb0
      refine ⟨(0:Fin 5), (0:Fin 5), ⟨decode 2 x0, by simpa using hd0.2.1⟩, ?_⟩
      simp only [Fin.val_zero]
      refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
      simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
      have hn0:decode 2 x0≠0:=Nat.ne_of_gt hd0.1
      simp only [↓reduceIte, hn0]
      congr 1
      exact hd0.2.2
    | cons x1 t1=>
      cases t1 with
      | nil=>
        have hb0:=hbits x0 (by simp)
        have hd0:=decode_valid ⟨2, by decide⟩ ⟨x0, hb0.1⟩ hb0
        have hb1:=hbits x1 (by simp)
        have hd1:=decode_valid ⟨2, by decide⟩ ⟨x1, hb1.1⟩ hb1
        have ho0:decode 2 x0≤decode 2 x1:=
          decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
        refine ⟨(0:Fin 5), ⟨decode 2 x0, by simpa using hd0.2.1⟩, ⟨decode 2 x1, by simpa using hd1.2.1⟩, ?_⟩
        simp only [Fin.val_zero]
        refine ⟨Nat.zero_le _, ho0, ?_⟩
        simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
        have hn0:decode 2 x0≠0:=Nat.ne_of_gt hd0.1
        have hn1:decode 2 x1≠0:=Nat.ne_of_gt hd1.1
        simp only [↓reduceIte, hn0, hn1]
        simp only [← hd0.2.2, ← hd1.2.2]
      | cons x2 t2=>
        cases t2 with
        | nil=>
          have hb0:=hbits x0 (by simp)
          have hd0:=decode_valid ⟨2, by decide⟩ ⟨x0, hb0.1⟩ hb0
          have hb1:=hbits x1 (by simp)
          have hd1:=decode_valid ⟨2, by decide⟩ ⟨x1, hb1.1⟩ hb1
          have hb2:=hbits x2 (by simp)
          have hd2:=decode_valid ⟨2, by decide⟩ ⟨x2, hb2.1⟩ hb2
          have ho0:decode 2 x0≤decode 2 x1:=
            decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
          have ho1:decode 2 x1≤decode 2 x2:=
            decode_monotone _ _ _ ((List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 x2 (by simp))
          refine ⟨⟨decode 2 x0, by simpa using hd0.2.1⟩, ⟨decode 2 x1, by simpa using hd1.2.1⟩, ⟨decode 2 x2, by simpa using hd2.2.1⟩, ?_⟩
          refine ⟨ho0, ho1, ?_⟩
          simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
          have hn0:decode 2 x0≠0:=Nat.ne_of_gt hd0.1
          have hn1:decode 2 x1≠0:=Nat.ne_of_gt hd1.1
          have hn2:decode 2 x2≠0:=Nat.ne_of_gt hd2.1
          simp only [↓reduceIte, hn0, hn1, hn2]
          simp only [← hd0.2.2, ← hd1.2.2, ← hd2.2.2]
        | cons x3 t3=>
          simp only [List.length_cons] at hlen
          omega
lemma canonical3_of_sorted (rows:List ℕ) (hlen:rows.length≤2)
    (hsort:rows.Pairwise (·≤·)) (hbits:∀ m∈rows, FirstBit 3 m):
    Helper4CombinedCertificate.Canonical3 rows:=by
  cases rows with
  | nil=>
    refine ⟨(0:Fin 3), (0:Fin 3), ?_⟩
    simp only [Fin.val_zero]
    refine ⟨Nat.zero_le _, ?_⟩
    rfl
  | cons x0 t0=>
    cases t0 with
    | nil=>
      have hb0:=hbits x0 (by simp)
      have hd0:=decode_valid ⟨3, by decide⟩ ⟨x0, hb0.1⟩ hb0
      refine ⟨(0:Fin 3), ⟨decode 3 x0, by simpa using hd0.2.1⟩, ?_⟩
      simp only [Fin.val_zero]
      refine ⟨Nat.zero_le _, ?_⟩
      simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
      have hn0:decode 3 x0≠0:=Nat.ne_of_gt hd0.1
      simp only [↓reduceIte, hn0]
      congr 1
      exact hd0.2.2
    | cons x1 t1=>
      cases t1 with
      | nil=>
        have hb0:=hbits x0 (by simp)
        have hd0:=decode_valid ⟨3, by decide⟩ ⟨x0, hb0.1⟩ hb0
        have hb1:=hbits x1 (by simp)
        have hd1:=decode_valid ⟨3, by decide⟩ ⟨x1, hb1.1⟩ hb1
        have ho0:decode 3 x0≤decode 3 x1:=
          decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
        refine ⟨⟨decode 3 x0, by simpa using hd0.2.1⟩, ⟨decode 3 x1, by simpa using hd1.2.1⟩, ?_⟩
        refine ⟨ho0, ?_⟩
        simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
        have hn0:decode 3 x0≠0:=Nat.ne_of_gt hd0.1
        have hn1:decode 3 x1≠0:=Nat.ne_of_gt hd1.1
        simp only [↓reduceIte, hn0, hn1]
        simp only [← hd0.2.2, ← hd1.2.2]
      | cons x2 t2=>
        simp only [List.length_cons] at hlen
        omega
lemma canonical4_of_sorted (rows:List ℕ) (hlen:rows.length≤2)
    (hsort:rows.Pairwise (·≤·)) (hbits:∀ m∈rows, FirstBit 4 m):
    Helper4CombinedCertificate.Canonical4 rows:=by
  cases rows with
  | nil=>
    refine ⟨(0:Fin 2), (0:Fin 2), ?_⟩
    simp only [Fin.val_zero]
    refine ⟨Nat.zero_le _, ?_⟩
    rfl
  | cons x0 t0=>
    cases t0 with
    | nil=>
      have hb0:=hbits x0 (by simp)
      have hd0:=decode_valid ⟨4, by decide⟩ ⟨x0, hb0.1⟩ hb0
      refine ⟨(0:Fin 2), ⟨decode 4 x0, by simpa using hd0.2.1⟩, ?_⟩
      simp only [Fin.val_zero]
      refine ⟨Nat.zero_le _, ?_⟩
      simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
      have hn0:decode 4 x0≠0:=Nat.ne_of_gt hd0.1
      simp only [↓reduceIte, hn0]
      congr 1
      exact hd0.2.2
    | cons x1 t1=>
      cases t1 with
      | nil=>
        have hb0:=hbits x0 (by simp)
        have hd0:=decode_valid ⟨4, by decide⟩ ⟨x0, hb0.1⟩ hb0
        have hb1:=hbits x1 (by simp)
        have hd1:=decode_valid ⟨4, by decide⟩ ⟨x1, hb1.1⟩ hb1
        have ho0:decode 4 x0≤decode 4 x1:=
          decode_monotone _ _ _ ((List.pairwise_cons.mp hsort).1 x1 (by simp))
        refine ⟨⟨decode 4 x0, by simpa using hd0.2.1⟩, ⟨decode 4 x1, by simpa using hd1.2.1⟩, ?_⟩
        refine ⟨ho0, ?_⟩
        simp only [Helper4ProfileMembership.encoded, List.filterMap_cons, List.filterMap_nil]
        have hn0:decode 4 x0≠0:=Nat.ne_of_gt hd0.1
        have hn1:decode 4 x1≠0:=Nat.ne_of_gt hd1.1
        simp only [↓reduceIte, hn0, hn1]
        simp only [← hd0.2.2, ← hd1.2.2]
      | cons x2 t2=>
        simp only [List.length_cons] at hlen
        omega
lemma canonical_of_sorted (j:Fin 5) (rows:List ℕ)
    (hlen:rows.length≤ max 2 (5 - j.val))
    (hsort:rows.Pairwise (·≤·)) (hbits:∀ m∈rows, FirstBit j.val m):
    Helper4CombinedCertificate.Canonical j rows:=by
  fin_cases j
  · exact canonical0_of_sorted rows hlen hsort hbits
  · exact canonical1_of_sorted rows hlen hsort hbits
  · exact canonical2_of_sorted rows hlen hsort hbits
  · exact canonical3_of_sorted rows hlen hsort hbits
  · exact canonical4_of_sorted rows hlen hsort hbits
end Helper4CanonicalEncoding
namespace Helper4CanonicalEncoding
open scoped BigOperators
lemma sorted_temporal_mask_bound
    (rows:Fin 5→List ℕ) (z:ℕ)
    (hlen:∀ j:Fin 5, (rows j).length≤ max 2 (5 - j.val))
    (hsort:∀ j:Fin 5, (rows j).Pairwise (·≤·))
    (hbits:∀ j:Fin 5, ∀ m∈rows j, FirstBit j.val m)
    (hgood:∀ j:Fin 5, Helper4ProfileMembership.strongGood j.val (rows j)=true)
    (hw:32*z+∑ j:Fin 5, Helper4ClosingCertificate.totalWeight (rows j)≤128)
    (hu4:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 4 (rows j))≤128)
    (hu8:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 8 (rows j))≤128)
    (hu16:(∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight 16 (rows j))≤128)
    (ht:∀ j:Fin 5, Helper4TemporalCore.TemporalProperty 5 j.val (rows j)
      (Helper4TemporalAux.supportRows rows j)):
    z+(∑ j:Fin 5, (rows j).length)≤11:=
  Helper4TemporalAdapter.temporal_mask_bound rows z
    (fun j=>canonical_of_sorted j (rows j) (hlen j) (hsort j) (hbits j))
    hgood hw hu4 hu8 hu16 ht
end Helper4CanonicalEncoding
namespace Helper4TemporalBoolean
open Helper4TemporalCore
lemma intro_restrict {b j:ℕ} {fresh small large:List ℕ}
    (hsub:small.Sublist large) (hfresh:fresh⊆small)
    (h:IntroProperty b j fresh large):IntroProperty b j fresh small:=by
  intro m hm k hj hk hproper
  have hproperLarge:columnCount large k.val < large.length:=by
    have hle:=column_le_length large k.val
    by_contra hnot
    have he:columnCount large k.val=large.length:=by omega
    have:=column_full_mono hsub k.val he
    omega
  obtain ⟨l, hjl, hlk, hml, hcol⟩:=h m hm k hj hk hproperLarge
  refine ⟨l, hjl, hlk, hml, ?_⟩
  have hle:=column_mono hsub l.val
  have hpos:=column_positive (hfresh hm) hml
  omega
lemma find_range_min (p:ℕ→Bool) {b k l:ℕ}
    (hf:(List.range b).find? p=some k) (hl:l < b) (hp:p l=true):k≤l:=by
  induction b with
  | zero=>omega
  | succ b ih=>
    cases he:(List.range b).find? p with
    | none=>
      have hnot:=List.find?_eq_none.mp he
      have hkl:k=b:=by
        cases hb:p b with
        | false=>simp [List.range_succ, List.find?_append, he, hb] at hf
        | true=>simpa [List.range_succ, List.find?_append, he, hb] using hf.symm
      by_cases hlb:l < b
      · exact False.elim (hnot l (List.mem_range.mpr hlb) hp)
      · omega
    | some a=>
      have hka:k=a:=by
        simpa [List.range_succ, List.find?_append, he] using hf.symm
      by_cases hlb:l < b
      · apply ih
        · simpa [hka] using he
        · exact hlb
      · have hab:a < b:=List.mem_range.mp (List.mem_of_find?_eq_some he)
        omega
lemma temporal_of_intro {b j:ℕ} {rows:List ℕ}
    (h:IntroProperty b j rows rows):
    Helper4ProfileMembership.temporal b j rows=true:=by
  apply List.all_eq_true.mpr
  intro m hm
  let p:ℕ→Bool:=fun k=>decide (j < k) && m.testBit k &&
    decide (columnCount rows k < rows.length)
  change (match (List.range b).find? p with
    | none=>true
    | some k=>decide (columnCount rows k=1))=true
  cases hf:(List.range b).find? p with
  | none=>rfl
  | some k=>
    apply decide_eq_true
    have hkb:k < b:=List.mem_range.mp (List.mem_of_find?_eq_some hf)
    have hp:=List.find?_some hf
    have hkprops:j < k∧m.testBit k=true∧columnCount rows k < rows.length:=by
      simpa only [p, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hp
    obtain ⟨l, hjl, hlk, hml, hcol⟩:=h m hm ⟨k, hkb⟩ hkprops.1
      hkprops.2.1 hkprops.2.2
    have hlen:1 < rows.length:=by
      have hpos:=column_positive hm hkprops.2.1
      omega
    have hpl:p l.val=true:=by
      simp only [p, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hjl, hml⟩, by omega⟩
    change l.val≤k at hlk
    have hkl:=find_range_min p hf l.isLt hpl
    have he:l.val=k:=by omega
    simpa only [he] using hcol
lemma temporal_of_whole {b j:ℕ} {rows older:List ℕ}
    (h:TemporalProperty b j rows (rows++older)):
    Helper4ProfileMembership.temporal b j rows=true:=by
  apply temporal_of_intro
  exact intro_restrict (List.sublist_append_left rows older) (List.Subset.refl rows) h.1
lemma covered_of_whole {b j:ℕ} {rows older:List ℕ}
    (h:TemporalProperty b j rows (rows++older)):
    rows.length≤2∨rows.length≤Helper4ProfileMembership.covered b j rows+1:=by
  by_cases hsmall:rows.length≤2
  · exact Or.inl hsmall
  right
  have hthree:3≤rows.length:=by omega
  have hr:=temporal_restrict (List.sublist_append_left rows older)
    (List.Subset.refl rows) hthree h
  let p:ℕ→Bool:=fun m=>(List.range b).any fun k=>
    decide (j < k) && m.testBit k && decide (columnCount rows k=1)
  have hnot:∀ m∈rows, (!p m)=true→terminal b j rows m=true:=by
    intro m hm hp
    apply decide_eq_true
    intro k hj hk
    have hle:=column_le_length rows k.val
    by_contra hne
    have hproper:columnCount rows k.val < rows.length:=by omega
    obtain ⟨l, hjl, hlk, hml, hcol⟩:=hr.1 m hm k hj hk hproper
    have hpl:p m=true:=by
      apply List.any_eq_true.mpr
      refine ⟨l.val, List.mem_range.mpr l.isLt, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hjl, hml⟩, hcol⟩
    simp [hpl] at hp
  have hcount:=filter_length_mono rows (fun m=>!p m) (terminal b j rows) hnot
  have hsum:=List.length_eq_length_filter_add (l:=rows) p
  have ht:=hr.2 hthree
  have hc:Helper4ProfileMembership.covered b j rows=(rows.filter p).length:=rfl
  rw [hc]
  omega
end Helper4TemporalBoolean
namespace Helper4FreshLength
open Helper4TemporalCore
lemma filter_or_length (rows:List ℕ) (p q:ℕ→Bool):
    (rows.filter fun m=>p m || q m).length≤
      (rows.filter p).length+(rows.filter q).length:=by
  induction rows with
  | nil=>simp
  | cons m rows ih=>
    cases hp:p m <;> cases hq:q m <;> simp_all <;> omega
lemma filter_any_length (rows ks:List ℕ) (p:ℕ→ℕ→Bool):
    (rows.filter fun m=>ks.any fun k=>p k m).length≤
      (ks.map fun k=>(rows.filter (p k)).length).sum:=by
  induction ks with
  | nil=>simp
  | cons k ks ih=>
    simp only [List.any_cons, List.map_cons, List.sum_cons]
    exact le_trans (filter_or_length rows (p k) (fun m=>ks.any fun l=>p l m))
      (Nat.add_le_add_left ih _)
lemma later_count (b j:ℕ):
    ((List.range b).map fun k=>if j < k then 1 else 0).sum=b - (j+1):=by
  induction b with
  | zero=>simp
  | succ b ih=>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ih]
    by_cases h:j < b <;> simp only [h, ↓reduceIte] <;> omega
lemma covered_le (b j:ℕ) (rows:List ℕ):
    Helper4ProfileMembership.covered b j rows≤b - (j+1):=by
  let p:ℕ→ℕ→Bool:=fun k m=>decide (j < k) && m.testBit k &&
    decide (columnCount rows k=1)
  have hcol:∀ k, (rows.filter (p k)).length≤ if j < k then 1 else 0:=by
    intro k
    by_cases hj:j < k
    · by_cases hc:columnCount rows k=1
      · simp only [p, hj, hc, Bool.true_and, Bool.and_true, decide_true, ↓reduceIte]
        exact le_of_eq hc
      · simp [p, hj, hc]
    · simp [p, hj]
  have hs:∀ ks:List ℕ, (ks.map fun k=>(rows.filter (p k)).length).sum≤
      (ks.map fun k=>if j < k then 1 else 0).sum:=by
    intro ks
    induction ks with
    | nil=>simp
    | cons k ks ih=>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hcol k) ih
  have ha:=filter_any_length rows (List.range b) p
  change Helper4ProfileMembership.covered b j rows≤_ at ha
  exact le_trans ha (le_trans (hs (List.range b)) (le_of_eq (later_count b j)))
lemma length_bound_of_whole {b j:ℕ} {rows older:List ℕ}
    (h:TemporalProperty b j rows (rows++older)):
    rows.length≤ max 2 (b - j):=by
  have hf:=Helper4TemporalBoolean.covered_of_whole h
  have hc:=covered_le b j rows
  omega
end Helper4FreshLength
namespace Helper4TerminalKraft
open Helper4TemporalCore
def term (sub m:ℕ):ℕ:=
  if Nat.land m sub=sub then
    Helper4ClosingCertificate.weight m*
      2^(Helper4ClosingCertificate.credit [1, 1, 1, 1, 1] sub+1)
  else 0
set_option maxHeartbeats 0 in
lemma mask_contains:∀ m q:Fin 32,
    (∀ k:Fin 5, m.val.testBit k.val=true→q.val.testBit k.val=true)→
      Nat.land q.val m.val=m.val:=by
  decide+kernel
set_option maxHeartbeats 0 in
lemma contains_antisymm:∀ m q:Fin 32,
    Nat.land q.val m.val=m.val→Nat.land m.val q.val=q.val→m.val=q.val:=by
  decide+kernel
set_option maxHeartbeats 0 in
lemma self_term:∀ m:Fin 32, term m.val m.val=64:=by
  decide+kernel
set_option maxHeartbeats 0 in
lemma positive_term:∀ m q:Fin 32,
    Nat.land q.val m.val=m.val→1≤term m.val q.val:=by
  decide+kernel
lemma terminal_contains (j:Fin 5) (fresh IP:List ℕ)
    (hfirst:∀ m∈fresh, m < 32∧m.testBit j.val=true∧
      ∀ k:Fin 5, k.val < j.val→m.testBit k.val=false)
    (hs:∀ q∈IP, q < 32∧q.testBit j.val=true)
    (m:ℕ) (hm:m∈fresh) (ht:terminal 5 j.val IP m=true):
    ∀ q∈IP, Nat.land q m=m:=by
  intro q hq
  have hmfirst:=hfirst m hm
  have hqbits:=hs q hq
  apply mask_contains ⟨m, hmfirst.1⟩ ⟨q, hqbits.1⟩
  intro k hk
  by_cases he:k.val=j.val
  · simpa only [he] using hqbits.2
  · have hjk:j.val < k.val:=by
      have hnot:¬ k.val < j.val:=by
        intro hlt
        have hf:=hmfirst.2.2 k hlt
        rw [hf] at hk
        contradiction
      omega
    have hfull:=of_decide_eq_true ht k hjk hk
    exact List.length_filter_eq_length_iff.mp hfull q hq
lemma weighted_count (rows:List ℕ) (w:ℕ→ℕ) (m:ℕ)
    (hpos:∀ q∈rows, 1≤w q) (heq:64≤w m):
    rows.length+63*(rows.filter (fun q=>decide (q=m))).length≤
      (rows.map w).sum:=by
  induction rows with
  | nil=>simp
  | cons q rows ih=>
    have hq:=hpos q (by simp)
    have ht:=ih (fun a ha=>hpos a (by simp [ha]))
    by_cases he:q=m
    · subst q
      simp only [List.length_cons, List.filter_cons, decide_true,
        ↓reduceIte, List.map_cons, List.sum_cons] at*
      omega
    · simp only [List.length_cons, List.filter_cons, he, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.map_cons, List.sum_cons]
      omega
lemma filter_mono (rows:List ℕ) (p q:ℕ→Bool)
    (h:∀ m∈rows, p m=true→q m=true):
    (rows.filter p).length≤(rows.filter q).length:=by
  induction rows with
  | nil=>simp
  | cons m rows ih=>
    have ht:∀ a∈rows, p a=true→q a=true:=
      fun a ha=>h a (by simp [ha])
    have hh:=ih ht
    have hm:=h m (by simp)
    cases hp:p m <;> cases hq:q m <;> simp_all
    omega
lemma terminal_count_bound (j:Fin 5) (fresh IP:List ℕ)
    (hf:fresh.Sublist IP)
    (hfirst:∀ m∈fresh, m < 32∧m.testBit j.val=true∧
      ∀ k:Fin 5, k.val < j.val→m.testBit k.val=false)
    (hs:∀ q∈IP, q < 32∧q.testBit j.val=true)
    (hu:∀ sub:Fin 32, 0 < sub.val→
      Helper4ClosingCertificate.uniformWeight sub.val IP≤128)
    (hlen:3≤IP.length):
    (fresh.filter (terminal 5 j.val IP)).length≤1:=by
  by_cases hempty:(fresh.filter (terminal 5 j.val IP))=[]
  · simp [hempty]
  · obtain ⟨m, hm⟩:=List.exists_mem_of_ne_nil _ hempty
    obtain ⟨hmfresh, hmterm⟩:=List.mem_filter.mp hm
    have hmfirst:=hfirst m hmfresh
    have hmzero:0 < m:=by
      by_contra hn
      have he:m=0:=by omega
      subst m
      simp at hmfirst
    have hcontains:=terminal_contains j fresh IP hfirst hs m hmfresh hmterm
    have hallEq:∀ q∈fresh, terminal 5 j.val IP q=true→q=m:=by
      intro q hq hqt
      have hqfirst:=hfirst q hq
      have hreverse:=terminal_contains j fresh IP hfirst hs q hq hqt
      exact contains_antisymm ⟨q, hqfirst.1⟩ ⟨m, hmfirst.1⟩
        (hreverse m (hf.subset hmfresh)) (hcontains q (hf.subset hq))
    have hfilter:=filter_mono fresh (terminal 5 j.val IP)
      (fun q=>decide (q=m)) (fun q hq ht=>decide_eq_true (hallEq q hq ht))
    have hsubfilter:=(hf.filter (fun q=>decide (q=m))).length_le
    have hweight:=weighted_count IP (term m) m
      (fun q hq=>positive_term ⟨m, hmfirst.1⟩ ⟨q, (hs q hq).1⟩ (hcontains q hq))
      (le_of_eq (self_term ⟨m, hmfirst.1⟩).symm)
    have hupper:=hu ⟨m, hmfirst.1⟩ hmzero
    change (IP.map (term m)).sum≤128 at hupper
    omega
lemma uniformWeight_append (sub:ℕ) (a b:List ℕ):
    Helper4ClosingCertificate.uniformWeight sub (a++b)=
      Helper4ClosingCertificate.uniformWeight sub a+
        Helper4ClosingCertificate.uniformWeight sub b:=by
  simp only [Helper4ClosingCertificate.uniformWeight, List.map_append, List.sum_append]
lemma uniformWeight_filter_le (sub:ℕ) (rows:List ℕ) (p:ℕ→Bool):
    Helper4ClosingCertificate.uniformWeight sub (rows.filter p)≤
      Helper4ClosingCertificate.uniformWeight sub rows:=by
  change ((rows.filter p).map (term sub)).sum≤(rows.map (term sub)).sum
  induction rows with
  | nil=>simp
  | cons m rows ih=>
    cases hp:p m <;> simp only [List.filter_cons, hp, Bool.false_eq_true,
      ↓reduceIte, List.map_cons, List.sum_cons]
    · omega
    · exact Nat.add_le_add_left ih _
end Helper4TerminalKraft
namespace Helper4TerminalSupport
open scoped BigOperators
open Helper4TerminalKraft
lemma supportRows_bits (rows:Fin 5→List ℕ)
    (hfirst:∀ j:Fin 5, ∀ m∈rows j, m < 32∧m.testBit j.val=true∧
      ∀ k:Fin 5, k.val < j.val→m.testBit k.val=false)
    (j:Fin 5):
    ∀ m∈Helper4TemporalAux.supportRows rows j, m < 32∧m.testBit j.val=true:=by
  intro m hm
  obtain hm | hm:=List.mem_append.mp hm
  · exact ⟨(hfirst j m hm).1, (hfirst j m hm).2.1⟩
  · obtain ⟨hm, hbit⟩:=List.mem_filter.mp hm
    obtain ⟨h, _, hmh⟩:=List.mem_flatMap.mp hm
    have hmember:m∈rows h:=by
      by_cases hlt:h.val < j.val
      · simpa only [hlt, ↓reduceIte] using hmh
      · simp only [hlt, ↓reduceIte, List.not_mem_nil] at hmh
    exact ⟨(hfirst h m hmember).1, hbit⟩
lemma supportRows_uniform_bound (rows:Fin 5→List ℕ) (sub:ℕ)
    (hglobal:(∑ h:Fin 5, Helper4ClosingCertificate.uniformWeight sub (rows h))≤128)
    (j:Fin 5):
    Helper4ClosingCertificate.uniformWeight sub (Helper4TemporalAux.supportRows rows j)≤128:=by
  have h0:=uniformWeight_filter_le sub (rows ⟨0, by decide⟩) (fun m=>m.testBit j.val)
  have h1:=uniformWeight_filter_le sub (rows ⟨1, by decide⟩) (fun m=>m.testBit j.val)
  have h2:=uniformWeight_filter_le sub (rows ⟨2, by decide⟩) (fun m=>m.testBit j.val)
  have h3:=uniformWeight_filter_le sub (rows ⟨3, by decide⟩) (fun m=>m.testBit j.val)
  have h4:=uniformWeight_filter_le sub (rows ⟨4, by decide⟩) (fun m=>m.testBit j.val)
  fin_cases j <;>
    simp_all [Helper4TemporalAux.supportRows, Helper4TemporalAux.priorRows,
      List.finRange, List.ofFn_succ, List.filter_append, uniformWeight_append, Fin.sum_univ_succ] <;>
    omega
lemma supportRows_terminal_count (rows:Fin 5→List ℕ)
    (hfirst:∀ j:Fin 5, ∀ m∈rows j, m < 32∧m.testBit j.val=true∧
      ∀ k:Fin 5, k.val < j.val→m.testBit k.val=false)
    (hu:∀ sub:Fin 32, 0 < sub.val→
      (∑ h:Fin 5, Helper4ClosingCertificate.uniformWeight sub.val (rows h))≤128)
    (j:Fin 5) (hlen:3≤(Helper4TemporalAux.supportRows rows j).length):
    ((rows j).filter (Helper4TemporalCore.terminal 5 j.val
      (Helper4TemporalAux.supportRows rows j))).length≤1:=by
  apply terminal_count_bound j (rows j) (Helper4TemporalAux.supportRows rows j)
  · exact List.sublist_append_left _ _
  · exact hfirst j
  · exact supportRows_bits rows hfirst j
  · intro sub hsub
    exact supportRows_uniform_bound rows sub.val (hu sub hsub) j
  · exact hlen
end Helper4TerminalSupport
namespace Helper4AllSubsetAdapter
open scoped BigOperators
abbrev cs:List ℕ:=[1, 1, 1, 1, 1]
def bitMask (f:Fin 5→Bool):Fin 32:=
  ⟨(if f 0 then 1 else 0)+(if f 1 then 2 else 0)+(if f 2 then 4 else 0)+
    (if f 3 then 8 else 0)+(if f 4 then 16 else 0), by
    split <;> split <;> split <;> split <;> split <;> decide⟩
set_option maxHeartbeats 0 in
lemma bitMask_bit:∀ f:Fin 5→Bool, ∀ k:Fin 5,
    (bitMask f).val.testBit k.val=f k:=by
  decide+kernel
def fullMask (rows:List ℕ):Fin 32:=
  bitMask (fun k=>rows.all (fun m=>m.testBit k.val))
lemma fullMask_bit (rows:List ℕ) (k:Fin 5):
    (fullMask rows).val.testBit k.val=(rows.all (fun m=>m.testBit k.val)):=
  bitMask_bit _ k
set_option maxHeartbeats 0 in
lemma land_of_bits:∀ m s:Fin 32,
    (∀ k:Fin 5, s.val.testBit k.val=true→m.val.testBit k.val=true)→
      Nat.land m.val s.val=s.val:=by
  decide+kernel
lemma fullMask_contains (rows:List ℕ) (m:ℕ) (hm:m∈rows) (hsmall:m < 32):
    Nat.land m (fullMask rows).val=(fullMask rows).val:=by
  apply land_of_bits ⟨m, hsmall⟩ (fullMask rows)
  intro k hk
  rw [fullMask_bit] at hk
  exact List.all_eq_true.mp hk m hm
lemma fullMask_nonzero (rows:List ℕ) (j:Fin 5)
    (hj:∀ m∈rows, m.testBit j.val=true):(fullMask rows).val≠0:=by
  have hb:(fullMask rows).val.testBit j.val=true:=by
    rw [fullMask_bit]
    exact List.all_eq_true.mpr hj
  intro he
  rw [he] at hb
  simp at hb
def nonFullCredit (j s m:ℕ):ℕ:=
  ((List.range 5).map fun k=>
    if decide (j < k) && m.testBit k && !(s.testBit k) then 1 else 0).sum
set_option maxHeartbeats 0 in
lemma uniform_dominates_nonFull:∀ j:Fin 5, ∀ m s:Fin 32,
    Helper4CanonicalEncoding.FirstBit j.val m.val→
    Nat.land m.val s.val=s.val→s.val.testBit j.val=true→
    2*2^(5 - nonFullCredit j.val s.val m.val)≤
      Helper4ClosingCertificate.weight m.val*
        2^(Helper4ClosingCertificate.credit cs s.val+1):=by
  intro j
  fin_cases j <;> decide+kernel
lemma insensitiveFull_is_full (j:ℕ) (rows:List ℕ) (k:Fin 5)
    (h:Helper4ProfileMembership.insensitiveFull 5 j k.val rows=true):
    (fullMask rows).val.testBit k.val=true:=by
  rw [fullMask_bit]
  apply List.all_eq_true.mpr
  have hc:Helper4ProfileMembership.columnCount rows k.val=rows.length:=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  exact List.length_filter_eq_length_iff.mp hc
lemma nonFull_le_effective (j:ℕ) (rows:List ℕ) (m:ℕ):
    nonFullCredit j (fullMask rows).val m≤
      Helper4ProfileMembership.effectiveCredit cs j rows m:=by
  unfold nonFullCredit Helper4ProfileMembership.effectiveCredit
  apply List.sum_le_sum
  intro k hk
  have hk5:k < 5:=List.mem_range.mp hk
  have hc:cs[k]! =1:=by
    have hkfin:(⟨k, hk5⟩:Fin 5).val=k:=rfl
    generalize he:(⟨k, hk5⟩:Fin 5)=kk at hkfin
    fin_cases kk <;> subst k <;> rfl
  change (if decide (j < k) && m.testBit k && !(fullMask rows).val.testBit k then 1 else 0)≤
    (if decide (j < k) && m.testBit k && !Helper4ProfileMembership.insensitiveFull 5 j k rows then cs[k]! else 0)
  rw [hc]
  by_cases he:Helper4ProfileMembership.insensitiveFull 5 j k rows=true
  · have hf:=insensitiveFull_is_full j rows ⟨k, hk5⟩ he
    simp [he, hf]
  · have heq:Helper4ProfileMembership.insensitiveFull 5 j k rows=false:=
      Bool.eq_false_iff.mpr he
    simp only [heq, Bool.not_false, Bool.and_true]
    split <;> split <;> simp_all
lemma totalWeight_eq (rows:List ℕ):Helper4ProfileMembership.totalWeight cs rows=
    Helper4ClosingCertificate.totalWeight rows:=rfl
lemma effective_weight_bound (j:Fin 5) (rows:List ℕ) (m:ℕ)
    (hm:m∈rows) (hfirst:Helper4CanonicalEncoding.FirstBit j.val m)
    (hj:∀ q∈rows, q.testBit j.val=true):
    2*2^(5 - Helper4ProfileMembership.effectiveCredit cs j.val rows m)≤
      Helper4ClosingCertificate.weight m*
        2^(Helper4ClosingCertificate.credit cs (fullMask rows).val+1):=by
  have hnon:=nonFull_le_effective j.val rows m
  have hp:2^(5 - Helper4ProfileMembership.effectiveCredit cs j.val rows m)≤
      2^(5 - nonFullCredit j.val (fullMask rows).val m):=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left hnon 5)
  apply (Nat.mul_le_mul_left 2 hp).trans
  apply uniform_dominates_nonFull j ⟨m, hfirst.1⟩ (fullMask rows) hfirst
    (fullMask_contains rows m hm hfirst.1)
  rw [fullMask_bit]
  exact List.all_eq_true.mpr hj
lemma double_sum (rows:List ℕ) (f:ℕ→ℕ):
    2*(rows.map f).sum=(rows.map fun m=>2*f m).sum:=by
  induction rows with
  | nil=>simp
  | cons a rows ih=>simp [Nat.mul_add, ih]
lemma effective_of_all_uniform (j:Fin 5) (rows:List ℕ)
    (hfirst:∀ m∈rows, Helper4CanonicalEncoding.FirstBit j.val m)
    (huk:∀ s:Fin 32, s.val≠0→
      Helper4ClosingCertificate.uniformWeight s.val rows≤128):
    Helper4ProfileMembership.effectiveKraft cs j.val rows=true:=by
  have hj:∀ m∈rows, m.testBit j.val=true:=fun m hm=>(hfirst m hm).2.1
  have hu:=huk (fullMask rows) (fullMask_nonzero rows j hj)
  have hs:2*(rows.map fun m=>
      2^(5 - Helper4ProfileMembership.effectiveCredit cs j.val rows m)).sum≤
      Helper4ClosingCertificate.uniformWeight (fullMask rows).val rows:=by
    rw [double_sum]
    unfold Helper4ClosingCertificate.uniformWeight
    apply List.sum_le_sum
    intro m hm
    rw [ite_eq_left (fullMask_contains rows m hm (hfirst m hm).1)]
    exact effective_weight_bound j rows m hm (hfirst m hm) hj
  unfold Helper4ProfileMembership.effectiveKraft
  apply decide_eq_true_eq.mpr
  change (rows.map fun m=>
    2^(5 - Helper4ProfileMembership.effectiveCredit cs j.val rows m)).sum≤64
  omega
set_option maxHeartbeats 0 in
lemma residual_single_le_uniform:∀ j k:Fin 5, ∀ m:Fin 32,
    Helper4ProfileMembership.residual cs j.val k.val [m.val]≤
      Helper4ClosingCertificate.uniformWeight (2^k.val) [m.val]:=by
  decide+kernel
lemma residual_le_uniform (j k:Fin 5) (rows:List ℕ)
    (hsmall:∀ m∈rows, m < 32):
    Helper4ProfileMembership.residual cs j.val k.val rows≤
      Helper4ClosingCertificate.uniformWeight (2^k.val) rows:=by
  unfold Helper4ProfileMembership.residual Helper4ClosingCertificate.uniformWeight
  apply List.sum_le_sum
  intro m hm
  simpa [Helper4ProfileMembership.residual, Helper4ClosingCertificate.uniformWeight] using
    residual_single_le_uniform j k ⟨m, hsmall m hm⟩
lemma good_of_local (j:Fin 5) (rows:List ℕ)
    (hfirst:∀ m∈rows, Helper4CanonicalEncoding.FirstBit j.val m)
    (hfr:rows.length≤2∨rows.length≤Helper4ProfileMembership.covered 5 j.val rows+1)
    (hw:Helper4ClosingCertificate.totalWeight rows≤128)
    (huk:∀ s:Fin 32, s.val≠0→
      Helper4ClosingCertificate.uniformWeight s.val rows≤128):
    Helper4ProfileMembership.good cs j.val rows=true:=by
  unfold Helper4ProfileMembership.good
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using hfr
    · apply decide_eq_true_eq.mpr
      change Helper4ProfileMembership.totalWeight cs rows≤128
      rw [totalWeight_eq]
      exact hw
  · apply List.all_eq_true.mpr
    intro k hk
    have hk5:k < 5:=List.mem_range.mp hk
    have hp:2^k < 32:=by
      have hx:2^k < 2^5:=Nat.pow_lt_pow_right (by decide) hk5
      exact hx
    have hne:2^k≠0:=Nat.ne_of_gt (Nat.two_pow_pos k)
    have hu:=huk ⟨2^k, hp⟩ hne
    have hr:=residual_le_uniform j ⟨k, hk5⟩ rows (fun m hm=>(hfirst m hm).1)
    exact decide_eq_true_eq.mpr (hr.trans hu)
lemma local_uniform (rows:Fin 5→List ℕ)
    (huk:∀ s:Fin 32, s.val≠0→
      (∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight s.val (rows j))≤128)
    (j:Fin 5) (s:Fin 32) (hs:s.val≠0):
    Helper4ClosingCertificate.uniformWeight s.val (rows j)≤128:=by
  have hl:Helper4ClosingCertificate.uniformWeight s.val (rows j)≤
      ∑ k:Fin 5, Helper4ClosingCertificate.uniformWeight s.val (rows k):=
    Finset.single_le_sum (f:=fun k:Fin 5=>Helper4ClosingCertificate.uniformWeight s.val (rows k))
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  exact hl.trans (huk s hs)
lemma local_weight (rows:Fin 5→List ℕ) (z:ℕ)
    (hw:32*z+∑ j:Fin 5, Helper4ClosingCertificate.totalWeight (rows j)≤128)
    (j:Fin 5):Helper4ClosingCertificate.totalWeight (rows j)≤128:=by
  have hl:Helper4ClosingCertificate.totalWeight (rows j)≤
      ∑ k:Fin 5, Helper4ClosingCertificate.totalWeight (rows k):=
    Finset.single_le_sum (f:=fun k:Fin 5=>Helper4ClosingCertificate.totalWeight (rows k))
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  omega
end Helper4AllSubsetAdapter
namespace Helper4AllSubsetFinal
open scoped BigOperators
lemma first_subset_mask_bound
    (rows:Fin 5→List ℕ) (z:ℕ)
    (hsort:∀ j:Fin 5, (rows j).Pairwise (·≤·))
    (hfirst:∀ j:Fin 5, ∀ m∈rows j, Helper4CanonicalEncoding.FirstBit j.val m)
    (hw:32*z+∑ j:Fin 5, Helper4ClosingCertificate.totalWeight (rows j)≤128)
    (hu:∀ sub:Fin 32, 0 < sub.val→
      (∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight sub.val (rows j))≤128)
    (hi:∀ j:Fin 5, Helper4TemporalCore.IntroProperty 5 j.val (rows j)
      (Helper4TemporalAux.supportRows rows j)):
    z+(∑ j:Fin 5, (rows j).length)≤11:=by
  have ht:∀ j:Fin 5, Helper4TemporalCore.TemporalProperty 5 j.val (rows j)
      (Helper4TemporalAux.supportRows rows j):=by
    intro j
    exact ⟨hi j, Helper4TerminalSupport.supportRows_terminal_count rows hfirst hu j⟩
  have hlocal:∀ j:Fin 5, ∀ sub:Fin 32, sub.val≠0→
      Helper4ClosingCertificate.uniformWeight sub.val (rows j)≤128:=by
    intro j sub hsub
    exact Helper4AllSubsetAdapter.local_uniform rows
      (fun s hs=>hu s (Nat.pos_of_ne_zero hs)) j sub hsub
  have hgood:∀ j:Fin 5, Helper4ProfileMembership.strongGood j.val (rows j)=true:=by
    intro j
    have hg:=Helper4AllSubsetAdapter.good_of_local j (rows j) (hfirst j)
      (Helper4TemporalBoolean.covered_of_whole (ht j))
      (Helper4AllSubsetAdapter.local_weight rows z hw j) (hlocal j)
    have he:=Helper4AllSubsetAdapter.effective_of_all_uniform j (rows j) (hfirst j) (hlocal j)
    have hp:=Helper4TemporalBoolean.temporal_of_whole (ht j)
    simp only [Helper4ProfileMembership.strongGood, hg, he, hp, Bool.and_true]
  apply Helper4CanonicalEncoding.sorted_temporal_mask_bound rows z
    (fun j=>Helper4FreshLength.length_bound_of_whole (ht j)) hsort hfirst hgood hw
    (hu ⟨4, by decide⟩ (by decide)) (hu ⟨8, by decide⟩ (by decide))
    (hu ⟨16, by decide⟩ (by decide)) ht
end Helper4AllSubsetFinal
namespace ListEncoding
lemma sum_indicator {α:Type} (l:List α) (P:α→Bool):
    (l.map fun a=>if P a then 1 else 0).sum=(l.filter P).length:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>
    cases h:P a <;> simp [h, ih, Nat.add_comm]
lemma filter_length {α:Type} {n:ℕ} (f:Fin n→α) (P:α→Bool):
    ((List.ofFn f).filter P).length=
      (Finset.univ.filter fun i=>P (f i)=true).card:=by
  rw [← sum_indicator]
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
lemma mapped_sum {α:Type} {n:ℕ} (f:Fin n→α) (w:α→ℕ):
    ((List.ofFn f).map w).sum=∑ i, w (f i):=by
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply]
lemma code_bounded {n:ℕ} (code:Fin n→Fin 32):
    ∀ m∈List.ofFn (fun i=>(code i).val), m < 32:=by
  intro m hm
  obtain ⟨i, rfl⟩:=List.mem_ofFn.mp hm
  exact (code i).isLt
lemma decode_nonempty:∀ a:Fin 32,
    (MaskDecode.decode 5 a).Nonempty↔0 < a.val:=by
  decide+kernel
lemma decode_mem {a:Fin 32} {j:Fin 5}:
    j∈MaskDecode.decode 5 a↔a.val.testBit j.val=true:=by
  simp [MaskDecode.decode]
end ListEncoding
namespace RawListWeights
open Helper4ClosingCertificate
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma credit_card:∀ a:Fin 32,
    credit [1, 1, 1, 1, 1] a.val=(MaskDecode.decode 5 a).card:=by
  decide+kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma land_decode:∀ a sub:Fin 32,
    Nat.land a.val sub.val=sub.val↔
      MaskDecode.decode 5 sub⊆MaskDecode.decode 5 a:=by
  decide+kernel
lemma totalWeight_eq {n:ℕ} (slots:Fin n→Finset (Fin 5))
    (code:Fin n→Fin 32) (hc:∀ i, MaskDecode.decode 5 (code i)=slots i):
    totalWeight (List.ofFn fun i=>(code i).val)=∑ i, 2^(5 - (slots i).card):=by
  unfold totalWeight
  rw [ListEncoding.mapped_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [weight, credit_card, hc]
lemma uniformWeight_eq {n:ℕ} (slots:Fin n→Finset (Fin 5))
    (code:Fin n→Fin 32) (hc:∀ i, MaskDecode.decode 5 (code i)=slots i)
    (sub:Fin 32):
    uniformWeight sub.val (List.ofFn fun i=>(code i).val)=
      ∑ i, if MaskDecode.decode 5 sub⊆slots i then
        2^((MaskDecode.decode 5 sub).card+1)*2^(5 - (slots i).card) else 0:=by
  unfold uniformWeight
  rw [ListEncoding.mapped_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [weight, credit_card, land_decode, hc, Nat.mul_comm]
lemma global_bound {n:ℕ} (slots:Fin n→Finset (Fin 5))
    (code:Fin n→Fin 32) (hc:∀ i, MaskDecode.decode 5 (code i)=slots i)
    (hg:(∑ i, (1 / 2:ℚ)^(2+(slots i).card))≤1):
    totalWeight (List.ofFn fun i=>(code i).val)≤128:=by
  rw [totalWeight_eq slots code hc]
  exact AC.Fj slots hg
lemma uniform_bound {n:ℕ} (slots:Fin n→Finset (Fin 5))
    (code:Fin n→Fin 32) (hc:∀ i, MaskDecode.decode 5 (code i)=slots i)
    (hu:∀ F:Finset (Fin 5), F.Nonempty→
      (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)
    (sub:Fin 32) (hs:0 < sub.val):
    uniformWeight sub.val (List.ofFn fun i=>(code i).val)≤128:=by
  rw [uniformWeight_eq slots code hc]
  exact AC.EB slots (MaskDecode.decode 5 sub)
    (hu _ ((ListEncoding.decode_nonempty sub).mpr hs))
end RawListWeights
namespace Az
lemma encoded_support_length {n:ℕ} (slots:Fin n→Finset (Fin 5))
    (code:Fin n→Fin 32) (hcode:∀ i, MaskDecode.decode 5 (code i)=slots i)
    (j:Fin 5):
    ((List.ofFn fun i=>(code i).val).filter fun m=>m.testBit j.val).length=
      IP slots j:=by
  rw [ListEncoding.filter_length]
  unfold IP
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hcode i]
  exact ListEncoding.decode_mem.symm
lemma encoded_columnCount {n:ℕ} (slots:Fin n→Finset (Fin 5))
    (code:Fin n→Fin 32) (hcode:∀ i, MaskDecode.decode 5 (code i)=slots i)
    (j k:Fin 5):
    Helper4TemporalCore.columnCount
      ((List.ofFn fun i=>(code i).val).filter fun m=>m.testBit j.val) k.val=
      Ci slots j k:=by
  unfold Helper4TemporalCore.columnCount
  rw [List.filter_filter, ListEncoding.filter_length]
  unfold Ci
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true]
  rw [← hcode i]
  exact and_comm.trans (and_congr ListEncoding.decode_mem.symm ListEncoding.decode_mem.symm)
lemma chronological_introProperty {n:ℕ} (slots:Fin n→Finset (Fin 5))
    (code:Fin n→Fin 32) (hcode:∀ i, MaskDecode.decode 5 (code i)=slots i)
    (ht:BO slots) (j:Fin 5):
    Helper4TemporalCore.IntroProperty 5 j.val
      ((List.ofFn fun i=>(code i).val).filter fun m=>
        decide (Helper4CanonicalEncoding.FirstBit j.val m))
      ((List.ofFn fun i=>(code i).val).filter fun m=>m.testBit j.val):=by
  intro m hm k hjk hmk hproper
  have hmraw:=(List.mem_filter.mp hm).1
  have hmfirst:Helper4CanonicalEncoding.FirstBit j.val m:=
    of_decide_eq_true (List.mem_filter.mp hm).2
  obtain ⟨i, rfl⟩:=List.mem_ofFn.mp hmraw
  obtain ⟨hbounded, hji, hfirst⟩:=hmfirst
  have hjmem:j∈slots i:=by
    rw [← hcode i]
    exact ListEncoding.decode_mem.mpr hji
  have hkmem:k∈slots i:=by
    rw [← hcode i]
    exact ListEncoding.decode_mem.mpr hmk
  have hpos:0 < Ci slots j k:=by
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjmem, hkmem⟩⟩
  have hproper':Ci slots j k < IP slots j:=by
    simpa only [encoded_columnCount slots code hcode, encoded_support_length slots code hcode]
      using hproper
  by_cases hone:Ci slots j k=1
  · refine ⟨k, hjk, le_rfl, hmk, ?_⟩
    simpa only [encoded_columnCount slots code hcode] using hone
  · have htwo:2≤Ci slots j k:=by omega
    have hfresh:∀ l:Fin 5, l < j→l∉slots i:=by
      intro l hlj hli
      have hlbit:(code i).val.testBit l.val=true:=by
        apply ListEncoding.decode_mem.mp
        simpa only [hcode i] using hli
      have hlfalse:=hfirst l hlj
      simp only [hlbit, Bool.true_eq_false] at hlfalse
    obtain ⟨l, hjl, hlk, hli, hlone, hlproper⟩:=
      ht i j k hjmem hfresh hjk hkmem htwo hproper'
    refine ⟨l, hjl, Nat.le_of_lt hlk, ?_, ?_⟩
    · apply ListEncoding.decode_mem.mp
      simpa only [hcode i] using hli
    · simpa only [encoded_columnCount slots code hcode] using hlone
end Az
namespace Az
abbrev RawListBound:Prop:=
  ∀ rows:List ℕ,
    (∀ m∈rows, m < 32)→
    Helper4ClosingCertificate.totalWeight rows≤128→
    (∀ sub:Fin 32, 0 < sub.val→
      Helper4ClosingCertificate.uniformWeight sub.val rows≤128)→
    (∀ j:Fin 5, Helper4TemporalCore.IntroProperty 5 j.val
      (rows.filter fun m=>decide (Helper4CanonicalEncoding.FirstBit j.val m))
      (rows.filter fun m=>m.testBit j.val))→
    rows.length≤11
lemma five_slots_bound (hcert:RawListBound) {n:ℕ}
    (slots:Fin n→Finset (Fin 5))
    (hg:(∑ i, (1 / 2:ℚ)^(2+(slots i).card))≤1)
    (hu:∀ F:Finset (Fin 5), F.Nonempty→
      (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)
    (ht:BO slots):n≤11:=by
  classical
  choose code hc using fun i=>MaskDecode.Df 5 (by omega) (slots i)
  have hb:=hcert (List.ofFn fun i=>(code i).val)
    (ListEncoding.code_bounded code)
    (RawListWeights.global_bound slots code hc hg)
    (RawListWeights.uniform_bound slots code hc hu)
    (chronological_introProperty slots code hc ht)
  simpa only [List.length_ofFn] using hb
lemma no_chronological_slots_of_raw_bound (hcert:RawListBound)
    {r:ℕ} (hr:r≤5) (slots:Fin (r+7)→Finset (Fin r))
    (hg:(∑ i, (1 / 2:ℚ)^(2+(slots i).card))≤1)
    (hu:∀ F:Finset (Fin r), F.Nonempty→
      (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)
    (ht:BO slots):False:=by
  by_cases hsmall:r≤4
  · obtain ⟨c, hc⟩:=DB hr slots hg hu ht
    exact no_profile_small hsmall c hc
  · have heq:r=5:=by omega
    subst r
    have:=five_slots_bound hcert slots hg hu ht
    omega
end Az
namespace Helper4MaskEntryBase
def firstBit (j m:ℕ):Bool:=
  m.testBit j && (List.range j).all (fun k=>!(m.testBit k))
def freshRows (masks:List ℕ) (j:Fin 5):List ℕ:=
  masks.filter (firstBit j.val)
def sortedRows (masks:List ℕ) (j:Fin 5):List ℕ:=
  (freshRows masks j).mergeSort (fun a b=>decide (a≤b))
def supportRows (masks:List ℕ) (j:Fin 5):List ℕ:=
  masks.filter (fun m=>m.testBit j.val)
def zeroCount (masks:List ℕ):ℕ:=
  (masks.filter (fun m=>decide (m=0))).length
end Helper4MaskEntryBase
namespace Helper4MaskEntryBasics
open Helper4MaskEntryBase
set_option maxHeartbeats 0 in
lemma firstBit_iff:∀ j:Fin 5, ∀ m:Fin 32,
    firstBit j.val m.val=true↔Helper4CanonicalEncoding.FirstBit j.val m.val:=by
  decide+kernel
lemma sortedRows_perm (masks:List ℕ) (j:Fin 5):
    (sortedRows masks j).Perm (freshRows masks j):=
  List.mergeSort_perm _ _
lemma sortedRows_sorted (masks:List ℕ) (j:Fin 5):
    (sortedRows masks j).Pairwise (·≤·):=by
  exact List.pairwise_mergeSort' (·≤·) (freshRows masks j)
lemma sortedRows_firstBit (masks:List ℕ)
    (hsmall:∀ m∈masks, m < 32) (j:Fin 5):
    ∀ m∈sortedRows masks j, Helper4CanonicalEncoding.FirstBit j.val m:=by
  intro m hm
  have hf:=(sortedRows_perm masks j).mem_iff.mp hm
  obtain ⟨hmasks, hb⟩:=List.mem_filter.mp hf
  exact (firstBit_iff j ⟨m, hsmall m hmasks⟩).mp hb
end Helper4MaskEntryBasics
namespace Helper4MaskEntryAggregation
open scoped BigOperators
open Helper4MaskEntryBase
set_option maxHeartbeats 0 in
lemma firstBit_partition:∀ m:Fin 32,
    (if m.val=0 then 1 else 0)+
      (∑ j:Fin 5, if firstBit j.val m.val then 1 else 0)=1:=by
  decide+kernel
lemma weighted_singleton (v:ℕ→ℕ) (m:ℕ) (hm:m < 32):
    (if m=0 then v 0 else 0)+
      (∑ j:Fin 5, if firstBit j.val m then v m else 0)=v m:=by
  have hp:=congrArg (fun a:ℕ=>a*v m) (firstBit_partition ⟨m, hm⟩)
  simp only [Nat.add_mul, Finset.sum_mul, ite_mul, one_mul, zero_mul] at hp
  by_cases hz:m=0
  · simpa only [hz] using hp
  · simpa only [hz, ↓reduceIte] using hp
lemma zeroCount_cons (m:ℕ) (masks:List ℕ):
    zeroCount (m::masks)=(if m=0 then 1 else 0)+zeroCount masks:=by
  by_cases hm:m=0 <;> simp [zeroCount, hm, Nat.add_comm]
lemma fresh_sum_cons (v:ℕ→ℕ) (m:ℕ) (masks:List ℕ) (j:Fin 5):
    ((freshRows (m::masks) j).map v).sum=
      (if firstBit j.val m then v m else 0)+((freshRows masks j).map v).sum:=by
  cases hb:firstBit j.val m <;> simp [freshRows, hb]
lemma fresh_weighted_partition (v:ℕ→ℕ) (masks:List ℕ)
    (hsmall:∀ m∈masks, m < 32):
    v 0*zeroCount masks+
      (∑ j:Fin 5, ((freshRows masks j).map v).sum)=(masks.map v).sum:=by
  induction masks with
  | nil=>simp [zeroCount, freshRows]
  | cons m masks ih=>
    have hi:=ih (fun q hq=>hsmall q (by simp [hq]))
    have hp:=weighted_singleton v m (hsmall m (by simp))
    rw [zeroCount_cons, Nat.mul_add]
    simp_rw [fresh_sum_cons]
    rw [Finset.sum_add_distrib]
    simp only [List.map_cons, List.sum_cons, mul_ite, Nat.mul_one, Nat.mul_zero]
    omega
lemma sorted_map_sum (v:ℕ→ℕ) (masks:List ℕ) (j:Fin 5):
    ((sortedRows masks j).map v).sum=((freshRows masks j).map v).sum:=by
  exact ((List.mergeSort_perm (freshRows masks j) (fun a b=>decide (a≤b))).map v).sum_eq
lemma sorted_weighted_partition (v:ℕ→ℕ) (masks:List ℕ)
    (hsmall:∀ m∈masks, m < 32):
    v 0*zeroCount masks+
      (∑ j:Fin 5, ((sortedRows masks j).map v).sum)=(masks.map v).sum:=by
  simp_rw [sorted_map_sum]
  exact fresh_weighted_partition v masks hsmall
lemma ones_sum (rows:List ℕ):(rows.map fun _=>(1:ℕ)).sum=rows.length:=by
  induction rows with
  | nil=>rfl
  | cons m rows ih=>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    omega
lemma length_partition (masks:List ℕ) (hsmall:∀ m∈masks, m < 32):
    zeroCount masks+(∑ j:Fin 5, (sortedRows masks j).length)=masks.length:=by
  have h:=sorted_weighted_partition (fun _=>1) masks hsmall
  simpa only [ones_sum, Nat.one_mul] using h
lemma weight_partition (masks:List ℕ) (hsmall:∀ m∈masks, m < 32):
    32*zeroCount masks+
      (∑ j:Fin 5, Helper4ClosingCertificate.totalWeight (sortedRows masks j))=
        Helper4ClosingCertificate.totalWeight masks:=by
  exact sorted_weighted_partition Helper4ClosingCertificate.weight masks hsmall
lemma uniform_partition (masks:List ℕ) (hsmall:∀ m∈masks, m < 32)
    (sub:Fin 32) (hsub:sub.val≠0):
    (∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight sub.val (sortedRows masks j))=
      Helper4ClosingCertificate.uniformWeight sub.val masks:=by
  let v:ℕ→ℕ:=fun m=>if Nat.land m sub.val=sub.val then
    Helper4ClosingCertificate.weight m*
      2^(Helper4ClosingCertificate.credit [1, 1, 1, 1, 1] sub.val+1) else 0
  have hz:v 0=0:=by simp [v, Ne.symm hsub]
  have h:=sorted_weighted_partition v masks hsmall
  rw [hz, Nat.zero_mul, Nat.zero_add] at h
  exact h
end Helper4MaskEntryAggregation
namespace Helper4MaskEntryTransport
open Helper4MaskEntryBase
lemma count_filter_if (m:ℕ) (rows:List ℕ) (p:ℕ→Bool):
    (rows.filter p).count m=if p m then rows.count m else 0:=by
  cases hp:p m
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply List.count_eq_zero_of_not_mem
    intro hm
    have hbit:=(List.mem_filter.mp hm).2
    rw [hp] at hbit
    contradiction
  · simpa only [hp, ↓reduceIte] using (List.count_filter hp:(rows.filter p).count m=rows.count m)
lemma count_sorted (masks:List ℕ) (j:Fin 5) (m:ℕ):
    (sortedRows masks j).count m=if firstBit j.val m then masks.count m else 0:=by
  rw [(Helper4MaskEntryBasics.sortedRows_perm masks j).count_eq m]
  exact count_filter_if m masks _
def coefficient (j:Fin 5) (m:ℕ):ℕ:=
  (if firstBit j.val m then 1 else 0)+
    ((List.finRange 5).map fun h=>if h.val < j.val then
      if m.testBit j.val then (if firstBit h.val m then 1 else 0) else 0 else 0).sum
set_option maxHeartbeats 0 in
lemma coefficient_eq:∀ j:Fin 5, ∀ m:Fin 32,
    coefficient j m.val=if m.val.testBit j.val then 1 else 0:=by
  decide+kernel
lemma count_grouped (masks:List ℕ) (j:Fin 5) (m:ℕ):
    (Helper4TemporalAux.supportRows (sortedRows masks) j).count m=
      coefficient j m*masks.count m:=by
  cases hb:m.testBit j.val <;> fin_cases j <;>
    simp_all [Helper4TemporalAux.supportRows, Helper4TemporalAux.priorRows,
      List.finRange, List.ofFn_succ, List.filter_append, List.count_append,
      count_filter_if, count_sorted, coefficient, Nat.add_mul, ite_mul]
lemma supportRows_perm (masks:List ℕ) (hsmall:∀ m∈masks, m < 32) (j:Fin 5):
    (Helper4TemporalAux.supportRows (sortedRows masks) j).Perm (supportRows masks j):=by
  apply List.perm_iff_count.mpr
  intro m
  rw [count_grouped]
  change coefficient j m*masks.count m=(masks.filter (fun n=>n.testBit j.val)).count m
  rw [count_filter_if]
  by_cases hm:m∈masks
  · rw [coefficient_eq j ⟨m, hsmall m hm⟩]
    cases m.testBit j.val <;> simp
  · rw [List.count_eq_zero_of_not_mem hm]
    simp
lemma intro_transport {b j:ℕ} {fresh fresh' IP support':List ℕ}
    (hf:fresh'.Perm fresh) (hs:support'.Perm IP)
    (hi:Helper4TemporalCore.IntroProperty b j fresh IP):
    Helper4TemporalCore.IntroProperty b j fresh' support':=by
  intro m hm k hj hk hproper
  have hmold:m∈fresh:=hf.mem_iff.mp hm
  have hcolumns:∀ q:ℕ,
      Helper4TemporalCore.columnCount support' q=Helper4TemporalCore.columnCount IP q:=
    fun q=>by
      change (support'.filter (fun n:ℕ=>n.testBit q)).length=
        (IP.filter (fun n:ℕ=>n.testBit q)).length
      exact (hs.filter (fun n:ℕ=>n.testBit q)).length_eq
  have hlength:=hs.length_eq
  have holdproper:Helper4TemporalCore.columnCount IP k.val < IP.length:=by
    rw [← hcolumns k.val, ← hlength]
    exact hproper
  obtain ⟨l, hjl, hlk, hml, hcol⟩:=hi m hmold k hj hk holdproper
  exact ⟨l, hjl, hlk, hml, (hcolumns l.val).trans hcol⟩
lemma sortedRows_intro (masks:List ℕ) (hsmall:∀ m∈masks, m < 32)
    (hi:∀ j:Fin 5, Helper4TemporalCore.IntroProperty 5 j.val
      (freshRows masks j) (supportRows masks j)):
    ∀ j:Fin 5, Helper4TemporalCore.IntroProperty 5 j.val
      (sortedRows masks j) (Helper4TemporalAux.supportRows (sortedRows masks) j):=by
  intro j
  exact intro_transport (Helper4MaskEntryBasics.sortedRows_perm masks j)
    (supportRows_perm masks hsmall j) (hi j)
end Helper4MaskEntryTransport
namespace Helper4MaskEntryFinal
open scoped BigOperators
open Helper4MaskEntryBase
lemma mask_list_bound (masks:List ℕ)
    (hsmall:∀ m∈masks, m < 32)
    (hw:Helper4ClosingCertificate.totalWeight masks≤128)
    (hu:∀ sub:Fin 32, 0 < sub.val→
      Helper4ClosingCertificate.uniformWeight sub.val masks≤128)
    (hi:∀ j:Fin 5, Helper4TemporalCore.IntroProperty 5 j.val
      (freshRows masks j) (supportRows masks j)):
    masks.length≤11:=by
  have hgroupWeight:32*zeroCount masks+
      (∑ j:Fin 5, Helper4ClosingCertificate.totalWeight (sortedRows masks j))≤128:=by
    rw [Helper4MaskEntryAggregation.weight_partition masks hsmall]
    exact hw
  have hgroupUniform:∀ sub:Fin 32, 0 < sub.val→
      (∑ j:Fin 5, Helper4ClosingCertificate.uniformWeight sub.val (sortedRows masks j))≤128:=by
    intro sub hsub
    rw [Helper4MaskEntryAggregation.uniform_partition masks hsmall sub (Nat.ne_of_gt hsub)]
    exact hu sub hsub
  have hb:=Helper4AllSubsetFinal.first_subset_mask_bound (sortedRows masks) (zeroCount masks)
    (Helper4MaskEntryBasics.sortedRows_sorted masks)
    (Helper4MaskEntryBasics.sortedRows_firstBit masks hsmall)
    hgroupWeight hgroupUniform (Helper4MaskEntryTransport.sortedRows_intro masks hsmall hi)
  rw [Helper4MaskEntryAggregation.length_partition masks hsmall] at hb
  exact hb
end Helper4MaskEntryFinal
namespace Az
lemma raw_list_bound:RawListBound:=by
  intro rows hsmall hw hu hi
  apply Helper4MaskEntryFinal.mask_list_bound rows hsmall hw hu
  intro j m hm k hjk hbit hproper
  have hmrows:m∈rows:=(List.mem_filter.mp hm).1
  have hfirst:Helper4CanonicalEncoding.FirstBit j.val m:=
    (Helper4MaskEntryBasics.firstBit_iff j ⟨m, hsmall m hmrows⟩).mp
      (List.mem_filter.mp hm).2
  exact hi j m (List.mem_filter.mpr ⟨hmrows, decide_eq_true hfirst⟩)
    k hjk hbit hproper
lemma no_chronological_slots {r:ℕ} (hr:r≤5)
    (slots:Fin (r+7)→Finset (Fin r))
    (hg:(∑ i, (1 / 2:ℚ)^(2+(slots i).card))≤1)
    (hu:∀ F:Finset (Fin r), F.Nonempty→
      (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)
    (ht:BO slots):False:=
  no_chronological_slots_of_raw_bound raw_list_bound hr slots hg hu ht
end Az
namespace FinalStep
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma refutation_of_no_slots
    (hnumeric:∀ r:ℕ, r≤5→∀ slots:Fin (r+7)→Finset (Fin r),
      (∑ i, (1 / 2:ℚ)^(2+(slots i).card)≤1)→
      (∀ F:Finset (Fin r), F.Nonempty→
        (∑ i, if F⊆slots i then (1 / 2:ℚ)^(1+(slots i \ F).card) else 0)≤1)→
      Az.BO slots→False):
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v:Fin 12=>decide (u≠v)) 40:=by
  intro hr
  obtain ⟨C,hC,hsize,ht⟩:=Ad.De (by decide) hr
  obtain ⟨n,D,hn,hupper,hmin,htD,hsizeD,hshape,hsecondary,hraw,hleast⟩:=
    Am.Dz
      12 C hC ht (by omega)
  obtain ⟨hn7,slots,hglobal,hforce,hchron⟩:=
    Ab.regular_minimum_slots n (by omega) hupper D hmin htD hshape hraw hsizeD
  generalize hrEq:n-7=r at slots hglobal hforce hchron
  have hr5:r≤5:=by omega
  have hnEq:n=r+7:=by omega
  subst n
  exact hnumeric r hr5 slots hglobal hforce hchron
end FinalStep
namespace FinalStep
lemma assembly_refutation:
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v:Fin 12=>decide (u≠v)) 40:=by
  apply refutation_of_no_slots
  intro r hr slots hg hu ht
  exact Az.no_chronological_slots hr slots hg hu ht
end FinalStep
end PEqualNP.Outside.L_meta_18264

theorem PEqualNP.Outside.L_meta_18264 :
    ¬ PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 12 => decide (u ≠ v)) 40 := by
  exact PEqualNP.Outside.L_meta_18264.FinalStep.assembly_refutation
