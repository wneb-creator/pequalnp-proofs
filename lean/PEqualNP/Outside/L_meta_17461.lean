import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17461

def pg3Enc (e : Fin 7 ≃ Fin 7) (flip : Fin 7 → Bool) (l : Fin 7 × Bool) : Nat :=
  2 * (e l.1).val + (l.2 ^^ flip l.1).toNat

def pg3Used (t : Fin 12 → Nat) (i : Nat) : Nat :=
  ((List.ofFn t).take i).foldl (fun k n => max k (n / 2 + 1)) 0

theorem pg3Used_succ (t : Fin 12 → Nat) (i : Fin 12) :
    pg3Used t (i.val+1) = max (pg3Used t i.val) (t i/2+1) := by
  unfold pg3Used
  rw [List.take_succ_eq_append_getElem (l := List.ofFn t) (i := i.val) (by simp)]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.getElem_ofFn]

theorem pg3Enc_opp (e : Fin 7 ≃ Fin 7) (f : Fin 7 → Bool) (g : Fin 7) (b : Bool) :
    pg3Enc e f (g,!b) = pg3Enc e f (g,b) ^^^ 1 := by
  have h₀ := Nat.xor_one_of_even (n := 2*(e g).val) ⟨(e g).val, by omega⟩
  have h₁ := Nat.xor_one_of_odd (n := 2*(e g).val+1) ⟨(e g).val,rfl⟩
  cases b <;> cases h : f g <;> simp [pg3Enc, h, h₀, h₁]

theorem pg3Enc_div (e : Fin 7 ≃ Fin 7) (f : Fin 7 → Bool) (z : Fin 7 × Bool) :
    pg3Enc e f z / 2 = (e z.1).val := by
  unfold pg3Enc
  have := Bool.toNat_lt (z.2 ^^ f z.1)
  omega

theorem pg3Enc_injective (e : Fin 7 ≃ Fin 7) (f : Fin 7 → Bool) :
    Function.Injective (pg3Enc e f) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hg := congrArg (· / 2) h
  simp only [pg3Enc_div] at hg
  have hij := e.injective (Fin.ext hg)
  subst j
  cases b <;> cases c <;> cases hf : f i <;> simp_all [pg3Enc]

private abbrev NSlot := Fin 7 × Bool
private abbrev NLabel := (Fin 7 ≃ Fin 7) × (Fin 7 → Bool)
private abbrev NLabel.e (L : NLabel) := L.1
private abbrev NLabel.f (L : NLabel) := L.2

private def NLabel.code (L : NLabel) := pg3Enc L.e L.f

private def NFix (u : Nat) (L M : NLabel) : Prop :=
  ∀ z, L.code z / 2 < u → M.code z = L.code z

private theorem NLabel.seat (L : NLabel) (u : Nat) (z : NSlot) :
    ∃ M : NLabel, NFix u L M ∧ M.code z < min 14 (2*u+1) := by
  classical
  have hdiv : L.code z / 2 = (L.e z.1).val := pg3Enc_div ..
  have hlt := (L.e z.1).isLt
  by_cases h : (L.e z.1).val < u
  · exact ⟨L, fun _ _ => rfl, by omega⟩
  · let v : Fin 7 := ⟨u, by omega⟩
    let M : NLabel := ⟨L.e.trans (Equiv.swap (L.e z.1) v),
                       fun g => if g = z.1 then z.2 else L.f g⟩
    refine ⟨M, ?_, ?_⟩
    · intro x hx
      have hdx : L.code x / 2 = (L.e x.1).val := pg3Enc_div ..
      have hne : L.e x.1 ≠ L.e z.1 := by
        intro he
        rw [he] at hdx
        omega
      have hnev : L.e x.1 ≠ v := by
        intro he
        rw [he] at hdx
        change L.code x / 2 = u at hdx
        omega
      have hn : x.1 ≠ z.1 := fun h' => hne (congrArg L.e h')
      simp [M, NLabel.code, NLabel.e, NLabel.f, pg3Enc, hn, Equiv.swap_apply_of_ne_of_ne hne hnev]
    · simp [M, NLabel.code, NLabel.e, NLabel.f, pg3Enc, v]
      omega

private def NLabel.sorted (L : NLabel) (p : NSlot × NSlot) : Nat × Nat :=
  (min (L.code p.1) (L.code p.2), max (L.code p.1) (L.code p.2))

private def NCanonical (u : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (s,t)::xs =>
    s < min 14 (2*u+1) ∧ t < min 14 (2*(max u (s/2+1))+1) ∧
      NCanonical (max u (t/2+1)) xs

private theorem nNormAux (xs : List (NSlot × NSlot)) (u : Nat) (L : NLabel) :
    ∃ M : NLabel, NFix u L M ∧ NCanonical u (xs.map M.sorted) := by
  induction xs generalizing u L with
  | nil => exact ⟨L, fun _ _ => rfl, trivial⟩
  | cons p xs ih =>
    obtain ⟨A, hA, ha⟩ := L.seat u p.1
    let k := max u (A.code p.1 / 2 + 1)
    obtain ⟨B, hB, hb⟩ := A.seat k p.2
    have hba : B.code p.1 = A.code p.1 := hB _ (by dsimp [k]; omega)
    let v := max k (B.code p.2 / 2 + 1)
    obtain ⟨M, hM, hcan⟩ := ih v B
    have hma : M.code p.1 = A.code p.1 :=
      (hM _ (by dsimp [v,k]; omega)).trans hba
    have hmb : M.code p.2 = B.code p.2 := hM _ (by dsimp [v]; omega)
    refine ⟨M, ?_, ?_⟩
    · intro z hz
      have heA := hA z hz
      have heB := hB z (by dsimp [k]; omega)
      have heM := hM z (by dsimp [v,k]; omega)
      exact heM.trans (heB.trans heA)
    · simp only [List.map_cons, NLabel.sorted, hma, hmb, NCanonical]
      have hv : max u (max (A.code p.1) (B.code p.2) / 2 + 1) = v := by
        dsimp [v,k]; omega
      refine ⟨by omega, ?_, hv ▸ hcan⟩
      dsimp [k] at hb
      omega

private theorem nBounds (xs : List (Nat × Nat)) (u i : Nat) (hi : i < xs.length)
    (h : NCanonical u xs) :
    let k := ((xs.take i).map Prod.snd).foldl (fun d n => max d (n/2+1)) u
    xs[i].1 < min 14 (2*k+1) ∧ xs[i].2 < min 14 (2*(max k (xs[i].1/2+1))+1) := by
  induction xs generalizing u i with
  | nil => simp at hi
  | cons p ts ih =>
    obtain ⟨a,b⟩ := p
    rcases h with ⟨hs,ht,h⟩
    cases i with
    | zero => exact ⟨hs,ht⟩
    | succ i => exact ih _ i (by simpa using hi) h

theorem pg3NormalizeSlots (O : Fin 12 → Finset (Fin 7 × Bool))
    (hpos : ∀ i, (O i).Nonempty) (hcap : ∀ i, (O i).card ≤ 2)
    (hop : ∀ i g, (g,false) ∈ O i → (g,true) ∉ O i) :
    ∃ (e : Fin 7 ≃ Fin 7) (flip : Fin 7 → Bool) (s t : Fin 12 → Nat),
      (∀ i l, l ∈ O i ↔ pg3Enc e flip l = s i ∨ pg3Enc e flip l = t i) ∧
      ∀ i, s i < min 14 (2*pg3Used t i.val+1) ∧
        t i < min 14 (2*(max (pg3Used t i.val) (s i/2+1))+1) ∧
        s i ≤ t i ∧ (s i = t i ∨ s i/2 ≠ t i/2) := by
  classical
  have hpair (i) : ∃ a b, O i = {a,b} := by
    have h₁ := (hpos i).card_pos
    have h₂ := hcap i
    rcases (show (O i).card = 1 ∨ (O i).card = 2 by omega) with h | h
    · obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
      exact ⟨a,a,by simpa using ha⟩
    · obtain ⟨a,b,_,h⟩ := Finset.card_eq_two.mp h
      exact ⟨a,b,h⟩
  choose a b hab using hpair
  let pairs := List.ofFn fun i => (a i,b i)
  obtain ⟨L, _, hL⟩ := nNormAux pairs 0 ⟨Equiv.refl _, fun _ => false⟩
  let s := fun i => (L.sorted (a i,b i)).1
  let t := fun i => (L.sorted (a i,b i)).2
  refine ⟨L.e,L.f,s,t,?_,?_⟩
  · intro i l
    simp only [hab i, Finset.mem_insert, Finset.mem_singleton]
    change l = a i ∨ l = b i ↔
      L.code l = min (L.code (a i)) (L.code (b i)) ∨
        L.code l = max (L.code (a i)) (L.code (b i))
    by_cases h : L.code (a i) ≤ L.code (b i)
    · rw [min_eq_left h, max_eq_right h]
      simp only [NLabel.code, (pg3Enc_injective L.e L.f).eq_iff]
    · have hh := Nat.le_of_not_ge h
      rw [min_eq_right hh, max_eq_left hh]
      simp only [NLabel.code, (pg3Enc_injective L.e L.f).eq_iff, or_comm]
  · intro i
    have hbounds := nBounds (pairs.map L.sorted) 0 i.val (by simp [pairs]) hL
    have hu : ((pairs.map L.sorted).take i.val).map Prod.snd = (List.ofFn t).take i.val := by
      simp [pairs, t]
    simp only [hu] at hbounds
    have hh : s i < min 14 (2*pg3Used t i.val+1) ∧
        t i < min 14 (2*(max (pg3Used t i.val) (s i/2+1))+1) := by
      simpa only [pairs, List.getElem_map, List.getElem_ofFn, s,t,pg3Used] using hbounds
    refine ⟨hh.1, hh.2, ?_, ?_⟩
    · dsimp [s,t,NLabel.sorted]; omega
    · have hsep : (a i).1 = (b i).1 → a i = b i := by
        rcases ha : a i with ⟨g,x⟩
        rcases hb : b i with ⟨k,y⟩
        dsimp only
        rintro rfl
        have hp := hop i g
        rw [hab i, ha, hb] at hp
        cases x <;> cases y <;> simp_all
      by_cases heq : a i = b i
      · left; simp [s,t,NLabel.sorted,heq]
      · right
        have hne : (L.e (a i).1).val ≠ (L.e (b i).1).val :=
          fun h => heq (hsep (L.e.injective (Fin.ext h)))
        have ha : L.code (a i)/2 = (L.e (a i).1).val := pg3Enc_div ..
        have hb : L.code (b i)/2 = (L.e (b i).1).val := pg3Enc_div ..
        dsimp only [s,t,NLabel.sorted]
        omega

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461

def rcData : List (Nat × Nat) := [(0, 35777249544923), (1, 16836275385376), (2, 70560147653389), (2, 263891376406528), (1, 8416809216), (16, 281466386776064), (36, 792739058), (40, 1953679), (16, 5703717727342), (260, 205347809787920), (128, 10725122781296), (1280, 123205914198913)]
def rcFull : Nat := 281474976710655
abbrev Entry := Nat × Nat × Nat
def rcOpp (s : Nat) := s ^^^ 1
def rcHit (s : Nat) (x : Entry) := s == x.1 || s == x.2.1
def rcEdges (m s t : Nat) (xs : List Entry) : Bool :=
  xs.zipIdx.all (fun (v,i) => !m.testBit i || rcHit (rcOpp s) v || rcHit (rcOpp t) v)
def rcHits : List Entry → Nat → Nat
  | [], _ => 0
  | v::vs, s => (if rcHit s v then v.2.2 else 0) ||| rcHits vs s
def rcBad (v : Entry) (xs : List Entry) (s : Nat) : Nat :=
  let outside := rcFull &&& (rcFull ^^^ v.2.2)
  if v.1 == s then outside &&& (if v.2.1 == s then rcFull else rcHits xs v.2.1)
  else if v.2.1 == s then outside &&& rcHits xs v.1 else 0
def rcF (xs : List Entry) (s : Nat) := (xs.map fun v => rcBad v xs s).foldr (· ||| ·) 0
def rcRows (xs : List Entry) (k : Nat) : Bool :=
  (List.range k).all fun g =>
    let l := 2*g
    let r := 2*g+1
    let fl := rcF xs l
    let fr := rcF xs r
    (fl &&& rcHits xs l == 0) && (fr &&& rcHits xs r == 0) && (fl &&& fr == 0)

def rcSearch (xs : List Entry) (used : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (e, c)::rest =>
    (List.range (min 14 (2*used+1))).any fun s =>
      let k := max used (s/2+1)
      (List.range (min 14 (2*k+1))).any fun t =>
        let k' := max k (t/2+1)
        let xs' := xs ++ [(s,t,c)]
        (s ≤ t) && (s == t || s/2 != t/2) && rcEdges e s t xs && rcRows xs' k' &&
          rcSearch xs' k' rest

def rcReal (xs : List Entry) : Prop := ∀ r : Nat, rcFull.testBit r = true →
  ∃ f : Nat → Bool, (∀ g, f (2*g) = true → f (2*g+1) = false) ∧
    ∀ x ∈ xs, x.2.2.testBit r = true ↔ f x.1 = false ∧ f x.2.1 = false

theorem rcReal_sub {xs ys : List Entry} (h : ∀ v ∈ xs, v ∈ ys) (hy : rcReal ys) : rcReal xs := by
  intro r hr
  obtain ⟨f,hf,he⟩ := hy r hr
  exact ⟨f,hf,fun v hv => he v (h v hv)⟩

theorem rcHits_iff (xs : List Entry) (s r : Nat) : (rcHits xs s).testBit r = true ↔
    ∃ x ∈ xs, rcHit s x = true ∧ x.2.2.testBit r = true := by
  induction xs with
  | nil => simp [rcHits]
  | cons x l ih =>
    by_cases h : rcHit s x = true <;> simp [rcHits,h,ih]

theorem rcF_iff (xs : List Entry) (s r : Nat) : (rcF xs s).testBit r = true ↔
    ∃ x ∈ xs, (rcBad x xs s).testBit r = true := by
  suffices ∀ (t : List Entry), ((t.map fun x => rcBad x xs s).foldr (· ||| ·) 0).testBit r = true ↔
      ∃ x ∈ t, (rcBad x xs s).testBit r = true by apply this
  intro t
  induction t with
  | nil => simp
  | cons x l ih => simp [ih]

theorem rcRows_true (xs : List Entry) (k : Nat) (h : rcReal xs) : rcRows xs k = true := by
  apply List.all_eq_true.mpr
  intro g _
  have both (s t : Nat) (r : Nat) (f : Nat → Bool)
      (hspec : ∀ x ∈ xs, x.2.2.testBit r = true ↔ f x.1 = false ∧ f x.2.1 = false) :
      ((rcHits xs s).testBit r = true → f s = false) ∧
      ((rcF xs t).testBit r = true → f t = true) := by
    have hit (w : Nat) (hw : (rcHits xs w).testBit r = true) : f w = false := by
      obtain ⟨v,hv,he,hb⟩ := (rcHits_iff ..).mp hw
      rcases (by simpa [rcHit] using he : w = v.1 ∨ w = v.2.1) with rfl|rfl
      · exact ((hspec v hv).mp hb).1
      · exact ((hspec v hv).mp hb).2
    refine ⟨hit s, ?_⟩
    intro ht
    obtain ⟨v,hv,hs⟩ := (rcF_iff ..).mp ht
    simp only [rcBad, beq_iff_eq] at hs
    by_contra z
    have z' : f t = false := Bool.eq_false_iff.mpr z
    split_ifs at hs with he he' he' <;> try simp only [Nat.testBit_and, Bool.and_eq_true, Nat.testBit_xor] at hs
    · obtain ⟨⟨hr, hn⟩, _⟩ := hs
      have := (hspec v hv).mpr ⟨he ▸ z', he' ▸ z'⟩
      simp [hr,this] at hn
    · obtain ⟨⟨hr, hn⟩, h₂⟩ := hs
      have := (hspec v hv).mpr ⟨he ▸ z', hit _ h₂⟩
      simp [hr,this] at hn
    · obtain ⟨⟨hr, hn⟩, h₁⟩ := hs
      have := (hspec v hv).mpr ⟨hit _ h₁, he' ▸ z'⟩
      simp [hr,this] at hn
    · simp at hs
  have inFull (s r : Nat) (hs : (rcF xs s).testBit r = true) : rcFull.testBit r = true := by
    obtain ⟨v, _, hb⟩ := (rcF_iff ..).mp hs
    unfold rcBad at hb
    split_ifs at hb <;> simp only [Nat.testBit_and, Bool.and_eq_true, Nat.zero_testBit] at hb <;> tauto
  have disjHit (s : Nat) : (rcF xs s &&& rcHits xs s) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro r
    simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_imp]
    intro hr
    obtain ⟨f,_,hf⟩ := h r (inFull _ _ hr)
    obtain ⟨h1,h2⟩ := both s s r f hf
    have := h2 hr
    exact Bool.eq_false_iff.mpr (fun he => Bool.noConfusion ((h1 he).symm.trans this))
  have opps : (rcF xs (2*g) &&& rcF xs (2*g+1)) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro r
    simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_imp]
    intro h1
    obtain ⟨f,ho,hf⟩ := h r (inFull _ _ h1)
    have hh := (both 0 (2*g) r f hf).2 h1
    exact Bool.eq_false_iff.mpr (fun h2 => by have := (both 0 (2*g+1) r f hf).2 h2; have := ho g hh; grind)
  simp [disjHit,opps]

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461

theorem pg3SearchOfModel (s t : Fin 12 → Nat)
    (hcanon : ∀ i, s i < min 14 (2*pg3Used t i.val+1) ∧
      t i < min 14 (2*(max (pg3Used t i.val) (s i/2+1))+1) ∧
      s i ≤ t i ∧ (s i = t i ∨ s i/2 ≠ t i/2))
    (real : rcReal (List.ofFn fun i : Fin 12 => (s i,t i,rcData[i.val]!.2)))
    (edges : ∀ j, rcEdges rcData[j.val]!.1 (s j) (t j)
      ((List.ofFn fun i : Fin 12 => (s i,t i,rcData[i.val]!.2)).take j.val) = true) :
    rcSearch [] 0 rcData = true := by
  let xs := List.ofFn fun i : Fin 12 => (s i,t i,rcData[i.val]!.2)
  have hlen : rcData.length = 12 := rfl
  have aux (n k : Nat) (h : n+k=12) :
      rcSearch (xs.take n) (pg3Used t n) (rcData.drop n) = true := by
    induction k generalizing n with
    | zero =>
      have hn : n=12 := by omega
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
    | succ k ih =>
      let i : Fin 12 := ⟨n, by omega⟩
      have hn : n < rcData.length := by omega
      rw [List.drop_eq_getElem_cons hn, rcSearch]
      obtain ⟨hs,ht,hst,hd⟩ := hcanon i
      apply List.any_eq_true.mpr
      refine ⟨s i, List.mem_range.mpr hs, ?_⟩
      apply List.any_eq_true.mpr
      refine ⟨t i, List.mem_range.mpr ht, ?_⟩
      have he : rcData[n]! = rcData[n] := getElem!_pos rcData n hn
      have hxs : xs.take (n+1) = xs.take n ++ [(s i,t i,rcData[n].2)] := by
        rw [List.take_succ_eq_append_getElem (by simp only [xs, List.length_ofFn]; omega : n < xs.length)]
        simp only [xs, List.getElem_ofFn]
        rw [he]
      have hu : pg3Used t (n+1) = max (max (pg3Used t n) (s i / 2 + 1)) (t i / 2 + 1) := by
        rw [pg3Used_succ t i]
        change max (pg3Used t n) (t i / 2 + 1) = _
        have : s i/2 ≤ t i/2 := Nat.div_le_div_right hst
        rw [max_assoc, max_eq_right (by omega : s i/2+1 ≤ t i/2+1)]
      have hek := edges i
      change rcEdges rcData[n]!.1 (s i) (t i) (xs.take n) = true at hek
      rw [he] at hek
      have hr := rcRows_true (xs.take (n+1)) (pg3Used t (n+1))
        (rcReal_sub (fun v hv => List.mem_of_mem_take hv) real)
      have hi := ih (n+1) (by omega)
      rw [hxs,hu] at hi hr
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
      exact ⟨⟨⟨⟨hst, hd⟩, hek⟩, hr⟩, hi⟩
  exact aux 0 12 rfl

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461

theorem pg3Enc_exists (e : Fin 7 ≃ Fin 7) (f : Fin 7 → Bool) (n : Nat) (h : n < 14) :
    ∃ z, pg3Enc e f z = n := by
  let g : Fin 7 := ⟨n / 2, by omega⟩
  let x := e.symm g
  have he : (e x).val = n/2 := by simp [x,g]
  by_cases hn : n % 2 = 0
  · exact ⟨(x,f x), by simp [pg3Enc, he]; omega⟩
  · exact ⟨(x,!(f x)), by cases hb : f x <;> simp [pg3Enc, hb, he] <;> omega⟩

theorem pg3RCModel (O : Fin 12 → Finset (Fin 7 × Bool))
    (hpos : ∀ i, (O i).Nonempty) (hcap : ∀ i, (O i).card ≤ 2)
    (hop : ∀ i g, (g,false) ∈ O i → (g,true) ∉ O i)
    (hrow : ∀ r : Fin 48, ∃ f : Fin 7 → Option Bool, ∀ i : Fin 12,
      rcData[i.val]!.2.testBit r.val = true ↔ ∀ l ∈ O i, f l.1 ≠ some l.2)
    (hedge : ∀ i j : Fin 12, i < j → rcData[j.val]!.1.testBit i.val = true →
      ∃ l ∈ O i, (l.1,!l.2) ∈ O j) :
    ∃ s t : Fin 12 → Nat,
      (∀ i, s i < min 14 (2*pg3Used t i.val+1) ∧
        t i < min 14 (2*(max (pg3Used t i.val) (s i/2+1))+1) ∧
        s i ≤ t i ∧ (s i = t i ∨ s i/2 ≠ t i/2)) ∧
      rcReal (List.ofFn fun i : Fin 12 => (s i,t i,rcData[i.val]!.2)) ∧
      ∀ j : Fin 12, rcEdges rcData[j.val]!.1 (s j) (t j)
        ((List.ofFn fun i : Fin 12 => (s i,t i,rcData[i.val]!.2)).take j.val) = true := by
  classical
  obtain ⟨e,flip,s,t,hm,hc⟩ := pg3NormalizeSlots O hpos hcap hop
  refine ⟨s,t,hc,?_,?_⟩
  · intro r hr
    have hlt : r < 48 := by
      change (2^48-1 : Nat).testBit r = true at hr
      exact of_decide_eq_true ((Nat.testBit_two_pow_sub_one 48 r) ▸ hr)
    obtain ⟨f,hf⟩ := hrow ⟨r,hlt⟩
    let F (n : Nat) := decide (∃ z, pg3Enc e flip z = n ∧ f z.1 = some z.2)
    have hF (z) : F (pg3Enc e flip z) = false ↔ f z.1 ≠ some z.2 := by
      simp only [F, decide_eq_false_iff_not, (pg3Enc_injective e flip).eq_iff]
      constructor
      · intro h h'
        exact h ⟨z,rfl,h'⟩
      · rintro h ⟨_,rfl,h'⟩
        exact h h'
    refine ⟨F,?_,?_⟩
    · intro g hg
      apply Bool.eq_false_iff.mpr
      intro hg'
      obtain ⟨x,hx,hxf⟩ := of_decide_eq_true hg
      obtain ⟨y,hy,hyf⟩ := of_decide_eq_true hg'
      have hdx := pg3Enc_div e flip x
      have hdy := pg3Enc_div e flip y
      rw [hx] at hdx
      rw [hy] at hdy
      have hxy : x.1 = y.1 := e.injective (Fin.ext (by omega))
      rw [hxy] at hxf
      have h₁ : x = y := Prod.ext hxy (Option.some.inj (hxf.symm.trans hyf))
      rw [h₁, hy] at hx
      omega
    · intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      change rcData[i.val]!.2.testBit r = true ↔ F (s i) = false ∧ F (t i) = false
      rw [hf i]
      constructor
      · intro h
        have witness (n : Nat) (he : n = s i ∨ n = t i) : F n = false := by
          have hlt' : n < 14 := by
            obtain ⟨hs,ht,_⟩ := hc i
            omega
          obtain ⟨z,hz⟩ := pg3Enc_exists e flip n hlt'
          rw [← hz]
          exact (hF z).mpr (h z ((hm i z).mpr (hz.symm ▸ he)))
        exact ⟨witness _ (Or.inl rfl), witness _ (Or.inr rfl)⟩
      · rintro ⟨hs,ht⟩ z hz
        apply (hF z).mp
        rcases (hm i z).mp hz with h | h
        · rwa [h]
        · rwa [h]
  · intro j
    apply List.all_eq_true.mpr
    rintro ⟨x,k⟩ hk
    obtain ⟨hlt,hx⟩ := List.mem_zipIdx' hk
    simp only [List.length_take, List.length_ofFn] at hlt
    let i : Fin 12 := ⟨k,by omega⟩
    have hx' : x = (s i,t i,rcData[i.val]!.2) := by
      simpa only [List.getElem_take, List.getElem_ofFn] using hx
    change (!rcData[j.val]!.1.testBit k || rcHit (rcOpp (s j)) x || rcHit (rcOpp (t j)) x) = true
    by_cases he : rcData[j.val]!.1.testBit k = true
    · obtain ⟨l,hli,hlj⟩ := hedge i j (by change k < j.val; omega) he
      have hi := (hm i l).mp hli
      have hj := (hm j (l.1,!l.2)).mp hlj
      have ho : rcOpp (pg3Enc e flip (l.1,!l.2)) = pg3Enc e flip l := by
        simp [rcOpp, pg3Enc_opp]
      simp only [he, Bool.not_true, Bool.false_or, hx', rcHit, Bool.or_eq_true, beq_iff_eq]
      rcases hj with h | h
      · exact Or.inl (h ▸ ho ▸ hi)
      · exact Or.inr (h ▸ ho ▸ hi)
    · rw [Bool.eq_false_iff.mpr he]
      simp

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461

private abbrev sgInc (q m : Fin 13) := q = m ∨ q = m + 1 ∨ q = m + 3 ∨ q = m + 9
private abbrev sgPt := (Fin.castAdd 13 : Fin 13 → Fin 26)
private abbrev sgLn := (Fin.natAdd 13 : Fin 13 → Fin 26)
private def sgData : List (Nat × Nat) := [(0, 35777249544923), (1, 16836275385376), (2, 70560147653389), (2, 263891376406528), (1, 8416809216), (16, 281466386776064), (36, 792739058), (40, 1953679), (16, 5703717727342), (260, 205347809787920), (128, 10725122781296), (1280, 123205914198913)]
private def sgP : List Nat := [29, 39, 71, 77, 83, 85, 101, 105, 135, 141, 195, 201, 275, 281, 297, 329, 337, 549, 7, 13, 19, 21, 25, 35, 37, 41, 67, 69, 73, 81, 97, 131, 133, 137, 265, 273]
private def sgW : List Nat := [2592, 392, 896, 2816, 644, 2688, 2432, 2306, 776, 800, 772, 770, 580, 2624, 2114, 2562, 2564, 2184, 904, 2848, 708, 2720, 2656, 456, 2440, 2370, 900, 2944, 2818, 2692, 2434, 780, 808, 802, 2626, 2628]
private abbrev sgBit (m : List Nat) (s : Fin 36 × Fin 13) (q : Fin 13) :=
  (m.getD s.1.val 0).testBit (q - s.2).val

private def sgCoords : List Nat := [0, 113622181459235, 57613145712504, 153348205783569, 0, 170132651584291, 57325358880088, 107984761240753, 126556509397333, 112297742797700, 0, 112228994026099, 0]
private def sgCodes : List Nat := [0, 199820732533659105507249873768673418514676795363732242837661881984570737573910552202042339225037832736914305355467280474680514885, 222968111284814400536737000676491297651774985325024802790721414637310604978180606148881190547870235327021967987007830592368102745, 4795311699137034583985518886200628169376725531386550849733416133791597991946455992557455372117075550316386415856533175902096530728, 0, 4703757011158149048918719614975591548937866972445251493740184749419546548653149296046427365950668863349588955237995876529976254787, 224195031194999903481943882866134415292685216805682692110273853424526042628496820313590979090704662906029541720390778723210065343, 4618771680682271393316508256177133348339991994036265090007459093731977885616130008478152512848447861350081228582487368658451342582, 2950881030289233941831983576048826750607398993964416349046737129399137451413153373146925347569145218190585420508513602525542451499, 2971824437472839396129516914871531647379601599659298075899606107855976537590219018246859118221241390085977643447932154614885000042, 0, 3777024494495746739526257527942748049170900265241493308720682240918449240939640063855465087810406976152339699947073039467122913142, 0]
private def sgPoint (i : Fin 12) := (1325 : Nat).testBit i.val
private def sgCoord (d : Fin 13) (i : Fin 12) : Fin 13 :=
  Fin.ofNat 13 (((sgCoords.getD d.val 0) >>> (4*i.val)) % 16)
private def sgRaw (d : Fin 13) (r : Fin 48) : Fin 36 × Fin 13 :=
  let n := ((sgCodes.getD d.val 0) >>> (9*r.val)) % 512
  (Fin.ofNat 36 (n/13), Fin.ofNat 13 n)
private def sgCol (i : Fin 12) (r : Fin 48) := (sgData[i.val]!).2.testBit r.val
private def sgEdge (i j : Fin 12) := (sgData[j.val]!).1.testBit i.val

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem sgFixed0 : ∀ d : Fin 13, ¬ sgInc 0 d → ∀ r : Fin 48,
    sgBit sgP (sgRaw d r) 0 = true ∧ sgBit sgW (sgRaw d r) d = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem sgCol0 : ∀ d : Fin 13, ¬ sgInc 0 d → ∀ i : Fin 12, ∀ r : Fin 48,
    (if sgPoint i then sgBit sgP (sgRaw d r) (sgCoord d i)
     else sgBit sgW (sgRaw d r) (sgCoord d i)) = sgCol i r := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem sgActive0 : ∀ d : Fin 13, ¬ sgInc 0 d → ∀ i : Fin 12,
    if sgPoint i then sgCoord d i ≠ 0 ∧ ¬ sgInc (sgCoord d i) d
    else sgCoord d i ≠ d ∧ ¬ sgInc 0 (sgCoord d i) := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem sgEdge0 : ∀ d : Fin 13, ¬ sgInc 0 d → ∀ i j : Fin 12,
    i < j → sgEdge i j = true →
    (sgPoint i = true ∧ sgPoint j = false ∧ sgInc (sgCoord d i) (sgCoord d j)) ∨
    (sgPoint j = true ∧ sgPoint i = false ∧ sgInc (sgCoord d j) (sgCoord d i)) := by
  decide +kernel

theorem pg3ColumnWitnesses : ∀ i : Fin 12,
    (∃ r : Fin 48, (sgData[i.val]!).2.testBit r.val = true) ∧
    (∃ r : Fin 48, (sgData[i.val]!).2.testBit r.val = false) := by decide +kernel

private def sgDualRC (s : Fin 36 × Fin 13) : Fin 36 × Fin 13 :=
  let n := ([353, 304, 238, 249, 420, 275, 288, 376, 342, 264, 407, 402, 433, 314, 454, 337, 388, 457, 30, 41, 121, 67, 80, 18, 171, 207, 108, 2, 103, 219, 155, 134, 56, 160, 194, 223] : List Nat).getD s.1.val 0
  (Fin.ofNat 36 (n/13), (Fin.ofNat 13 n)-s.2)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem pg3DualOrbit (s : Fin 36 × Fin 13) : ∃ t : Fin 36 × Fin 13, ∀ q : Fin 13,
    sgBit sgP t q = sgBit sgW s (-q) ∧ sgBit sgW t q = sgBit sgP s (-q) := by
  have cert : ∀ s : Fin 36 × Fin 13, ∀ q : Fin 13,
      sgBit sgP (sgDualRC s) q = sgBit sgW s (-q) ∧
      sgBit sgW (sgDualRC s) q = sgBit sgP s (-q) := by decide +kernel
  exact ⟨_, cert s⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem pg3Relabel
    (rowSet : Fin 36 × Fin 13 → Finset (Fin 26))
    (rowPt : ∀ s q, sgPt q ∈ rowSet s ↔ sgBit sgP s q = true)
    (rowLn : ∀ s m, sgLn m ∈ rowSet s ↔ sgBit sgW s m = true)
    (p l : Fin 13) (hni : ¬ sgInc p l) :
    ∃ v : Fin 12 → Fin 26, ∃ row : Fin 48 → Fin 36 × Fin 13,
      (∀ r, sgPt p ∈ rowSet (row r) ∧ sgLn l ∈ rowSet (row r)) ∧
      (∀ i r, v i ∈ rowSet (row r) ↔ (sgData[i.val]!).2.testBit r.val = true) ∧
      (∀ i, (∃ q, v i = sgPt q ∧ q ≠ p ∧ ¬ sgInc q l) ∨
            (∃ m, v i = sgLn m ∧ m ≠ l ∧ ¬ sgInc p m)) ∧
      (∀ i j, i < j → (sgData[j.val]!).1.testBit i.val = true →
        ∃ q m, sgInc q m ∧
          ((v i = sgPt q ∧ v j = sgLn m) ∨ (v j = sgPt q ∧ v i = sgLn m))) := by
  have shift : ∀ a b c : Fin 13, sgInc (a+c) (b+c) ↔ sgInc a b := by decide +kernel
  have sub : ∀ a b c : Fin 13, (a+c)-(b+c) = a-b := by decide +kernel
  have subadd : ∀ a b : Fin 13, (a-b)+b = a := by decide
  let d := l-p
  have hd : d+p = l := subadd l p
  have hn : ¬ sgInc 0 d := by
    intro h
    have hh := (shift 0 d p).2 h
    exact hni (by simpa only [zero_add, hd] using hh)
  let z (i) := sgCoord d i + p
  let v (i : Fin 12) := if sgPoint i then sgPt (z i) else sgLn (z i)
  let row (r : Fin 48) : Fin 36 × Fin 13 := ((sgRaw d r).1, (sgRaw d r).2+p)
  have hb (m : List Nat) (r : Fin 48) (q : Fin 13) :
      sgBit m (row r) (q+p) = sgBit m (sgRaw d r) q := by simp only [sgBit, row, sub]
  refine ⟨v, row, ?_, ?_, ?_, ?_⟩
  · intro r
    obtain ⟨hp, hl⟩ := sgFixed0 d hn r
    refine ⟨(rowPt _ _).2 ?_, (rowLn _ _).2 ?_⟩
    · simpa only [zero_add] using (hb sgP r 0).trans hp
    · simpa only [hd] using (hb sgW r d).trans hl
  · intro i r
    have h := sgCol0 d hn i r
    cases ht : sgPoint i
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
      simp only [v, ht, Bool.false_eq_true, ↓reduceIte, rowLn, z, hb, h, sgCol]
    · simp only [ht, ↓reduceIte] at h
      simp only [v, ht, ↓reduceIte, rowPt, z, hb, h, sgCol]
  · intro i
    have h := sgActive0 d hn i
    cases ht : sgPoint i
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
      right
      refine ⟨z i, by simp [v, ht], ?_, ?_⟩
      · rw [← hd]; exact fun ha => h.1 (add_right_cancel ha)
      · have hi := (shift 0 (sgCoord d i) p).not.mpr h.2
        simpa only [zero_add, z] using hi
    · simp only [ht, ↓reduceIte] at h
      left
      refine ⟨z i, by simp [v, ht], ?_, ?_⟩
      · intro ha
        exact h.1 (add_right_cancel (show sgCoord d i + p = 0+p by simpa only [zero_add] using ha))
      · rw [← hd]; exact (shift _ _ p).not.mpr h.2
  · intro i j hij he
    rcases sgEdge0 d hn i j hij he with ⟨hi,hj,hn⟩ | ⟨hj,hi,hn⟩
    · exact ⟨z i, z j, (shift _ _ p).mpr hn, Or.inl ⟨by simp [v, hi], by simp [v, hj]⟩⟩
    · exact ⟨z j, z i, (shift _ _ p).mpr hn, Or.inr ⟨by simp [v, hj], by simp [v, hi]⟩⟩

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461

set_option maxHeartbeats 400000 in
theorem pg3RowCover {n : ℕ} (E : PEqualNP.AndCount.AndCountCircuit n)
    (I : Finset (Fin n)) (hout : E.outVars = ∅) (hfl : E.eval I = false) :
    let occ (v : Fin n) := Finset.univ.filter (fun s : Fin E.size × Bool =>
      if s.2 then v ∈ E.rightVars s.1 else v ∈ E.leftVars s.1)
    ∃ f : Fin E.size → Option Bool,
      (∀ v ∈ I, ∀ l ∈ occ v, f l.1 ≠ some l.2) ∧
      ∀ w ∉ I, E.eval (insert w I) = true → ∃ l ∈ occ w, f l.1 = some l.2 := by
  classical
  intro occ
  have sideTrue_def : ∀ {k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool),
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := fun _ _ _ _ _ => rfl
  have eval_def : ∀ (E : PEqualNP.AndCount.AndCountCircuit n) (U : Finset (Fin n)),
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := fun _ _ => rfl

  have sideTrue_congr : ∀ {k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
      (val val' : Fin k → Bool), (∀ j : Fin k, j < i → val j = val' j) →
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val' := by
    intro k U B F i val val' h
    rw [sideTrue_def, sideTrue_def, decide_eq_decide]
    constructor
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩
  have fuel_indep : ∀ (E : PEqualNP.AndCount.AndCountCircuit n) (U : Finset (Fin n))
      (d d' : ℕ) (i : Fin E.size), i.val < d → i.val < d' →
      E.gateValFuel U d i = E.gateValFuel U d' i := by
    intro E U d
    induction d with
    | zero =>
      intro d' i h
      exact absurd h (Nat.not_lt_zero _)
    | succ e ih =>
      intro d' i h h'
      cases d' with
      | zero => exact absurd h' (Nat.not_lt_zero _)
      | succ e' =>
        have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateValFuel U e' j := by
          intro j hj
          have hji : j.val < i.val := hj
          exact ih e' j (by omega) (by omega)
        show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) =
             (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e') &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e'))
        rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
            sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateVal_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit n) (U : Finset (Fin n)) (i : Fin E.size),
      E.gateVal U i =
        (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateVal U) &&
         PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateVal U)) := by
    intro E U i
    have hi : i.val < E.size := i.2
    obtain ⟨e, he⟩ : ∃ e, E.size = e + 1 := ⟨E.size - 1, by omega⟩
    have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateVal U j := by
      intro j hj
      have hji : j.val < i.val := hj
      exact fuel_indep E U e E.size j (by omega) j.2
    have h1 : E.gateVal U i = E.gateValFuel U (e + 1) i :=
      fuel_indep E U E.size (e + 1) i i.2 (by omega)
    rw [h1]
    show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
          PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) = _
    rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
        sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  let sideL (E : PEqualNP.AndCount.AndCountCircuit n) (I : Finset (Fin n)) (i : Fin E.size) : Bool :=
    PEqualNP.AndCount.AndCountCircuit.sideTrue I (E.leftVars i) (E.leftGates i) i (E.gateVal I)
  let sideR (E : PEqualNP.AndCount.AndCountCircuit n) (I : Finset (Fin n)) (i : Fin E.size) : Bool :=
    PEqualNP.AndCount.AndCountCircuit.sideTrue I (E.rightVars i) (E.rightGates i) i (E.gateVal I)
  let f : Fin E.size → Option Bool := fun i =>
    if sideL E I i = false then some false
    else if sideR E I i = false then some true
    else none
  refine ⟨f, ?_, ?_⟩
  · intro v hv l hl
    rcases l with ⟨g, b⟩
    have hlb := (Finset.mem_filter.mp hl).2
    cases b
    · have hsL : sideL E I g = true := decide_eq_true (Or.inl ⟨v, hlb, hv⟩)
      simp only [f, hsL, Bool.true_eq_false, ↓reduceIte]
      split_ifs <;> simp
    · have hsR : sideR E I g = true := decide_eq_true (Or.inl ⟨v, hlb, hv⟩)
      simp only [f, hsR, Bool.true_eq_false, ↓reduceIte]
      split_ifs <;> simp
  · intro w hwI hev
    let S : Finset (Fin E.size) :=
      Finset.univ.filter (fun i => E.gateVal I i = false ∧ E.gateVal (insert w I) i = true)
    have hSne : S.Nonempty := by
      rw [eval_def] at hev
      rw [decide_eq_true_eq] at hev
      rcases hev with h1 | h2
      · rcases h1 with ⟨u, huO, huIn⟩
        rw [hout] at huO
        exact (Finset.notMem_empty _ huO).elim
      · rcases h2 with ⟨i, hiO, hit⟩
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hit⟩⟩
        rw [Bool.eq_false_iff]
        intro hti
        have het : E.eval I = true := decide_eq_true (Or.inr ⟨i, hiO, hti⟩)
        rw [hfl] at het; cases het
    let g := S.min' hSne
    have hgS : g ∈ S := S.min'_mem hSne
    have hgF : E.gateVal I g = false := (Finset.mem_filter.mp hgS).2.1
    have hgT : E.gateVal (insert w I) g = true := (Finset.mem_filter.mp hgS).2.2
    have hmin : ∀ j : Fin E.size, j < g → E.gateVal (insert w I) j = true → E.gateVal I j = true := by
      intro j hj hjt
      by_contra hnf
      have hjf : E.gateVal I j = false := Bool.eq_false_iff.mpr hnf
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjf, hjt⟩
      exact (not_le_of_gt hj) (S.min'_le j hjS)
    rw [gateVal_eq E (insert w I) g, Bool.and_eq_true] at hgT
    rw [gateVal_eq E I g] at hgF
    change (sideL E I g && sideR E I g) = false at hgF
    change sideL E (insert w I) g = true ∧ sideR E (insert w I) g = true at hgT
    by_cases hL : sideL E I g = false
    · refine ⟨(g, false), ?_, by simp [f, hL]⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hLT : sideL E (insert w I) g = true := hgT.1
      dsimp only [sideL] at hLT hL; rw [sideTrue_def] at hLT hL
      rw [decide_eq_true_eq] at hLT
      rcases hLT with h1 | h2
      · rcases h1 with ⟨v, hv, hvI⟩
        rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact hv
        · have ht : decide ((∃ u ∈ E.leftVars g, u ∈ I) ∨
              ∃ j ∈ E.leftGates g, j < g ∧ E.gateVal I j = true) = true :=
            decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
          rw [hL] at ht; cases ht
      · rcases h2 with ⟨j, hj, hji, hjt⟩
        have hjiT := hmin j hji hjt
        have ht : decide ((∃ u ∈ E.leftVars g, u ∈ I) ∨
            ∃ j ∈ E.leftGates g, j < g ∧ E.gateVal I j = true) = true :=
          decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
        rw [hL] at ht; cases ht
    · have hLt : sideL E I g = true := by
        cases h' : sideL E I g
        · exact (hL h').elim
        · rfl
      have hR : sideR E I g = false := by simp [hLt] at hgF; exact hgF
      refine ⟨(g, true), ?_, by simp [f, hLt, hR]⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hRT : sideR E (insert w I) g = true := hgT.2
      dsimp only [sideR] at hRT hR; rw [sideTrue_def] at hRT hR
      rw [decide_eq_true_eq] at hRT
      rcases hRT with h1 | h2
      · rcases h1 with ⟨v, hv, hvI⟩
        rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact hv
        · have ht : decide ((∃ u ∈ E.rightVars g, u ∈ I) ∨
              ∃ j ∈ E.rightGates g, j < g ∧ E.gateVal I j = true) = true :=
            decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
          rw [hR] at ht; cases ht
      · rcases h2 with ⟨j, hj, hji, hjt⟩
        have hjiT := hmin j hji hjt
        have ht : decide ((∃ u ∈ E.rightVars g, u ∈ I) ∨
            ∃ j ∈ E.rightGates g, j < g ∧ E.gateVal I j = true) = true :=
          decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
        rw [hR] at ht; cases ht

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461
open PEqualNP.AndCount

private theorem modelRawPair {n : ℕ} (F : AndCountCircuit n)
    (disj : ∀ g, Disjoint (F.leftVars g) (F.rightVars g))
    (x y : Fin n) (hx : x ∉ F.outVars) (hy : y ∉ F.outVars)
    (h : F.eval {x,y} = true) :
    ∃ g, (x ∈ F.leftVars g ∧ y ∈ F.rightVars g) ∨
      (x ∈ F.rightVars g ∧ y ∈ F.leftVars g) := by
  have aux (d : ℕ) (g : Fin F.size) (hg : F.gateValFuel {x,y} d g = true) :
      ∃ k, (x ∈ F.leftVars k ∧ y ∈ F.rightVars k) ∨
        (x ∈ F.rightVars k ∧ y ∈ F.leftVars k) := by
    induction d generalizing g with
    | zero => exact (Bool.false_ne_true hg).elim
    | succ d ih =>
      simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true, AndCountCircuit.sideTrue,
        decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg.1 with ⟨a, ha, rfl | rfl⟩ | ⟨k, _, _, hk⟩
      · rcases hg.2 with ⟨b, hb, rfl | rfl⟩ | ⟨k, _, _, hk⟩
        · exact (Finset.disjoint_left.mp (disj g) ha hb).elim
        · exact ⟨g, Or.inl ⟨ha,hb⟩⟩
        · exact ih k hk
      · rcases hg.2 with ⟨b, hb, rfl | rfl⟩ | ⟨k, _, _, hk⟩
        · exact ⟨g, Or.inr ⟨hb,ha⟩⟩
        · exact (Finset.disjoint_left.mp (disj g) ha hb).elim
        · exact ih k hk
      · exact ih k hk
  simp only [AndCountCircuit.eval, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with ⟨_, ho, rfl | rfl⟩ | ⟨i, _, hi⟩
  · exact (hx ho).elim
  · exact (hy ho).elim
  · exact aux F.size i hi

private theorem modelRow {n : ℕ} (F : AndCountCircuit n) (I : Finset (Fin n))
    (hn : F.eval I = false) :
    let O (w : Fin n) := Finset.univ.filter (fun s : Fin F.size × Bool =>
      if s.2 then w ∈ F.rightVars s.1 else w ∈ F.leftVars s.1)
    ∃ f : Fin F.size → Option Bool,
      (∀ w ∈ I, ∀ l ∈ O w, f l.1 ≠ some l.2) ∧
      ∀ w ∉ I, w ∉ F.outVars → F.eval (insert w I) = true →
        ∃ l ∈ O w, f l.1 = some l.2 := by
  classical
  intro O
  let E : AndCountCircuit n := { F with outVars := ∅ }
  have gv (U : Finset (Fin n)) (d : ℕ) : E.gateValFuel U d = F.gateValFuel U d := by
    induction d with
    | zero => rfl
    | succ d ih => funext i; simp only [AndCountCircuit.gateValFuel, ih, E]
  have same (U : Finset (Fin n)) (hU : ∀ w ∈ U, w ∉ F.outVars) : E.eval U = F.eval U := by
    have hno : ¬ ∃ w ∈ F.outVars, w ∈ U := fun ⟨w, hw, hwU⟩ => hU w hwU hw
    have hgv : E.gateVal U = F.gateVal U := gv U F.size
    simp [AndCountCircuit.eval, hgv, E, hno]
  have hI (w) (hw : w ∈ I) : w ∉ F.outVars := by
    intro ho
    have ht : F.eval I = true := decide_eq_true (Or.inl ⟨w, ho, hw⟩)
    simp [hn] at ht
  obtain ⟨f, hin, hout⟩ := pg3RowCover E I rfl ((same I hI).trans hn)
  refine ⟨f, hin, ?_⟩
  intro w hw ho ht
  refine hout w hw ((same _ ?_).trans ht)
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu
  · exact ho
  · exact hI u hu

set_option maxHeartbeats 600000 in
theorem pg3ModelOfCircuit (F : AndCountCircuit 26) (v : Fin 12 → Fin 26)
    (R : Fin 48 → Finset (Fin 26)) (hsize : F.size = 7)
    (_hsing : ∀ i w, F.gateVal {w} i = false)
    (hdisj : ∀ i, Disjoint (F.leftVars i) (F.rightVars i))
    (hcap : ∀ j : Fin 12,
      (Finset.univ.filter fun i : Fin F.size => v j ∈ F.leftVars i ∨ v j ∈ F.rightVars i).card ≤ 2)
    (hcol : ∀ i r, v i ∈ R r ↔ (rcData[i.val]!).2.testBit r.val = true)
    (hneg : ∀ r, F.eval (R r) = false)
    (hins : ∀ r i, v i ∉ R r → F.eval (insert (v i) (R r)) = true)
    (hy : ∀ i j : Fin 12, i < j → (rcData[j.val]!).1.testBit i.val = true →
      F.eval {v i, v j} = true) :
    ∃ O : Fin 12 → Finset (Fin 7 × Bool),
      (∀ i, (O i).Nonempty) ∧
      (∀ i, (O i).card ≤ 2) ∧
      (∀ i g, (g,false) ∈ O i → (g,true) ∉ O i) ∧
      (∀ r : Fin 48, ∃ f : Fin 7 → Option Bool, ∀ i : Fin 12,
        (rcData[i.val]!).2.testBit r.val = true ↔ ∀ l ∈ O i, f l.1 ≠ some l.2) ∧
      (∀ i j : Fin 12, i < j → (rcData[j.val]!).1.testBit i.val = true →
        ∃ l ∈ O i, (l.1,!l.2) ∈ O j) := by
  classical
  rw [← hsize]
  let O (i : Fin 12) := Finset.univ.filter (fun l : Fin F.size × Bool =>
    if l.2 then v i ∈ F.rightVars l.1 else v i ∈ F.leftVars l.1)
  have hl (i : Fin 12) (g : Fin F.size) : (g,false) ∈ O i ↔ v i ∈ F.leftVars g := by simp [O]
  have hr (i : Fin 12) (g : Fin F.size) : (g,true) ∈ O i ↔ v i ∈ F.rightVars g := by simp [O]
  have witnesses : ∀ i : Fin 12,
      (∃ r : Fin 48, (rcData[i.val]!).2.testBit r.val = true) ∧
      (∃ r : Fin 48, (rcData[i.val]!).2.testBit r.val = false) := by decide +kernel
  have hno (i : Fin 12) : v i ∉ F.outVars := by
    obtain ⟨r, ht⟩ := (witnesses i).1
    intro ho
    have h : F.eval (R r) = true := decide_eq_true (Or.inl ⟨v i, ho, (hcol i r).2 ht⟩)
    simp [hneg] at h
  have hop (i : Fin 12) (g : Fin F.size) : (g,false) ∈ O i → (g,true) ∉ O i := by
    intro h₀ h₁
    exact Finset.disjoint_left.mp (hdisj g) ((hl i g).1 h₀) ((hr i g).1 h₁)
  have rows (r : Fin 48) : ∃ f : Fin F.size → Option Bool, ∀ i : Fin 12,
      (rcData[i.val]!).2.testBit r.val = true ↔ ∀ l ∈ O i, f l.1 ≠ some l.2 := by
    obtain ⟨f, hin, hout⟩ := modelRow F (R r) (hneg r)
    refine ⟨f, fun i => (hcol i r).symm.trans ⟨fun hi => hin (v i) hi, ?_⟩⟩
    intro ha
    by_contra hn
    obtain ⟨l, hl', hf⟩ := hout (v i) hn (hno i) (hins r i hn)
    exact ha l hl' hf
  refine ⟨O, ?_, ?_, hop, rows, ?_⟩
  · intro i
    obtain ⟨r, hfalse⟩ := (witnesses i).2
    obtain ⟨f, hf⟩ := rows r
    by_contra hn
    have h := (hf i).2 (fun l hl' => (hn ⟨l,hl'⟩).elim)
    exact Bool.false_ne_true (hfalse.symm.trans h)
  · intro i
    refine (Finset.card_le_card_of_injOn Prod.fst ?_ ?_).trans (hcap i)
    · rintro ⟨g,b⟩ hg
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      cases b
      · exact Or.inl ((hl i g).1 hg)
      · exact Or.inr ((hr i g).1 hg)
    · rintro ⟨g,b⟩ hg ⟨k,c⟩ hk he
      change g = k at he
      subst k
      cases b <;> cases c
      · rfl
      · exact (hop i g hg hk).elim
      · exact (hop i g hk hg).elim
      · rfl
  · intro i j hij hbit
    obtain ⟨g, hg | hg⟩ := modelRawPair F hdisj (v i) (v j) (hno i) (hno j) (hy i j hij hbit)
    · exact ⟨(g,false), (hl i g).2 hg.1, (hr j g).2 hg.2⟩
    · exact ⟨(g,true), (hr i g).2 hg.1, (hl j g).2 hg.2⟩

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461

open PEqualNP.AndCount in
theorem pg3Cofactor (n : ℕ) (E : AndCountCircuit n) (T : Finset (Fin n)) :
    E.WellFormed → E.eval T = false →
    ∃ F : AndCountCircuit n, F.WellFormed ∧ F.size = E.size ∧
      ∀ U : Finset (Fin n), F.eval U = E.eval (T ∪ U) := by
  classical
  intro hWF hT

  let liftVars (V : Finset (Fin n)) : Finset (Fin n) :=
    if ∃ x ∈ V, x ∈ T then Finset.univ else V
  let F : AndCountCircuit n := { E with
    leftVars := fun i => liftVars (E.leftVars i)
    rightVars := fun i => liftVars (E.rightVars i)
    outVars := liftVars E.outVars }
  refine ⟨F, hWF, rfl, ?_⟩
  intro U
  by_cases hU : U.Nonempty
  · have hit (V : Finset (Fin n)) :
        (∃ x ∈ liftVars V, x ∈ U) ↔ ∃ x ∈ V, x ∈ T ∪ U := by
      by_cases h : ∃ x ∈ V, x ∈ T
      · rcases h with ⟨t, ht, htT⟩
        rw [show liftVars V = Finset.univ from ite_eq_left ⟨t, ht, htT⟩]
        exact ⟨fun _ => ⟨t, ht, Finset.mem_union_left _ htT⟩,
          fun _ => ⟨hU.choose, Finset.mem_univ _, hU.choose_spec⟩⟩
      · rw [show liftVars V = V from ite_eq_right h]
        constructor
        · rintro ⟨x, hx, hxU⟩
          exact ⟨x, hx, Finset.mem_union_right _ hxU⟩
        · rintro ⟨x, hx, hxTU⟩
          exact ⟨x, hx, (Finset.mem_union.mp hxTU).resolve_left fun hxT => h ⟨x, hx, hxT⟩⟩
    have side (V : Finset (Fin n)) (G : Finset (Fin E.size)) (i : Fin E.size)
        (val : Fin E.size → Bool) :
        AndCountCircuit.sideTrue U (liftVars V) G i val =
          AndCountCircuit.sideTrue (T ∪ U) V G i val := by
      unfold AndCountCircuit.sideTrue
      rw [decide_eq_decide]
      exact or_congr (hit V) Iff.rfl
    have fuel (d : ℕ) : F.gateValFuel U d = E.gateValFuel (T ∪ U) d := by
      induction d with
      | zero => rfl
      | succ d ih =>
        funext i
        change (AndCountCircuit.sideTrue U (liftVars (E.leftVars i)) _ i (F.gateValFuel U d) &&
                AndCountCircuit.sideTrue U (liftVars (E.rightVars i)) _ i (F.gateValFuel U d)) =
               (AndCountCircuit.sideTrue (T ∪ U) _ _ i (E.gateValFuel (T ∪ U) d) &&
                AndCountCircuit.sideTrue (T ∪ U) _ _ i (E.gateValFuel (T ∪ U) d))
        rw [ih, side, side]
    have gate : F.gateVal U = E.gateVal (T ∪ U) := fuel E.size
    unfold AndCountCircuit.eval
    rw [gate, decide_eq_decide]
    exact or_congr (hit E.outVars) Iff.rfl
  ·
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    have fuelFalse (d : ℕ) (i : Fin F.size) : F.gateValFuel ∅ d i = false := by
      induction d generalizing i with
      | zero => rfl
      | succ d ih => simp [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue, ih]
    rw [Finset.union_empty, hT]
    simp [AndCountCircuit.eval, AndCountCircuit.gateVal, fuelFalse]

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461

abbrev RCCol := (Nat → Nat) × (Nat → Nat) × Nat
def RCCol.s (v : RCCol) := v.1
def RCCol.t (v : RCCol) := v.2.1
def RCCol.c (v : RCCol) := v.2.2

def RCCol.den (v : RCCol) (i : Nat) (x : Entry) : Prop :=
  v.c = x.2.2 ∧ (∀ n, (v.s n).testBit i = decide (x.1=n)) ∧
    (∀ n, (v.t n).testBit i = decide (x.2.1=n))

def rsOr {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: as => f a ||| rsOr f as

def rsHit (v : RCCol) (n : Nat) := v.s n ||| v.t n
def rsMeet (p q : Nat → Nat) := rsOr (fun n => p n &&& q n) (List.range 14)

def rsEdge (v : RCCol) (e : Nat) (full : Nat) : List RCCol → Nat
  | [] => full
  | w :: ws =>
    if e.testBit 0 then
      rsMeet (rsHit v) (fun n => rsHit w (rcOpp n)) &&& rsEdge v (e/2) full ws
    else rsEdge v (e/2) full ws

def rsRaw (xs : List RCCol) (r n : Nat) :=
  rsOr (fun v => if v.c.testBit r then rsHit v n else 0) xs

def rsForce (xs : List RCCol) (r : Nat) (v : RCCol) : Nat × Nat :=
  if v.c.testBit r then (0,0)
  else
    let dup := rsMeet v.s v.t
    (dup ||| rsMeet v.t (rsRaw xs r), dup ||| rsMeet v.s (rsRaw xs r))

def rsForced (xs : List RCCol) (r n : Nat) :=
  rsOr (fun v =>
    let f := rsForce xs r v
    (f.1 &&& v.s n) ||| (f.2 &&& v.t n)) xs

def rsConflict (xs : List RCCol) (r g : Nat) :=
  let l := 2*g
  let h := 2*g+1
  let fl := rsForced xs r l
  let fh := rsForced xs r h
  (fl &&& rsRaw xs r l) ||| (fh &&& rsRaw xs r h) ||| (fl &&& fh)

def rsBad (xs : List RCCol) :=
  rsOr (fun r => rsOr (rsConflict xs r) (List.range 7)) (List.range 48)

def rcPackOK (xs : List RCCol) (edge full : Nat) : Nat :=
  match xs.getLast? with
  | none => full
  | some v => rsEdge v edge full xs.dropLast &&& (full ^^^ rsBad xs)

abbrev RSClause := Nat × Nat × Nat × Nat × Nat

def rsAccess (xs : List RCCol) (j : Nat) (f : RCCol → Nat) : Nat :=
  match xs[j]? with
  | none => 0
  | some v => f v

def rsEnd (v : RCCol) (a : Nat) := if a % 2 = 0 then v.s else v.t
def rsMate (v : RCCol) (a : Nat) := if a % 2 = 0 then v.t else v.s

def rsWithHit (xs : List RCCol) (p : Nat → Nat) (j r : Nat) :=
  rsAccess xs j fun w => if w.c.testBit r then rsMeet p (rsHit w) else 0

def rsForceBy (xs : List RCCol) (v : RCCol) (a j r : Nat) :=
  if v.c.testBit r then 0 else
    if j = 12 then rsMeet v.s v.t else rsWithHit xs (rsMate v a) j r

def rsClause (xs : List RCCol) : RSClause → Nat
  | (a,b,j,k,r) =>
    if r < 48 then
      rsAccess xs (a / 2) fun v =>
        let f := rsForceBy xs v a j r
        if b = 24 then f &&& rsWithHit xs (rsEnd v a) k r
        else rsAccess xs (b/2) fun w =>
          f &&& rsForceBy xs w b k r &&&
            rsMeet (rsEnd v a) (fun n => rsEnd w b (rcOpp n))
    else 0

def rcPackClauses (cs : List RSClause) (xs : List RCCol) (edge full : Nat) : Nat :=
  match xs.getLast? with
  | none => full
  | some v => rsEdge v edge full xs.dropLast &&& (full ^^^ rsOr (rsClause xs) cs)

theorem rsOr_bit {α : Type} (f : α → Nat) (xs : List α) (i : Nat) :
    (rsOr f xs).testBit i = true ↔ ∃ a ∈ xs, (f a).testBit i = true := by
  induction xs with
  | nil => simp [rsOr]
  | cons a xs ih => simp [rsOr,ih]

theorem rsMeet_bit (p q : Nat → Nat) (i : Nat) :
    (rsMeet p q).testBit i = true ↔
      ∃ n < 14, (p n).testBit i = true ∧ (q n).testBit i = true := by
  simp [rsMeet,rsOr_bit]

theorem rsHit_bit {v : RCCol} {x : Entry} {i : Nat} (h : RCCol.den v i x) (n : Nat) :
    (rsHit v n).testBit i = true ↔ rcHit n x = true := by
  simp only [rsHit,rcHit,Nat.testBit_or,Bool.or_eq_true,h.2.1,h.2.2,
    decide_eq_true_eq,beq_iff_eq]
  grind

theorem rsAligned {xs : List RCCol} {ys : List Entry} {i : Nat}
    (h : List.Forall₂ (fun v y => RCCol.den v i y) xs ys) :
    ∀ v ∈ xs, ∃ y ∈ ys, RCCol.den v i y := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · exact ⟨_, List.mem_cons_self, hx⟩
    obtain ⟨w,hw,hvw⟩ := ih _ hv
    exact ⟨w,List.mem_cons_of_mem _ hw,hvw⟩

theorem rsRaw_sound {xs : List RCCol} {ys : List Entry} {i : Nat}
    (h : List.Forall₂ (fun v y => RCCol.den v i y) xs ys) {r n : Nat}
    (hb : (rsRaw xs r n).testBit i = true) : (rcHits ys n).testBit r = true := by
  obtain ⟨v,hv,hb⟩ := (rsOr_bit ..).mp hb
  obtain ⟨x,hx,hh⟩ := rsAligned h _ hv
  by_cases hc : v.c.testBit r = true
  · rw [ite_eq_left hc] at hb
    exact (rcHits_iff ..).mpr ⟨x,hx,(rsHit_bit hh _).mp hb, hh.1 ▸ hc⟩
  · simp [hc] at hb

theorem rsForce_sound {xs : List RCCol} {ys : List Entry} {i r : Nat}
    (h : List.Forall₂ (fun v y => RCCol.den v i y) xs ys) {v : RCCol} {x : Entry}
    (hv : RCCol.den v i x) (hr : rcFull.testBit r = true) :
    (((rsForce xs r v).1.testBit i = true) → (rcBad x ys x.1).testBit r = true) ∧
    (((rsForce xs r v).2.testBit i = true) → (rcBad x ys x.2.1).testBit r = true) := by
  by_cases hc : v.c.testBit r = true
  · simp [rsForce,hc]
  have hxc : x.2.2.testBit r = false := by simpa [← hv.1] using Bool.eq_false_iff.mpr hc
  have dup (hd : (rsMeet v.s v.t).testBit i = true) : x.1 = x.2.1 := by
    obtain ⟨n,_,hs,ht⟩ := (rsMeet_bit ..).mp hd
    simp [hv.2.1,hv.2.2] at hs ht
    exact hs.trans ht.symm
  have pick (p : Nat → Nat) (a : Nat) (hp : ∀ n, (p n).testBit i = decide (a=n))
      (hd : (rsMeet p (rsRaw xs r)).testBit i = true) : (rcHits ys a).testBit r = true := by
    obtain ⟨n,_,he,hb⟩ := (rsMeet_bit ..).mp hd
    have ha : a = n := by simpa [hp] using he
    exact ha ▸ rsRaw_sound h hb
  simp only [rsForce,ite_eq_right hc,Nat.testBit_or,Bool.or_eq_true]
  constructor
  · rintro (hd|hp)
    · simp [rcBad,dup hd,hr,hxc]
    · by_cases hd : x.1 = x.2.1
      · simp [rcBad,hd,hr,hxc]
      · simp [rcBad,Ne.symm hd,hr,hxc,pick _ _ hv.2.2 hp]
  · rintro (hd|hp)
    · simp [rcBad,dup hd,hr,hxc]
    · by_cases hd : x.1 = x.2.1
      · simp [rcBad,hd,hr,hxc]
      · simp [rcBad,hd,hr,hxc,pick _ _ hv.2.1 hp]

theorem rsForced_sound {xs : List RCCol} {ys : List Entry} {i r k : Nat}
    (h : List.Forall₂ (fun v y => RCCol.den v i y) xs ys)
    (hslot : ∀ z ∈ ys, z.1 < 2*k ∧ z.2.1 < 2*k) (hr : rcFull.testBit r = true)
    {n : Nat} (hb : (rsForced xs r n).testBit i = true) :
    n < 2*k ∧ (rcF ys n).testBit r = true := by
  obtain ⟨v,hv,hb⟩ := (rsOr_bit ..).mp hb
  obtain ⟨x,hx,hh⟩ := rsAligned h _ hv
  obtain ⟨hs,ht⟩ := rsForce_sound h hh hr
  simp only [Nat.testBit_or,Bool.or_eq_true,Nat.testBit_and,Bool.and_eq_true,
    hh.2.1,hh.2.2,decide_eq_true_eq] at hb
  rcases hb with ⟨hf,he⟩|⟨hf,he⟩
  · exact he ▸ ⟨(hslot _ hx).1, (rcF_iff ..).mpr ⟨x,hx,hs hf⟩⟩
  · exact he ▸ ⟨(hslot _ hx).2, (rcF_iff ..).mpr ⟨x,hx,ht hf⟩⟩

theorem rsBad_sound {xs : List RCCol} {ys : List Entry} {i k : Nat}
    (h : List.Forall₂ (fun v y => RCCol.den v i y) xs ys)
    (hslot : ∀ z ∈ ys, z.1 < 2*k ∧ z.2.1 < 2*k)
    (hr : rcRows ys k = true) : (rsBad xs).testBit i = false := by
  apply Bool.eq_false_iff.mpr
  intro hb
  obtain ⟨r,hri,hb⟩ := (rsOr_bit ..).mp hb
  have h48 : r < 48 := List.mem_range.mp hri
  have hfull : rcFull.testBit r = true := by
    exact (show ∀ j : Fin 48, rcFull.testBit j.val = true by decide) ⟨r,h48⟩
  obtain ⟨g,_,hb⟩ := (rsOr_bit ..).mp hb
  have no (a b : Nat) (hab : a &&& b = 0) (ha : a.testBit r = true)
      (hb : b.testBit r = true) : False := by
    have he := congrArg (fun n : Nat => n.testBit r) hab
    simp [ha,hb] at he
  have forced := @rsForced_sound xs ys i r k h hslot hfull
  have raw := @rsRaw_sound xs ys i h r
  have rows (hg : g < k) :
      ((rcF ys (2*g) &&& rcHits ys (2*g) = 0) ∧
       (rcF ys (2*g+1) &&& rcHits ys (2*g+1) = 0)) ∧
       (rcF ys (2*g) &&& rcF ys (2*g+1) = 0) := by
    simpa using List.all_eq_true.mp hr g (List.mem_range.mpr hg)
  simp only [rsConflict,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_and,Bool.and_eq_true] at hb
  rcases hb with ((⟨hf,hh⟩|⟨hf,hh⟩)|⟨hf,hf'⟩)
  · obtain ⟨hl,hf⟩ := forced hf
    exact no _ _ (rows (by omega)).1.1 hf (raw hh)
  · obtain ⟨hl,hf⟩ := forced hf
    exact no _ _ (rows (by omega)).1.2 hf (raw hh)
  · obtain ⟨hl,hf⟩ := forced hf
    exact no _ _ (rows (by omega)).2 hf (forced hf').2

theorem rsEdge_sound {xs : List RCCol} {ys : List Entry} {v : RCCol} {y : Entry}
    {i full e : Nat} (hfull : full.testBit i = true)
    (h : List.Forall₂ (fun v y => RCCol.den v i y) xs ys) (hv : RCCol.den v i y)
    (hs : y.1 < 14) (ht : y.2.1 < 14) (he : rcEdges e y.1 y.2.1 ys = true) :
    (rsEdge v e full xs).testBit i = true := by
  induction h generalizing e with
  | nil => exact hfull
  | @cons w x ws zs hw _ ih =>
    have hjoin : (e.testBit 0 = true → rcHit (rcOpp y.1) x = true ∨ rcHit (rcOpp y.2.1) x = true) ∧
        rcEdges (e/2) y.1 y.2.1 zs = true := by
      unfold rcEdges at he ⊢
      rw [List.zipIdx_cons',List.all_cons,Bool.and_eq_true] at he
      refine ⟨?_,?_⟩
      · intro h0
        simpa [h0] using he.1
      · apply List.all_eq_true.mpr
        rintro ⟨z,n⟩ hz
        have hm := List.mem_map_of_mem (f := Prod.map (id : Entry → Entry) (fun k : Nat => k + 1)) hz
        simpa only [Prod.map_apply,id_eq,Nat.testBit_div_two] using List.all_eq_true.mp he.2 _ hm
    unfold rsEdge
    split
    next h0 =>
      simp only [Nat.testBit_and,Bool.and_eq_true]
      refine ⟨(rsMeet_bit ..).mpr ?_,ih hjoin.2⟩
      rcases hjoin.1 h0 with h1|h2
      · exact ⟨y.1,hs,(rsHit_bit hv _).mpr (by simp [rcHit]),(rsHit_bit hw _).mpr h1⟩
      · exact ⟨y.2.1,ht,(rsHit_bit hv _).mpr (by simp [rcHit]),(rsHit_bit hw _).mpr h2⟩
    next => exact ih hjoin.2

theorem rcPackOK_sound {xs : List RCCol} {ys : List Entry} {v : RCCol} {y : Entry}
    {e mask i k : Nat} (hfull : mask.testBit i = true)
    (h : List.Forall₂ (fun v y => RCCol.den v i y) xs ys) (hv : RCCol.den v i y)
    (hslot : ∀ z ∈ ys++[y], z.1 < 2*k ∧ z.2.1 < 2*k) (hk : k ≤ 7)
    (he : rcEdges e y.1 y.2.1 ys = true) (hr : rcRows (ys++[y]) k = true) :
    (rcPackOK (xs++[v]) e mask).testBit i = true := by
  have hy := hslot y (by simp)
  have he' := rsEdge_sound hfull h hv (by omega) (by omega) he
  have hr' := rsBad_sound (List.rel_append h (.cons hv .nil)) hslot hr
  simp [rcPackOK,he',hr',hfull]

theorem rsAccess_sound {xs : List RCCol} {j i : Nat} {f : RCCol → Nat}
    (h : (rsAccess xs j f).testBit i = true) : ∃ v ∈ xs, (f v).testBit i = true := by
  unfold rsAccess at h
  split at h
  next => simp at h
  next w hw => exact ⟨w,List.mem_of_getElem? hw,h⟩

theorem rsWithHit_sound {xs : List RCCol} {p : Nat → Nat} {j r i : Nat}
    (h : (rsWithHit xs p j r).testBit i = true) :
    (rsMeet p (rsRaw xs r)).testBit i = true := by
  obtain ⟨w,hw,hh⟩ := rsAccess_sound h
  by_cases hc : w.c.testBit r = true
  · rw [ite_eq_left hc] at hh
    obtain ⟨n,hn,hp,hh⟩ := (rsMeet_bit ..).mp hh
    refine (rsMeet_bit ..).mpr ⟨n,hn,hp, (rsOr_bit ..).mpr ⟨w,hw,?_⟩⟩
    simpa [hc] using hh
  · simp [hc] at hh

theorem rsForceBy_sound {xs : List RCCol} {v : RCCol} {a j r n i : Nat}
    (hv : v ∈ xs) (hf : (rsForceBy xs v a j r).testBit i = true)
    (he : (rsEnd v a n).testBit i = true) : (rsForced xs r n).testBit i = true := by
  refine (rsOr_bit ..).mpr ⟨v,hv,?_⟩
  by_cases hc : v.c.testBit r = true
  · simp [rsForceBy,hc] at hf
  by_cases hj : j = 12
  · simp [rsForceBy,hc,hj] at hf
    by_cases ha : a % 2 = 0
    · have hs : (v.s n).testBit i = true := by simpa [rsEnd,ha] using he
      simp [rsForce,hc,hf,hs]
    · have ht : (v.t n).testBit i = true := by simpa [rsEnd,ha] using he
      simp [rsForce,hc,hf,ht]
  · have hhit := rsWithHit_sound (show (rsWithHit xs (rsMate v a) j r).testBit i = true by
          simpa [rsForceBy,hc,hj] using hf)
    by_cases ha : a % 2 = 0
    · simp [rsMate,ha] at hhit
      have hs : (v.s n).testBit i = true := by simpa [rsEnd,ha] using he
      simp [rsForce,hc,hhit,hs]
    · simp [rsMate,ha] at hhit
      have ht : (v.t n).testBit i = true := by simpa [rsEnd,ha] using he
      simp [rsForce,hc,hhit,ht]

theorem rsHitConflict {xs : List RCCol} {r n i : Nat} (hr : r < 48) (hn : n < 14)
    (hf : (rsForced xs r n).testBit i = true) (hh : (rsRaw xs r n).testBit i = true) :
    (rsBad xs).testBit i = true := by
  let g := n / 2
  have he : n = 2*g ∨ n = 2*g+1 := by dsimp [g]; omega
  refine (rsOr_bit ..).mpr ⟨r,List.mem_range.mpr hr,(rsOr_bit ..).mpr
    ⟨g,List.mem_range.mpr (by dsimp [g]; omega),?_⟩⟩
  simp only [rsConflict,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_and,Bool.and_eq_true]
  rcases he with he|he
  · exact Or.inl (Or.inl (he ▸ And.intro hf hh))
  · exact Or.inl (Or.inr (he ▸ And.intro hf hh))

theorem rsOppConflict {xs : List RCCol} {r n i : Nat} (hr : r < 48) (hn : n < 14)
    (hf : (rsForced xs r n).testBit i = true)
    (hh : (rsForced xs r (rcOpp n)).testBit i = true) : (rsBad xs).testBit i = true := by
  let g := n / 2
  have he : (n = 2*g ∧ rcOpp n = 2*g+1) ∨ (n = 2*g+1 ∧ rcOpp n = 2*g) := by
    exact (show ∀ s : Fin 14, (s.val = 2*(s.val/2) ∧ rcOpp s = 2*(s.val/2)+1) ∨
        (s.val = 2*(s.val/2)+1 ∧ rcOpp s = 2*(s.val/2)) by decide) ⟨n,hn⟩
  refine (rsOr_bit ..).mpr ⟨r,List.mem_range.mpr hr,(rsOr_bit ..).mpr
    ⟨g,List.mem_range.mpr (by dsimp [g]; omega),?_⟩⟩
  simp only [rsConflict,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_and,Bool.and_eq_true]
  apply Or.inr
  rcases he with ⟨hl,hr⟩|⟨hl,hr⟩
  · exact ⟨hl ▸ hf,hr ▸ hh⟩
  · exact ⟨hr ▸ hh,hl ▸ hf⟩

theorem rsClause_sound {xs : List RCCol} {c : RSClause} {i : Nat}
    (h : (rsClause xs c).testBit i = true) : (rsBad xs).testBit i = true := by
  obtain ⟨a,b,j,k,r⟩ := c
  by_cases hr : r < 48
  · simp only [rsClause,ite_eq_left hr] at h
    obtain ⟨v,hv,hc⟩ := rsAccess_sound h
    by_cases hb : b = 24
    · simp only [ite_eq_left hb,Nat.testBit_and,Bool.and_eq_true] at hc
      obtain ⟨n,hn,he,hh⟩ := (rsMeet_bit ..).mp (rsWithHit_sound hc.2)
      exact rsHitConflict hr hn (rsForceBy_sound hv hc.1 he) hh
    · simp only [ite_eq_right hb] at hc
      obtain ⟨w,hw,hc⟩ := rsAccess_sound hc
      simp only [Nat.testBit_and,Bool.and_eq_true] at hc
      obtain ⟨n,hn,h1,h2⟩ := (rsMeet_bit ..).mp hc.2
      exact rsOppConflict hr hn (rsForceBy_sound hv hc.1.1 h1) (rsForceBy_sound hw hc.1.2 h2)
  · simp [rsClause,hr] at h

theorem rcPackClauses_sound (cs : List RSClause)
    {xs : List RCCol} {ys : List Entry} {v : RCCol} {y : Entry}
    {e mask i k : Nat} (hfull : mask.testBit i = true)
    (h : List.Forall₂ (fun v y => RCCol.den v i y) xs ys) (hv : RCCol.den v i y)
    (hslot : ∀ z ∈ ys++[y], z.1 < 2*k ∧ z.2.1 < 2*k) (hk : k ≤ 7)
    (he : rcEdges e y.1 y.2.1 ys = true) (hr : rcRows (ys++[y]) k = true) :
    (rcPackClauses cs (xs++[v]) e mask).testBit i = true := by
  have hy := hslot y (by simp)
  have he' := rsEdge_sound hfull h hv (by omega) (by omega) he
  have hr' := rsBad_sound (List.rel_append h (.cons hv .nil)) hslot hr
  have hcs : (rsOr (rsClause (xs++[v])) cs).testBit i = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    obtain ⟨c,_,hc⟩ := (rsOr_bit ..).mp hc
    have := rsClause_sound hc
    simp [hr'] at this
  simp [rcPackClauses,he',hcs,hfull]

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461

abbrev RState := Nat × List RCCol × (Nat → Nat)
def RState.width (a : RState) := a.1
def RState.cols (a : RState) := a.2.1
def RState.used (a : RState) := a.2.2

def RIn (A : RState) (ys : List Entry) (u : Nat) : Prop :=
  ∃ i < A.width, List.Forall₂ (fun v y => v.den i y) A.cols ys ∧
    (A.used u).testBit i = true

def RBounds (ys : List Entry) (u : Nat) : Prop :=
  (∀ z ∈ ys, z.1 < 2*u ∧ z.2.1 < 2*u) ∧ u ≤ 7

def RStep (A B : RState) (e c : Nat) : Prop :=
  ∀ ys u s t, RIn A ys u → RBounds ys u →
    s < min 14 (2*u+1) → t < min 14 (2*max u (s/2+1)+1) →
    s ≤ t → (s=t ∨ s/2 ≠ t/2) →
    rcEdges e s t ys = true → rcRows (ys ++ [(s,t,c)]) (max u (t/2+1)) = true →
    RIn B (ys ++ [(s,t,c)]) (max u (t/2+1))

theorem rBounds_push {ys : List Entry} {u s t c : Nat} (hb : RBounds ys u)
    (ht : t < 14) (hst : s ≤ t) : RBounds (ys ++ [(s,t,c)]) (max u (t/2+1)) := by
  obtain ⟨hys, hu⟩ := hb
  constructor
  · intro z hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨hl, hr⟩ := hys z h
      constructor <;> omega
    · obtain rfl := List.mem_singleton.mp h
      change s < 2 * max u (t/2+1) ∧ t < 2 * max u (t/2+1)
      constructor <;> omega
  · omega

def RDead (A : RState) (ds : List (Nat × Nat)) : Prop :=
  ∀ ys u, RIn A ys u → RBounds ys u → rcSearch ys u ds = false

theorem RStep.dead {A B : RState} {e c : Nat} {ds : List (Nat × Nat)}
    (step : RStep A B e c) (dead : RDead B ds) : RDead A ((e,c)::ds) := by
  intro ys u hin hb
  apply Bool.eq_false_iff.mpr
  intro hsearch
  rw [rcSearch] at hsearch
  obtain ⟨s, hs, hsearch⟩ := List.any_eq_true.mp hsearch
  obtain ⟨t, ht, hsearch⟩ := List.any_eq_true.mp hsearch
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    decide_eq_true_eq] at hsearch
  obtain ⟨⟨⟨⟨hst, hd⟩, he⟩, hr⟩, hrec⟩ := hsearch
  have hk : max (max u (s/2+1)) (t/2+1) = max u (t/2+1) := by
    have : s/2 ≤ t/2 := Nat.div_le_div_right hst
    rw [max_assoc, max_eq_right (by omega : s/2+1 ≤ t/2+1)]
  rw [hk] at hr hrec
  have hnext := step ys u s t hin hb (List.mem_range.mp hs) (List.mem_range.mp ht) hst hd he hr
  have hbound := rBounds_push (c := c) hb (lt_of_lt_of_le (List.mem_range.mp ht) (min_le_left ..)) hst
  rw [dead _ _ hnext hbound] at hrec
  contradiction

theorem rEmptyDead (A : RState) (h : A.width = 0) (ds : List (Nat × Nat)) : RDead A ds := by
  intro ys u hin _
  obtain ⟨i, hi, _⟩ := hin
  omega

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461

private def reLow (w : Nat) : Nat := (1 <<< w) - 1

private theorem reLow_bit (w i : Nat) : (reLow w).testBit i = decide (i<w) := by
  simp [reLow, Nat.shiftLeft_eq]

private theorem reBefore {k l w i : Nat} (h : k < l) (hi : i < w) :
    k*w+i < l*w := by
  have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at this
  omega

private def reTilePow (w x : Nat) : Nat → Nat
  | 0 => x &&& reLow w
  | d+1 =>
    let a := reTilePow w x d
    a ||| (a <<< ((2^d)*w))

private theorem reTilePow_bit (w x d k i : Nat) (hi : i<w) :
    (reTilePow w x d).testBit (k*w+i) = (decide (k<2^d) && x.testBit i) := by
  induction d generalizing k with
  | zero =>
    by_cases hk : k=0
    · simp [reTilePow, hk, reLow_bit, hi]
    · have : ¬ k*w+i<w := by
        have := Nat.mul_le_mul_right w (show 1≤k by omega)
        simp only [one_mul] at this
        omega
      simp [reTilePow, reLow_bit, this, hk]
  | succ d ih =>
    rw [reTilePow, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases h : k<2^d
    · have hb := reBefore h hi
      have h' : k < 2^(d+1) := by rw [pow_succ]; omega
      simp [h, h', Nat.not_le.mpr hb]
    · have hk : 2^d ≤ k := by omega
      have hb := Nat.mul_le_mul_right w hk
      have hc : k*w+i - (2^d)*w = (k-2^d)*w+i := by rw [Nat.sub_mul]; omega
      have h' : k-2^d<2^d ↔ k<2^(d+1) := by rw [pow_succ]; omega
      simp [h, show k*w+i ≥ (2^d)*w by omega, hc, ih, h']

private def reTile (w n d x : Nat) := reTilePow w x d &&& reLow (n*w)

private theorem reTile_bit {w n d k i x : Nat} (hi : i < w) (hk : k < n) (hn : n ≤ 2^d) :
    (reTile w n d x).testBit (k*w+i) = x.testBit i := by
  simp [reTile, reTilePow_bit _ _ _ _ _ hi, reLow_bit, reBefore hk hi, lt_of_lt_of_le hk hn]

private def rePut (w n x : Nat) := if x=0 then 0 else (x &&& reLow w) <<< (n*w)

private theorem rePut_bit (w n x k i : Nat) (hi : i<w) :
    (rePut w n x).testBit (k*w+i) = (decide (k=n) && x.testBit i) := by
  by_cases hx : x=0
  · simp [rePut,hx]
  simp only [rePut, ite_eq_right hx, Nat.testBit_shiftLeft, Nat.testBit_and, reLow_bit]
  rcases lt_trichotomy k n with h|rfl|h
  · simp [ne_of_lt h, Nat.not_le.mpr (reBefore h hi)]
  · simp [hi]
  · have hb := Nat.mul_le_mul_right w (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at hb
    simp [ne_of_gt h, show ¬k*w+i-n*w<w by omega]

private def reHot (w k n : Nat) := if n<k then rePut w n (reLow w) else 0

private theorem reHot_bit {w l k i : Nat} (n : Nat) (hi : i < w) (hl : l<k) :
    (reHot w k n).testBit (l*w+i) = decide (l=n) := by
  by_cases h : n<k
  · simp [reHot,h,rePut_bit _ _ _ _ _ hi,reLow_bit,hi]
  · have : l≠n := by omega
    simp [reHot,h,this]

private def reStack (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => reStack w f k ||| rePut w k (f k)

private theorem reStack_bit (w : Nat) (f : Nat → Nat) (n k i : Nat) (hi : i<w) :
    (reStack w f n).testBit (k*w+i) = (decide (k<n) && (f k).testBit i) := by
  induction n with
  | zero => simp [reStack]
  | succ n ih =>
    rw [reStack, Nat.testBit_or, ih, rePut_bit _ _ _ _ _ hi]
    rcases lt_trichotomy k n with h|rfl|h
    · simp [h, Nat.lt_succ_of_lt h, ne_of_lt h]
    · simp
    · simp [Nat.not_lt.mpr h.le, ne_of_gt h, Nat.not_lt.mpr h]

private def reGrid (w : Nat) (f : Nat → Nat → Nat) :=
  reStack (14*w) (fun s => reStack w (f s) 14) 14

private theorem reIndex (w s t i : Nat) : (s*14+t)*w+i = s*(14*w)+(t*w+i) := by
  simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem reGrid_bit {w i s t : Nat} (f : Nat → Nat → Nat) (hi : i<w)
    (hs : s<14) (ht : t<14) :
    (reGrid w f).testBit ((s*14+t)*w+i) = (f s t).testBit i := by
  rw [reGrid, reIndex, reStack_bit _ _ _ _ _ (reBefore ht hi), reStack_bit _ _ _ _ _ hi]
  simp [hs,ht]

private def reLift (w : Nat) (v : RCCol) : RCCol :=
  ⟨fun n => reTile w 196 8 (v.s n), fun n => reTile w 196 8 (v.t n), v.c⟩

private def reFresh (w c : Nat) : RCCol :=
  ⟨reHot (14*w) 14, fun n => reTile (14*w) 14 4 (reHot w 14 n), c⟩

private def reUsed (A : RState) (n s t : Nat) :=
  rsOr (fun u => if max u (max (s/2+1) (t/2+1)) = n then A.used u else 0) (List.range 8)

def rcExpand (A : RState) (c : Nat) : RState :=
  ⟨196*A.width, A.cols.map (reLift A.width) ++ [reFresh A.width c],
    fun n => reGrid A.width (reUsed A n)⟩

private abbrev reLegal (u s t : Nat) : Prop :=
  s < min 14 (2*u+1) ∧ t < min 14 (2*max u (s/2+1)+1) ∧ s ≤ t ∧ (s=t ∨ s/2≠t/2)

def rcCanon (A : RState) : Nat :=
  reGrid A.width fun s t => rsOr (fun u => if reLegal u s t then A.used u else 0) (List.range 8)

theorem rcCanon_lane_iff {A : RState} {s t i : Nat} (hi : i < A.width)
    (hs : s<14) (ht : t<14) :
    (rcCanon A).testBit ((s*14+t)*A.width+i) = true ↔
      ∃ u < 8, (A.used u).testBit i = true ∧
        s < min 14 (2*u+1) ∧ t < min 14 (2*max u (s/2+1)+1) ∧
          s ≤ t ∧ (s=t ∨ s/2≠t/2) := by
  rw [rcCanon, reGrid_bit _ hi hs ht, rsOr_bit]
  simp only [List.mem_range]
  constructor
  · rintro ⟨u,hu,h⟩
    by_cases hL : reLegal u s t
    · exact ⟨u,hu,by simpa only [ite_eq_left hL] using h,hL⟩
    · simp only [ite_eq_right hL, Nat.zero_testBit, Bool.false_eq_true] at h
  · rintro ⟨u,hu,ha,hL⟩
    exact ⟨u,hu,by simpa only [ite_eq_left (show reLegal u s t from hL)] using ha⟩

theorem rcExpand_lane {A : RState} {ys : List Entry} {i u s t c : Nat} (hi : i<A.width)
    (h : List.Forall₂ (fun v y => v.den i y) A.cols ys) (hu : (A.used u).testBit i=true)
    (hu7 : u≤7) (hs : s < min 14 (2*u+1)) (ht : t < min 14 (2*max u (s/2+1)+1))
    (hsort : s≤t) (hd : s=t ∨ s/2≠t/2) :
    ∃ j, j < (rcExpand A c).width ∧ (rcCanon A).testBit j=true ∧
      List.Forall₂ (fun v y => v.den j y) (rcExpand A c).cols (ys++[(s,t,c)]) ∧
      ((rcExpand A c).used (max u (t/2+1))).testBit j=true := by
  have hs14 : s<14 := lt_of_lt_of_le hs (min_le_left ..)
  have ht14 : t<14 := lt_of_lt_of_le ht (min_le_left ..)
  have h196 : s*14+t<196 := by omega
  refine ⟨(s*14+t)*A.width+i, reBefore h196 hi,
    (rcCanon_lane_iff hi hs14 ht14).mpr ⟨u,by omega,hu,hs,ht,hsort,hd⟩, ?_, ?_⟩
  · apply List.rel_append
    · apply List.forall₂_map_left_iff.mpr
      refine h.imp ?_
      intro v y hv
      refine ⟨hv.1, fun n => ?_, fun n => ?_⟩
      · exact (reTile_bit hi h196 (by decide : 196≤2^8)).trans (hv.2.1 n)
      · exact (reTile_bit hi h196 (by decide : 196≤2^8)).trans (hv.2.2 n)
    · refine .cons ⟨rfl,fun n => ?_,fun n => ?_⟩ .nil
      · rw [reIndex]
        exact reHot_bit n (reBefore ht14 hi) hs14
      · rw [reIndex]
        exact (reTile_bit (reBefore ht14 hi) hs14 (by decide : 14≤2^4)).trans (reHot_bit n hi ht14)
  · change (reGrid A.width _).testBit _ = true
    rw [reGrid_bit _ hi hs14 ht14, reUsed, rsOr_bit]
    have hk : s/2+1 ≤ t/2+1 := by omega
    refine ⟨u,List.mem_range.mpr (by omega), ?_⟩
    simp [max_eq_right hk, hu]

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461

abbrev RPlan := List (Nat × Nat × Nat)

def rcPext : RPlan → Nat → Nat
  | [], w => w
  | (s, k, v) :: p, w => rcPext p ((w &&& k) ||| ((w &&& v) >>> s))

def rcParity : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | n+1, s, x => rcParity n (s+s) (x ^^^ (x <<< s))

def rcPlanAux (bits : Nat) : Nat → Nat → Nat → Nat → RPlan
  | 0, _, _, _ => []
  | n+1, s, m, holes =>
    let v₀ := rcParity bits 1 holes
    let v := m &&& v₀
    let k := m ^^^ v
    (s, k, v) :: rcPlanAux bits n (s+s) (k ||| (v >>> s))
      (holes ^^^ (holes &&& v₀))

def rcPlan (m width : Nat) : RPlan :=
  let bits := (width-1).log2+1
  rcPlanAux bits bits 1 m (((((1 <<< width)-1) ^^^ m) <<< 1))

def rcPlanOK : RPlan → Nat → Nat → Bool
  | [], m, mass => decide (m < 1 <<< mass)
  | (s,k,v) :: p, m, mass =>
    (k ||| v == m) && (((v >>> s) <<< s) == v) && ((k &&& (v >>> s)) == 0) &&
      rcPlanOK p (k ||| (v >>> s)) mass

theorem rcLift {p : RPlan} {m mass : Nat} (ok : rcPlanOK p m mass = true)
    {i : Nat} (hi : m.testBit i = true) :
    ∃ j < mass, ∀ w : Nat, (rcPext p w).testBit j = w.testBit i := by
  induction p generalizing m i with
  | nil =>
    change decide (m < 1 <<< mass) = true at ok
    have h := of_decide_eq_true ok
    rw [Nat.one_shiftLeft] at h
    refine ⟨i, ?_, fun _ => rfl⟩
    by_contra! hn
    have h' := Nat.testBit_lt_two_pow (lt_of_lt_of_le h
      (Nat.pow_le_pow_right (by decide : 0 < 2) hn))
    simp [hi] at h'
  | cons a p ih =>
    obtain ⟨s,k,v⟩ := a
    simp only [rcPlanOK, Bool.and_eq_true, beq_iff_eq] at ok
    obtain ⟨⟨⟨hcov,hshift⟩,hdis⟩,htail⟩ := ok
    have hd (b : Nat) := congrArg (fun z : Nat => z.testBit b) hdis
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit] at hd
    rw [← hcov, Nat.testBit_or, Bool.or_eq_true] at hi
    rcases hi with hk | hv
    · obtain ⟨j,hj,he⟩ := ih htail (i := i) (by simp [hk])
      refine ⟨j,hj,fun w => ?_⟩
      have hd' := hd i
      simp [hk] at hd'
      simp [rcPext, he, hk, hd']
    · have hs : s ≤ i := by
        by_contra! hh
        have hz := congrArg (fun z : Nat => z.testBit i) hshift
        simp [Nat.testBit_shiftLeft, Nat.not_le.mpr hh, hv] at hz
      have hadd : s + (i-s) = i := by omega
      obtain ⟨j,hj,he⟩ := ih htail (i := i-s) (by simp [hadd,hv])
      refine ⟨j,hj,fun w => ?_⟩
      have hd' := hd (i-s)
      simp [hadd,hv] at hd'
      simp [rcPext, he, hd', hadd, hv]

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461

abbrev RFour := Nat × Nat × Nat × Nat

def rPlane (w n b x : Nat) := if n.testBit b then x else w ^^^ x

def rNibble (w : Nat) (p : RFour) (n : Nat) :=
  if n < 14 then
    rPlane w n 0 p.1 &&& rPlane w n 1 p.2.1 &&&
    rPlane w n 2 p.2.2.1 &&& rPlane w n 3 p.2.2.2
  else 0

abbrev RWordCol := RFour × RFour × Nat

def rBuildCol (w : Nat) (v : RWordCol) : RCCol :=
  ⟨rNibble w v.1, rNibble w v.2.1, v.2.2⟩

def rDense (width : Nat) (vs : List RWordCol) (u : RFour) : RState :=
  let w := 2^width-1
  ⟨width, vs.map (rBuildCol w), rNibble w u⟩

def rCompare (f : Nat → Nat) (a b : RCCol) :=
  a.c == b.c && (List.range 14).all fun n =>
    f (a.s n) == b.s n && f (a.t n) == b.t n

def rCompareList (f : Nat → Nat) : List RCCol → List RCCol → Bool
  | [], [] => true
  | a :: as, b :: bs => rCompare f a b && rCompareList f as bs
  | _, _ => false

def rCompareState (f : Nat → Nat) (A B : RState) : Bool :=
  rCompareList f A.cols B.cols &&
    (List.range 8).all fun u => f (A.used u) == B.used u

def rTrunc (b : RCCol) : Prop := ∀ n ≥ 14, b.s n = 0 ∧ b.t n = 0

theorem rDense_trunc (width vs u) :
    ∀ b ∈ (rDense width vs u).cols, rTrunc b := by
  intro b hb
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
  intro n hn
  simp [rBuildCol, RCCol.s, RCCol.t, rNibble, Nat.not_lt_of_le hn]

theorem rCarryCols {f : Nat → Nat} {i j : Nat} (transport : ∀ w, (f w).testBit j = w.testBit i)
    {as bs : List RCCol} {ys : List Entry} (hc : rCompareList f as bs = true)
    (hz : ∀ b ∈ bs, rTrunc b) (hys : ∀ y ∈ ys, y.1 < 14 ∧ y.2.1 < 14)
    (h : List.Forall₂ (fun v y => v.den i y) as ys) :
    List.Forall₂ (fun v y => v.den j y) bs ys := by
  induction h generalizing bs with
  | nil => cases bs <;> simp_all [rCompareList]
  | @cons a y as ys ha _ ih =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      simp only [rCompareList, Bool.and_eq_true, rCompare, beq_iff_eq] at hc
      refine .cons ⟨hc.1.1 ▸ ha.1, ?_, ?_⟩ (ih hc.2 (fun b hb => hz b (.tail _ hb))
        (fun y hy => hys y (.tail _ hy)))
      · intro n
        by_cases hn : n < 14
        · have he := List.all_eq_true.mp hc.1.2 n (List.mem_range.mpr hn)
          simp only [Bool.and_eq_true, beq_iff_eq] at he
          rw [← he.1, transport, ha.2.1]
        · rw [(hz b (.head _) n (by omega)).1]
          have := (hys y (.head _)).1
          simp [show y.1 ≠ n by omega]
      · intro n
        by_cases hn : n < 14
        · have he := List.all_eq_true.mp hc.1.2 n (List.mem_range.mpr hn)
          simp only [Bool.and_eq_true, beq_iff_eq] at he
          rw [← he.2, transport, ha.2.2]
        · rw [(hz b (.head _) n (by omega)).2]
          have := (hys y (.head _)).2
          simp [show y.2.1 ≠ n by omega]

theorem rCarry {f : Nat → Nat} {A B : RState} {i j u : Nat} {ys : List Entry}
    (transport : ∀ w, (f w).testBit j = w.testBit i)
    (hc : rCompareState f A B = true) (hz : ∀ b ∈ B.cols, rTrunc b)
    (hj : j < B.width) (hb : RBounds ys u)
    (hy : List.Forall₂ (fun v y => v.den i y) A.cols ys) (hu : (A.used u).testBit i = true) :
    RIn B ys u := by
  simp only [rCompareState, Bool.and_eq_true] at hc
  obtain ⟨hcs,hcu⟩ := hc
  have hu' := beq_iff_eq.mp (List.all_eq_true.mp hcu u (List.mem_range.mpr (by have := hb.2; omega)))
  refine ⟨j, hj, rCarryCols transport hcs hz (fun y hy' => ?_) hy, ?_⟩
  · obtain ⟨hs, ht⟩ := hb.1 y hy'
    have := hb.2
    omega
  · rwa [← hu', transport]

theorem rLastRel {α β : Type} {R : α → β → Prop} {vs : List α} {ys : List β} {y : β}
    (h : List.Forall₂ R vs (ys ++ [y])) :
    ∃ xs x, vs = xs ++ [x] ∧ List.Forall₂ R xs ys ∧ R x y := by
  induction ys generalizing vs with
  | nil =>
    obtain ⟨x, xs, hx, hxs, rfl⟩ := List.forall₂_cons_right_iff.mp h
    cases hxs
    exact ⟨[], x, rfl, .nil, hx⟩
  | cons z zs ih =>
    obtain ⟨w, ws, hw, hws, rfl⟩ := List.forall₂_cons_right_iff.mp h
    obtain ⟨xs, x, rfl, hrs, hx⟩ := ih hws
    exact ⟨w::xs, x, rfl, .cons hw hrs, hx⟩

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461

def rSparse : List Nat → Nat
  | [] => 0
  | n::ns => (1 ||| (rSparse ns <<< 1)) <<< n

def rCandidate (A : RState) (e c : Nat) (cs : List RSClause) :=
  rcPackClauses cs (rcExpand A c).cols e (rcCanon A)

theorem rCandidate_mem {A : RState} {ys : List Entry} {u s t e c : Nat}
    (cs : List RSClause) (hin : RIn A ys u) (bound : RBounds ys u)
    (hs : s < min 14 (2*u+1)) (ht : t < min 14 (2*max u (s/2+1)+1))
    (hst : s ≤ t) (hd : s=t ∨ s/2≠t/2)
    (he : rcEdges e s t ys = true) (hr : rcRows (ys++[(s,t,c)]) (max u (t/2+1)) = true) :
    ∃ i, (rCandidate A e c cs).testBit i = true ∧
      List.Forall₂ (fun v y => v.den i y) (rcExpand A c).cols (ys++[(s,t,c)]) ∧
      ((rcExpand A c).used (max u (t/2+1))).testBit i = true := by
  obtain ⟨i,hi,hy,hu⟩ := hin
  obtain ⟨j, _, ha, hy, hu⟩ := rcExpand_lane (c := c) hi hy hu bound.2 hs ht hst hd
  refine ⟨j, ?_, hy, hu⟩
  obtain ⟨xs,x,hx,hxs,hxy⟩ := rLastRel hy
  unfold rCandidate
  rw [hx]
  have hb := rBounds_push (c:=c) bound (lt_of_lt_of_le ht (min_le_left ..)) hst
  exact rcPackClauses_sound cs ha hxs hxy hb.1 hb.2 he hr

theorem rCheckedStep {A B : RState} {e c m : Nat} {cs : List RSClause} {f : Nat → Nat}
    (mask : rCandidate A e c cs = m)
    (carry : ∀ i, m.testBit i = true → ∃ j < B.width, ∀ w, (f w).testBit j = w.testBit i)
    (words : rCompareState f (rcExpand A c) B = true)
    (trunc : ∀ b ∈ B.cols, rTrunc b) : RStep A B e c := by
  intro ys u s t hin bound hs ht hst hd he hr
  obtain ⟨i,hi,hy,hu⟩ := rCandidate_mem cs hin bound hs ht hst hd he hr
  obtain ⟨j,hj,transport⟩ := carry i (mask ▸ hi)
  apply rCarry transport words trunc hj _ hy hu
  exact rBounds_push bound (lt_of_lt_of_le ht (min_le_left ..)) hst

theorem rZeroStep {A B : RState} {e c : Nat} {cs : List RSClause}
    (mask : rCandidate A e c cs = 0) : RStep A B e c := by
  intro ys u s t hin bound hs ht hst hd he hr
  obtain ⟨i,hi,_⟩ := rCandidate_mem cs hin bound hs ht hst hd he hr
  simp [mask] at hi

end PEqualNP.Outside.L_meta_17461
namespace PEqualNP.Outside.L_meta_17461

private def rpA0 := rDense 1 [] (0,0,0,0)
private def rpA1 := rDense 2 [((0,0,0,0),(0,2,0,0),0x208a0a400adb)] (1,2,0,0)
private def rpA2 := rDense 8 [((0,0,0,0),(0,251,0,0),0x208a0a400adb),((254,192,0,0),(83,93,160,0),0xf500036b420)] (160,255,0,0)
private def rpA3 := rDense 37 [((0,0,0,0),(0,0x1fd7feffff,0,0),0x208a0a400adb),((0x1fffede7ff,0x1506c8c200,0,0),(0x727855,0x78737866,0x1f878c8788,0),0xf500036b420),((0x1ff80ff800,0x1fff00000,0x1e00000000,0),(0x79b0d0b0f,0x181c01f40f,0x1fe7fe07f0,0),0x402c9089430d)] (0x7e3fe83f8,0x7fbfffbff,0x1804000400,0)
private def rpA4 := rDense 86 [((0,0,0,0),(0,0x3ffffef7ffffffffffffff,0,0),0x208a0a400adb),((0x3ffffffffffab9f9ffffff,0x2aad30468ff2b958700000,0,0),(0x1d4606000500,0x398101d4606004680,0x3ffffc67efe2b9f9ffb87f,0),0xf500036b420),((0x3337137b8b836be27be0b7,0x8b8231c04fc947c10c090,0x330000600b0021806b0026,0),(0x36440301c20860b1b013,0x3fc17c64ce00b191ce006c,0x3ffeabff7fffffff7fffff,0),0x402c9089430d),((0x3ffffffff00007fff00000,0x3fffffff800000000,0x3ffffc0000000000000000,0),(0x3c03c7ff200c1ff8200c7,0x3ffc38003ff060073ff07,0x3fffffff3ffffff83fff8,0x3c0000000c0000000c0000),0xf001ffc00000)] (0x3c00141bbc00486ebc0093,0x141bb000486eb00093,0x3fffebe44fffb7914fff6c,0)
private def rpA5 := rDense 350 [((0,0,0,0),(0,0x3fffffffffffffffffffffffffffffffffffffffffffefffffffffefffffffdffffdffffffffffffffffffff,0,0),0x208a0a400adb),((0x3fffffffa3fffffffe8ffffff27ffe0fffe7ffffffffffff5cffffffffbbfffdbffff9fffffffffc0fffffff,0x2b2b2a81a2a000550e8a80031202fe0c000000acacab457e5cc0ab457f3a0091b1007101f3feaa1c080aafaa,0,0),(0x5c002800017001400d8001f05018000000000003a300000001c4000240001e0000000003f0000000,0xc5c023000117001802da001f16018000000003803a306003801c4186646071e1c0c0000e3f0e00000,0x3ffffff3a3fdc7ffee8ffe3fd25ffe0e8fe7ffffffffc7fc5cf9ffc7fe3be799b9f8e1e3f3ffff1c0f1fffff,0),0xf500036b420),((0x32b2b389b73f02e70adcd8141cbf3add0505cfcacacd3670697dcd36581374f33f9682b742d33295adbfffff,0x909080848860010052200030330c52100184024242e711f968c2e712fec3060de167d14b12c888a50a0c200,0x32b2b001833802e00a0cd014000b0a0c05058dcacac006600871c00650134400218080a342c330140d1f3df3,0),(0x320200d800640801c00905c20000000e200000c803840080c801c00200138180000007001000000c20c,0x3ffffcb383f007f96e0fe03f8243de0e0fe71dfffff1c7c01cf1f1c7e03bc79801e8c1e3f38fff1c0f1f3df3,0x3fffff5ffffffffebfffffff7fbfeffffffffffffffe7ffffffffe7fffffff6ffff7fffffffffcffffffffff,0),0x402c9089430d),((0x3c3c3ffe0fe0007ff03f8003e3c3f03c07f80ff0f0ffff8003c0ffff800603fcf1ff8001fc07ffe0780fffff,0x303000ff00000001fc000007c000fc00020000c0c003ffffc00003ffff8007f0007ff000ff800ff80003100,0x3c3c3ff00000007fe00000038003f00007c00ef0f0ffc0000000ffc00000038001f80001f003ff00000fcefc,0),(0x3c1283d00480220f0025e7ec424801e9150000f047c010910047802045fec2208026748c3c2491333533,0x3fecfc3ff887d3f09fc5180c73b5f191e60000ffb87fe35f0fb81fc67d003c3f3e3a68f03fc769d3c63c,0x3ffeffdfff07f3ff1ff9fff073f9f9f9f70000ffffffff9e0fff9ffc79ffce3fbf3c7cfc3fe7f1e3f73f,0x3fffc001000000780c00600200038c02060608ffff0000000020f0006001820001c040c18303c018060c08c0),0xf001ffc00000),((0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00,0x3fffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000,0,0),(0x3fc0000000007ffffffffc0003fffff8000f00ff0000000000fffffffffc0001fffffe0003fffffff00fff,0x3fc000000000007ffffffffffffc000000000fff000000000000fffffffffffffe0000000003fffffffff0ff,0x7ffffffffffffffffffffff000000000000000fffffffffffffffffffffffc000000000000,0x3fffffffffffff800000000000000000000000ffffffffffffff000000000000000000000000000000000000),0x1f5ae5100)] (0x3ffffffffffff80c00600200038c42060e0800fffffffffffff0006001820001c040c58703c038962c08c0,0x3fc00000000000000000000000000040000800ff000000000000000000000000000000040400002090200000,0x3fffffffffffffffffffffffffffffbffff7fffffffffffffffffffffffffffffffffffbfbffffdf6fdfffff,0)
private def rpA6 := rDense 859 [((0,0,0,0),(0,0x7fffffffffffffffffffffefffffffffffffffffffffffffffffffffbffffffffffefffffffffffffffffffffffbffffffffffffffffffffffffffffffffffffffdffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0,0),0x208a0a400adb),((0x7fffffffffffff47ffffffffff5cfffffffffdffffffffff47fffffffffae7ffc9ffedffffffffffffffff0fffffe67e9fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa3fffefffffffffffffffffffffffffffffffffffffff,0x565607d6565503454000ab457e5cc000007ffdeaab2b2a81454001ad15f2e60448048d8aab2cb52b2b03f00c0060c64601a1f7480037ff8ff007643f805640000a878297c05ef75bf7716fdb7ebf17fffffff59f51a23ffef582feaaa842190221d92004081d00000002aaa,0,0),(0xb80050000003a300000400060000000000b800a000001d18003600120000000000000000f0a0007981600000000000000000000000000000008000000000000000000000000300000000000000005c0003000000000000000000000060000000000000000,0x18b80460003803a30600080006000000000cb808c000e01d1860b683323000000000000003f2c00e79b1e600000000000000000000000000000100700c0000000000000000000300000000000000005c0003000000000000000000000040000000000000000,0x7fffffffffffe747fb8fffc7fc5cf9fff3fff9fffffffff347f71fff1fe2e79f497ccdcffffffffffffffc0d1ff1864e19fffffffffffffffffffffffffffffe7f8ff3fffffffffffffffffffcffffffffffffffffa3fffcffffffffffffffffffffff9ffffffffffffffff,0),0xf500036b420),((0x656555656567136e7e05cd3670697da5c152e08032b283896e7c0a34d9834bd072f799fffbefbdf2b2aab25e14ad0ce855155a650e656943e2e860ffbd6574b82ce6fbdd72eb5aedddafb66db869ff55dca57955e1b5e9705eeb97fffd6b5d9fb5fdb7066cbfd54fc65ffff,0x12120292121010910c002e711f968c00003d3f6a89092808911801b9c4fcb4c40cc306f000000009090142a200ccf32724a0a5080212968c1207040000120000026118028014a5122250499e4f9600aa235a848a104a9e9fa10068000000000400000000208000020400000,0x65655565656003067005c006600871858142c08032b2800106600a00190043100020010ff3cf39f2b2aa800c1401044811155a650c646140e0e820ddbd6570b02c04e3dd72eb5aed9dafb461b061ff559c257955e18161605eeb97fffd6b5d9bb5fc36064c3fd54dc25ffff,0),(0x640401b000c8038400820e0107000000003204036003201c20082417009c00410420000002400009000000000000047003802031821004000041c00021000000000004000020c1c0800004080000004208838000000000000000400018380208000020400000,0x7ffffffffff96707e00ff1c7c01cf1cf03e781fffffffcb307c01fc71e00e71e090cc00fffffffffffffd40c1f31064e19fffffff8ffc7fdfdf7dffffffff9e07f8de3ffffffffffbffffdf3e0f7ffffbf7fffffff8373c0fffffffffffffffbfffe7c1fdf7ffffdfbfffff,0x7ffffffffffebffffffffe7fffffffffffffffffffffff5ffffffff9fffffffdfefb7ffff3cf39ffffffebffffcfffffffffffffbffefffefeefbeddbfffffffff7ffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffff,0),0x402c9089430d),((0x78786678787ffc1fc000ffff8003c0fe007f003ffc3c3ffe1fc001fffe001e0f8f0fe7800d34d73c3c333f3c02ff01c5a2199c71f007831f7f967926c6787fc00ff983fe7c739cfe3bcff9ffc056f99e33787e19fe0e3f801ff3e3fffe739fe379fff80f9b5f19f13b8ffff,0x606018606001fe00000003ffffc00000003ffc00303000fe0000000ffffe001f003f80aa20820030300c3c0000ffe02c3a0630810307c808081041900060000007e0001800c6301c4300601ffa90661cc87818603f001ffe0001c000000002000000000810000100800000,0x78786678787fe0000000ffc0000000f8007c003ffc3c3ff0000001ff0000000e000c00000c30c63c3c333c0002f0000400199c71e007801f1f16592246787f000f8003fe7c739cfe1bcff8fe0052f99e13387e19fc003e001ff3e3fffe739fc379ffc00f1a5f19e1338ffff,0),(0x782507a009f047c01091cf0267810000000c12078012c11e0084179fbff61002cb28c0000000080401000800000001b8c6c604c4fa4848180019e04f0d20c00480000ea0003d73e0f7f806a54920007a8373c086002430300001e8000e7c17cf7f00745894303,0x7fd9f87ff1ffb87fe35ff1fc78fe0000000fecf87fe2fee1ff1af4603801e00fffffc000003ff7e4fef9f9e6000001cf477907a76a296ed8001e3f8ff6bcc00480000ec0003e7c3f7bf806c58920007cfdfc7f06002430300001cc000f87e76eff00665494303,0x7ffdffbffeffffffff9effffffffc000000ffeffbffcfffffffce7ffcffe700ebae68000003ffbf8ffffb1e6000001ff87fe07c7d2492a50001fffffff3cc00480000ee0003f7ffffff806e5c920007effbfffe6002430300001ec000ffff7efff00765c94303,0x7fffffffff80020000000000000020000000003ffffff00100000100000001080000000ff000003fffffc0000300000619fffffe003800f81805969127ffe0000000433ffb7ffff11fffc080000007f91a36dfff8100000019ffdbcfcffffe13fff000081000ff89a36bcfc),0xf001ffc00000),((0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7fffffffe7ffffff9ffe7fffffffe13cffff0ffffffffffffffffffffffffffffff,0x7f80787f807fffffffff0000000000ffff8000333fc02fffffffff0000000007fff0000ccfc0f83fc03c3fffff000001785e1f81fff8001fe01f81fc07801ffff0000000007fe0fffffc7f80007fc7ffffff1fe07fffc000013cffff007c0000000ffff0000020000000000,0,0),(0x3c0000000000000000000000000000000f000ffc0000000000000000000001ffe003800ffffe79ffff8000000000000001f8000701df78000002378181c3fe001800000001ec3fccff0000e03be90000004692181c3f0cf0,0x7fffffffff80000000000000000000000000003c3ffff000000001000000000ffffffffff000ffffffc0000000000000441fe00000000000001861c387ffe000000003f8607fff801e07c080003c7de01fc07fff800000001fc3030cfffff003c0e00008178e9e01fc0f0cf,0x3000000001000000000ffffffff0f000ffc0003fc00003000007ffe01ffe003800efeffffffff8000000000000279f8000001ff80080003f80001fff800000000000013cfc0f00000003ff00000017f02001fff00f0,0x7fffffffffffffffffffffffffffffffffffffffffffcffffffffefffffffff00000000f0fff003fffc03ffffcfffff8001fe001ffc7ff101000000007ff9ffffffffc00007fffffe0007f7fffc007ffe0001ffe7fffffffe00003f00ffffffc000fffffe800dffe0003f00),0x1f5ae5100),((0x7fffffffffffffffffffffffffffffffffffffc03ffffffffffffffffffffffffffffff00000003fffffffffffffffffffe00000000000000000000007ffffffffffffffff800000000000000000000000001ffffffffffffffffffff000000000000000000000000000000,0x7fffff80000000000000000000000000000000003fffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000007ffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x7fffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),(0x7fffff80000000000000000000fffffffffc3fffcffffffffffffffffff80000000f0fff003fffc03ffffffffffe7fffe001ffffffe0001ffe0007ff9fffffffff3fe003ff0000007fffff80060000001ffe7ffffffff9ff0000007fe000000ffffff000c0000003fff,0x7fffffffffffffffffffffffff000000003ffffff00000000000000000000000000ff000003fffffc000000000007f9ffffe00000000001fffffffffe000000000380003ffffffff80000000060000001fff8000000001c003fff07ffffffff000000000c0000003fff,0x7fff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fe0000000000000001ffffff80000000000003ffffc000000000000000007ffffffe0000000000001fffc000f800000000000000000fffffffc000,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff801fffffffffffffffe0000007ffffffffffffc0007ffffffffffffffffff80000001ffffffffffffe0000000fffffffffffffffffff00000000000),0xfffe00000000)] (0x7fff80000000000000000000000000ffffffffc000000ffffffffffffffffffffffffff00fffffc000003fffffffffff99e00001ffffffffffe5969120001ffffffffffffb7c000000003ffffffffa1ffa36c0007fffffffffffd8ffcf800000000ffff7ffff61ffa368ffc,0x7fffffffffffffffffffffffffffff000000003ffffff00000000000000000000000000ff000003fffffc00000000000001ffffe000000000000000007ffe00000000000007fffffffffc000000005e000001fff80000000000003000ffffffffff0000800009e000003000,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0)
private def rpA7 := rDense 692 [((0,0,0,0),(0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0,0),0x208a0a400adb),((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff87ff863dfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xacacbc29a350ad7caa83ee925b6e2b22874ccd35a3363cca6a69e1a455d1c71d61f2a800230000aa37834cc03fd00ff5e0d560f594d64d7ffffffffffd76bf4800608ffe00000000002852000000057ffcfb800ffffff,0,0),(0x7941f9c200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1fd9dffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe02220000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0),0xf500036b420),((0xcacad6bfc395c62703eab4cbeeb5ffb6d7d5545ff55f55500ffccffbfdf249273213fd2c182d74ffaedfffff7efffffffffffffffc00ffc00088000407ffe06840608ffe00000000003dff00000007fffffffff000000,0x2424280020402958a8014a10114a0000000889200220288a600120040001861841e001543bd4b60011000002130000000040000000d6083fff77fffbf8001f68400000000000000000000000000000000000000ffffff,0xcacad6bfc395c62703eab4cbeeb5ffb6d7d5545ff55f55500ffccffbfdf249273213fc00000000ffaedfffec6c7ffffffebffffffc00d7c00000000007dfe00000608ffe00000000003dff000000000003047ff000000,0),(0x179780000003c000000000280000000000000000ffff9f70000002200020020000000006820000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000ffffffffe8687ffffffc3fffffffffd7ffffebfff7ffffff97bffffffffffb7fff7fffffff7ffff97dffffffffffffd,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff77fffbffdfff6840608ffffffddfffdffdfffffffffe8203047ffffffff,0),0x402c9089430d),((0xf0f0e700fdf0ff8cfc3338e3fdf9fffbe7eaaba0aaa0aaaff02bf83ffffdb6d8edec2b983c18fb0a040aeab0304ffff4b4d01effc6bf2c6afdfbffbff87356f7ff9f7abf57ef7fdfffc21ab7ffffff7ffcfbd5fffffff,0xc0c1829060007f00280c6100206000800044415011614401a4009800200c30d00b281e01fe139a0338104400f9000014005600010404115020400400504a9080060854001011044c0684000010448100001000000000,0xf0f0e700f800f800fc3338e3fcf9fff3e7eaaba00aa0aaafc003303bfdf92490c948020020000000000aeab0300ffff0b4001effc2bf282addb9f6a7f02356f5ff9f5abf56ee6f9b3f821ab7fefbb76ffcfad5ff7ddbf,0),(0xfde9ffc9000000000d000038000000005000000030148c3ffffdb6d8ddec14000000f805080000286802020803201ef00800108061623b1818004006000070c8030952ccc0c18201434cd830000386418e6cc,0xf011f005000000000c00003000000000f0000000003c443bfdf0000030003fffffff070f0c00003fffc2020c03f01ef00c003cc041bc3204107040f9ff9f00c8020ee28820838201c24897cffcf806410c48e,0xfdeefff8000000000d00003800000000000000003000883fffffffffcffc03ffffffff000000003fbf82020000001ef00000280061fe3b1c182040ffff9f70c8030ff2cce0c20201c34cdffffcfb86418e6ce,0xffffffff02000002fffffffff2ffffc7ffffffff0fffffffcfc333c0000000000003c000000000f0f3ffffc0003dfdf3fc0fe10ff3ffc33f9e01c4e3e78fbf0000608f37fcf00d331f3c7dfe3cb32000030479be71931),0xf001ffc00000),((0xffffffffffffffffffffffffffffc3ffffffffffffffffffffffffff87ffffffffffffffffffffffffffffffffffeffffbfffdffbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xff00f832ffff0000cb3c3f00ffff8000003332caccccc33cacb3c30f000e38e2ae0f33ffc001c2cccb8cb33fc02fe00a1b2a9d0a2b29b2b0ffc0df92fe4420871fd67001980f8a21a8335efd8840078b02947ffbf7fe9,0,0),(0x300000000f0003ffc70befdc2fa400003000f0000c0c3ffc1f89000003000000000000000000000000035b59004300610400000008001044400080401e007001604000830200040200401000f003800b200800,0xffffffff000000000fc0000380c0fe0303bfffff0ffaffff3fc002b5fae000000003c0000001fcf0f36ffc000039392027fc062ff3c0c33f1e00d8bfff87bb078066ff25f8f005c3fffc3dde38be383c032ff92c771f1,0x3000000000c3ffffc00ff0003fc000003000f000030c1dfc603000000300000000001ff00000003c00031c1c3dbf3e940003f00001000d8dcb8080007e0077006008005e2e5c04000209c383f003b8030561c1,0xfffffffcfffffffff3c00000ff0003fc003ffffcfff0ffffcf3e2008040fffffcffffffffffe00fffffffc3fffce0e0c000c108f3fc0ffffefff272347f7fff81ff88ff9ff7ffa1d1a3fbfffdf63c7c0ffc47fcfa9e3e),0x1f5ae5100),((0xffff0000ffffffff0c3fc00300000c00003ffcf00f00f3c030000030180fffff0e7003ffffffff00000f3fffffc0000fffcfe10fc3fffffc01fe8018000000fe1a80efc1e00ff400c0000007e00007f0d4077ff00003f,0xfffff83f000000000fc00003fffff000003fc0fff000fc003ffc003fe00000fc0f83fc000001fcff038f8000003ff000e3f03e00bc02fc3ffe00ffdffff7e3078c7ce3c1e0000400e03f8007e000003c67e3000ffffc0,0x3f000000000ffffffc00000000000000ffffff00003fffffc0000000fff003fc000001fffffc003fc00030000f03ffc0033ffcffc00000801c07f81c07ef7f7c0000000400e03fc0e00000003f7bfbe00000000,0xffff0000fffffffff000000000000000003fff000000000fc0000000000fff00000003fffffe0000000f003fffc000000000000c0000003c01ff0020000000f810000001e00ff80100000000000007c08000000000000),(0x3c0000000003c00000000000000003fffcfff0ffff0f3c000000003fffcffffc00000000fffc003c000000000ffc0ce10fffcfffc30800602107f3db000ff89ffe18400301083f9edfe87000007fc4fe043803f,0x3fffffffffffffffffffffffffffc3ffff0fffffffcfc003c0000fc0003003c3fffffe00f0f0003ffffffffff3000fc00f33f0c303f1ff8021878b9bf810639f3e1f8ffc010c3c5cde2f8007c0831cf9f7c0031,0xffffffc0000000000000000000000000003c0000000f0000000003c000000000300000000000000003ffc00000000003fc00e100c003003c060007c2780c200000031001e030003e13c061003003f8000018800801fc1,0xfffffffffffffffffffffffffffffffffffffffffff0fffffffffc3fffffffffcffffffffffffffffc0ffffffffffffc03ff1eff3ffcfffff9fff83f87f7dffffffcefc1ffcfffc1fc3fbeffdffc07ffffe77e0ffe03e),0xfffe00000000),((0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000003fffffffffffffff0000000001fffffffffffffffffffff8000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000003ffffffffffffffffffffffffe0000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000000000000,0),(0xffffffc0ffffffffffffffffffffffffffc000000000000ffffffffffff000000003ffffffffffffffffc03ffffffff003fffff03fff003c01ff803fe7ffffffe07f8001e00ffc01ff3ffff8000007ff03fc000ffffff,0xfffffffffffffffffffffffffffffffffffffff000000000000000000003fffffffe00fffff0003ffffffffffc0000003fffffc001ffffc007ffe0f8007ff000000ffffe003fff07ffffffc003ff800ffffff,0xffffffff000000000000000000000000000000000000000000000000000000000003fc00000000ffffffffc000000000000000003ffffffffe00000007ffff00007ffffffff00000003ffff80000000003fffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ffffffff00000fffffffffffffffffffffc000003ffffffffff80000ffff800001ffffffffffc00000000007fffc00000000000),0x2f403cf2)] (0xffffffff000000000000000000000000003c000000000000303ffffffff03ffffffc3c000001ff0f0c9fffc00000000003f0fff0cc0f3cfffe00001e387c4407ef9c60dffff00000f1c3e221f05de03f7ce306f81ef0f,0xffffffffffffffffffffffffffffffffffffffffffffffffcfc00000000fc0000003c3fffffe00f0f36ffffffffffffffc0f000f33f0c33fffffffe3c787bbf810608f21ffffffff1e3c3dde1fa207c08304790fe1030,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0)
private def rpA8 := rDense 328 [((0,0,0,0),(0,0xffffffffffffffffffffffffffefffffffffffffffffffffffbfffffffffffffffffffffffffffffff,0,0),0x208a0a400adb),((0xffffffffffffffffffffffffff3ffffffffffffffffffffffeffffffffffffffffffffffffffffffff,0xaab0e5a4e0af55364d654cd5e102a8ed5415eaf066ae2a6caa075598fffeb0e2c00000049f9207ffff,0,0),(0xc0000000000000000000000100000000000000000000000000000000,0xf80000000000000000000001c0000000000000000000000000000000,0xffffffffffffffffffffffffff07fffffffffffffffffffffe3fffffffffffffffffffffffffffffff,0),0xf500036b420),((0xccd9700ebfffccf03fcffffffc72efeffffff8000667e00ee7c707fcfcff433ffffff9fe879bffffff,0x222085a0400011064020000001b000a0000002f060880a6008c050000300b0c0000000001800000010,0xccd9700ebfffccf03fcffffffc006247fffff8000067e006660003fc3cff433dffff79fe879bffffef,0),(0x517f000000000180000110038080300000000000180000004000030,0xffffffffffffffffffffffffff07f81ffffffffffffffffffe3ffffffffffffffffe7fffffffffffcf,0xfffffffffffffffffffffffffff867e7ffffffffe1ffffe67fc0f3fc3ffffffdfffffffffffbffffff,0),0x402c9089430d),((0xfffe8ff3fffff3afe8302a804bff9c9fffffffdbffffffff99ffffffc003ffff00000007fffe07fff0,0x60040000041005454455a0382060000000200000002022c100003ffc0000c0000000000000000f,0xfffe8ff3fffff3afe8302a804b079c9fffffffdbffffff5f9836ffffc003ffff00000007fffe000000,0),(0x7fffff800000001e001db0000000000013fff80000002000000,0xff9ffffffff8001e00001980240c03c00000033fff8000000607fff0,0xff9ffffffff8001e0001f981ff0c03c0080003000000100006000000,0xffffffffffffffffffffffffff006000000007ffe1fffe067e00f3fc3ff7fffcc0007feffff9f8000f),0xf001ffc00000),((0xffffffffff0fffffffffffffffffffffffe1ffffffff7ffdffffffbbffffffffffffffffffffffffff,0xf0e326cb0e002aca72aab32a1ec5571661c00570795155915538aa231647c34c3fffd370785f80000f,0,0),(0xc03f24c000030000000006000007e4800000086020024004401300504c00202600a81800040,0xfffffffc3bfbbf03ffcfffffff006000067e77ffe19af8061ffff3fc2ef3fbfcc003dde7f7f9d0007a,0xfc4040cffc03000000000600000808012a065000061ff000001300504c00382600a81800070,0xfffffff0080833003fcfffffffff9ffff90107ed5f987ff99e00ff33fecffafb3ffc7d9ff57e7fff8f),0x1f5ae5100),((0xff03c003f03000fc3c003fcf00fe07e78606000001fff9ffe7dbf3ffe008000c20d9c0100000041b30,0xffe3e40c3fc00c027fcf3c3cf001f81867f800707586000401ff0c8abff7d3f31e37c060000403c6ff,0xfc0000cfc03ffc3ff9001f818000001801e787801e7ff3f33c0300402df7f8060080583eff0,0xff03c3f0000033003c003c0003fe07e780000600018007f81800c00020082800208040105000041000),(0x3f00000330003cfc3ffff019818000007801e1ff8079e00ffffc88038b31f7c110071de03ef80,0x3ffffffffffc3cfc3fffffe67e7f800078000787ff87e00f33018b879bce0803170f3d9a41004,0xfffffc00000000003c003c00000000000000007fe1878006000000cc27478240c0004e8f0421d8000b,0xffffffffffffffffffffffffffffffffffffff801ff87ff9ffffff33f8bbffb33ffff177fe5e67fffc),0xfffe00000000),((0xfffffbffffffff03bfffc000fff80007ffffffff81f807e07fc0f0003ffffcf1ff047ffff87bffe08f,0xffffe3ffffffff023ffc0000e3051017fffffff019f807f17e38f80339fbfcf1fc007077f985e7808c,0xffffc3fffffffffc3fffffff03f867e7ffffff8001ffffe67fc0f3fc3e3fff00fffbfc7ffe01ffff7f,0),(0xfffc34f3ffffc30c7cfffc30fcf867e7fffff80060601e0061e4000016d7cf316fa7adaf9e1afdf4ff,0x3ff03fffffc0cc0cfc03ffff867e7f8000793e1ff98007e3ff0c03fc47131b7fc7f88e21b3eff87,0xfffc300c000000ff3f0ffffffc0000000000006c00001800003f030006e782fd073c0dcf05fa58e78b,0xffffc3fffffffff33ff03fc003fffffffffffffe1fffe7ffffc0fffff93bffc2f8c3f277fe65e7187c),0x2f403cf2),((0xfffffffffffffffffffffffffffffff8000007fffe000000000000003fffffffc0007ffffffff80000,0xfffffffffff80000000000000000003fffffffffff80000000000000,0xffffffffffffffffffffffffffffffc0000000000000000000000000,0xffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000),(0xfffffc0fffffffffc000000003fe781fffffffffff8007f87fff0c00203bfffec0024077fffd80004f,0xffffffffffffffffffcff801ff80000001e0007ff80000fffc03c000300038078000678007f,0xfffffff0000000000000000000000018000000001ffff80000000fffffc00003c003ff800007800070,0xffffffffffffffffffffffffffffffe7ffffffffe1fffffffffff0003ffffffc3ffc7ffffff807ff80),0x1dcf8f)] (0xfffffffc000000f33f003fc00000181807fff86cbffff80001ff0f0fffe386c74f3fffc70ce6c9e7f9,0xffffffffffffffffffffffffffffe7e7f80007ff41fffffffe00f3f03ffffbf8b0c07ffff77976180e,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0)
private def rpA9 := rDense 388 [((0,0,0,0),(0,0xffffffffffffbffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0,0),0x208a0a400adb),((0xfffffffffffcfffffffbffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xa5a3cf0547580b54c6d0be06ab4cbc2b216959a1002000000028002800050000ebbffbffff801ffbdfffafff7bfffcbfe,0,0),(0x30000000400000000000010000000000000000000000000000000000000000000000000000000000000000,0x3e00000060000000000001c000000000000000000000000000000000000000000000000000000000000000,0xfffffffffffc1ffffff9ffffffffffffe3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0),0xf500036b420),((0xf0aa02dfdcbfefe00977ebe0180171fff30ffa173ffc3ffffffffffffffffffd85cfff0fffffffffffffffffffffff,0xa5a0c5054202c00000d42800014c3c282c0049000000000000000000000000000027a3000f00000000050000000080000,0xf0aa02dfc01fe7e00177e1e01801703ff30ffa173ffc3fffffebfffffffdfffd85cfff0fffffffffaffffffff7ffff,0),(0x140100010001400000000000000000000000000001c000000060000000000000000000070000000180000,0xfffffffffffc1ffffff9ffffffffffffe3fffffffffffffffffffe3fffffff9ffffffffffffffffffff8fffffffe7ffff,0xffffffffffffe1fe7ffe7ffe1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0),0x402c9089430d),((0xfffaa11fff33ffff85ffe001e7fe76fffcffcfffda3cfc3d27fc013e05ff801cfff68f3f0fc4149ff004f3fffffff7c41,0x14e000048e00042021e06080088000d001000000000000000000000000000000970c0f0000b600ffb0c000000083be,0xfffaa11fff301fff81f9e001e7fe76ffe0ffcfffda3cfc3d27fc013e05ff801cfff68f3f0fc4149ff004f217fe0073c41,0),(0x1fe20000000060000001c0000000000fc000000003de27ffffd0000003f000010000000f001fe0070001,0x3ffffa4078001e6000000000000000000fc00000001fde27ffffd0000003f000010000007f1e9fffff4001,0x3ffff80078001e60000001c0000000000fc00000001fc087f801c0000003f000010000007f401fe0070001,0xfffffffffffc00005bf87ffe19ffffffe3ffffffffff03fffffffe0215800002ffffffc0ffffeffffff80a1600000bffe),0xf001ffc00000),((0xffffffffffffffffffffffffffffffffffffffffffffffffffc3fffffff87fff83ffffcffffffffffffffffffffffffff,0xcacccf09aa6b159963655e074d4d3c3c32b2a90a00002803ff83fffffff07fff82efffcafffff00000000000000000000,0,0),(0x3c30f000000000208fe0200101f80807c0000300018082098080800120200180,0xfffffffffff0000001f87dde01ffffffffff00ffffffc03e7afffe02159f80e2fffffff00fffe9eeeff80a179c038bffe,0x7e04807fc3ff000000003f8d020200102000e0000000000f180e3108080800200380180,0xffffffffffffffffffffffffff81fb7f803c000fffff3fc07201fdffefc07f1f83ffffcff0e7f1c207f7f7fe41fc7ee7f),0x1f5ae5100),((0xfc0f0000c803f9e1a4060000600180041c02f0cc0000b001b40c19f16901866bcf00001c00e616dc0067c5658019afe61,0xfc0fcf012068061842019e078d4dbc383fb000ce000088024bf3f60e97fe7df6b3efffe2ffffe92c0fd8088d81f78bffe,0xc000060180018001e00000001f00ff0000000003fc03fe00b2007fe0000000000019eff00ff808a801ff8019e,0xffff000c1203f9e025fe6000000180000000000c00003000000001f14900000b8300000c00e610000007c54400002ee61),(0x3f0000cd300060181f9e001e000000100010000000000007001fc00a2007f00000000000001e1c007f000a801fc0001e,0x3f0000cff0ff9fe2ffe60000678000503c3f0f000003eb3ffffffff5800001d7c00000fac19ffffffffff4000007519f,0xfc0ffff300f0000050001ffe1987fffae03c000fffff014c000000000580000283ffffc053e600000000001600000ae60,0xffff000cf63fffffafffe015e7f9e0121ffcfffff03afeb3fffffffffffffffffffc0ebfacfffffffffffffffffffffff),0xfffe00000000),((0xfffffffef6ffe1fe7ffe7ffe1ff7dfc8df3c3ffffffffffe4fffc43f9ffff11cfffb7ffffafff93fff10ff9fffc473fff,0xffffc30cf73c15ff2ff9641547c59c09033d3fffc03afe824fff803f9fffe01cfffb1fbfaaffd93ffe10ff9fff8473ffd,0xffff0cccf6ffe1fe7ffe7bbe1f8180121ffcffffc1bbffc3fffffbfffffffefffff06efff0ffffffffeffffffffbfffff,0),(0xf0ff0ee136ffe1fe7e7e1ffe1f8820323cfcffffe1fbffc007fde7ff55fff9fffffcfefff5c6f01ff79ffb57ffe7ffc6f,0xf000eefe4cfe1fe7f867fea1e1fe4e060c0f0f033c13fdc07ffffffe2003f1d7c0cf04ff728f01ffffff3e800fc7528f,0xf00ffff009f0000050001ffe19e01b1f833fc00fedff0163f800fc0005803f0283fb7fc058d76fe003f0001600fc0ad76,0xfffff11cf63fffffafffe015e7e79f9a9ffc3fffcc3efeabffff03ffffffc0fffff30fbfaaff9ffffc0fffffff03ffff9),0x2f403cf2),((0xffffffff3fbffe0059fffff991ffffffe3ffcfffffff03ffffffffc21d800002ffffff00cfffefffffff0e1600000bffe,0xf00380bfffe60079e000600001c008202000000fc00000003ffe27ffffd00007f3fc0001020000ffc01fe0070001,0xf00fc003ffff8007e001e6061fe07c0030000e00fc0c000003fc007f801c0003803f03001000000ff001fe0070001,0xffff00000030000001f8000001f9e000033cccfff0000033f7fffc0005800002fffc00000cffefdffff0001600000bffe),(0xfc00f11f3f73f9fe020660078ffffffffffff3fffe3cfc3f8ffe023e1dff809cffff8fff3ff81e3ff808fe17fe0273f81,0xf000000c3ffffda07823ffe7800000300ccf000033df3fffffc3c180000fe7c0000cf7c1ffffffff0fc000003f91ff,0xfff00ee0003c000001f81dc1e181e000003c000ff1c0020000000000058000e083fc700080e0000000000016000382e00,0xffffffffff3ffffff5ffffe007fffffffffffffffffcff3fffffffffffffff1fffffff3fcffffffffffffffffffc7ffff),0x1dcf8f),((0xfffffffffffffffffffffffffe7ffffffc00f0fffffffffc00000000000000003ffffffffffff00000000000000000000,0xfffffffffff0000000000000007fffffffff00ffffffffffffffffffffffffffc00000000000000000000000000000000,0x7fffffffffff00000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000000),(0xfffffff0003c000001fffffe07e1ffff803c000fffff3ffff80000000600001303ffffcfff000fe00000001800004cfff,0x30000001fffffff981fffffc3f030fffffc03c0000000007ffffe303fffff00ffff0000000001fffff8cfff,0xffffffffffcffffffe000000007e000003c0fcf00000003ffffffffff8000003fc0000000f000fffffffffe000000f000,0xffffffffffffffffffffffffffffffffffffffffffffffc3fffffffffffffffc3ffffffff0000ffffffffffffffff0000),0x5300011ac6e)] (0xfffffffffffffffffff81dd401fffb1a83fcfcfffdfe0267fffffffffd800002bfff7f8099f70ffffffffff600000af70,0xffffffffffffffffffffffffffffffffffffffffffffffbbffffffffffffffffffffffffeefffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0)
private def rpA10 := rDense 95 [((0,0,0,0),(0,0x7ffffffffffff7ffffffffff,0,0),0x208a0a400adb),((0x7fffffffffff9dffffffffff,0x274b20fd1aa680501ffcf860,0,0),(0x620000000000,0x7f0000000000,0x7fffffffffff80ffffffffff,0),0xf500036b420),((0xbf87ff87f9fb8ffffdff87f,0x2403000500205a0000200000,0xbf87ff87f9f80ffffc3f87f,0),(896,0x7fffffffffff80ffffffffff,0x7fffffffffffffffffe3fc7f,0),0x402c9089430d),((0x7fef98dfd7f7ffd850be8fd1,0x202008001d000f407020,0x7fe798c7d7f580c850be8fd1,0),(0x1f00300001c00e040800000,0x1f80318001e7ff0409c0380,0x1e0000000147fc0409c0380,0x7e07fce7ffe1800fbf63fc7f),0xf001ffc00000),((0x7fffff3ffffbffffffffffff,0x2d934706652962afe00107df,0,0),(0xc00785800428403006,0x7e079ce7fff58007af63fc7f,0x7e00007e1800c38403006,0x7ff8073ff80a7ff3c7bfcff9),0x1f5ae5100),((0x818777ff90b7ff850bdcfb9,0x21831087fc240007af40f85f,0x6528000a000fbf6d35a6,0x14180217f8007ff04090ca19),(0x16000528008a8003872d05a0,0x1ffe7ef00781fffffff13626,0x60018007f86000000002c859,0x15fe7ffffe1e7fffffffffff),0xfffe00000000),((0x55fdf8c7f8547fffffe2fc5f,0x17f978c7f89480ff7ee2ffdf,0x15f87ffffe1e7fffffe3fc7f,0),(0x35fa7ad7fe347ffbf7c28851,0x61fffff8066a7fffdfa0540a,0xa000427f98b80018303a875,0x15f9fbdffe147ffe7cffffff),0x2f403cf2),((0x7e079ce7ffe1ff0fbf53fa7f,0x19f00300051d7fe040d00200,0x61e1e00000747fc040bc0780,0x61ce7f800000f9f03f87f),(0x7fe7f8c787f5ffcc78d2f25e,0x1e61ce078007fcfffdd3ba7,0x7800000000006c0d8,0x7ffffffffffffffffffbff7f),0x1dcf8f),((0x7ffff8c7f8747ff0003c079f,0x7e079f07fff9800fe0230440,0x7e00007e1800000020040,0x7ff80007f8007ff0003c0780),(0x7f80003000003f860,0x1ff83000006f8df,0x7ffffffffe007cfffff90720,0x7fffffffffffffffffff07e0),0x5300011ac6e),((0x7fffffffffffff00003f07e0,0x7fffffffffff8000003ff800,0x7fffffffffffffffffc00000,0),(0x7ffffff8007e7cffffff07e0,0x7f8300000700e0,0x7fffffffff807cfffffbff7f,0x7ffffffffffffffffffc0780),0xbac343420010)] (0x7fffffffff807cfffffbef7d,0x7fffffffffffffffffffffff,0x7fffffffffffffffffffffff,0)
private def rpA11 := rDense 18 [((0,0,0,0),(0,0x3ffff,0,0),0x208a0a400adb),((0x3fff7,0x25661,0,0),(8,12,0x3fff3,0),0xf500036b420),((0x3fee3,8,0x3fcc3,0),(272,0x3fff3,0x3fccf,0),0x402c9089430d),((0x7f3f,0x20044,0x3f33,0),(0x8c00,0xcf3c,0xf3c,0x330c3),0xf001ffc00000),((0x3fbff,0x1919a,0,0),(0x30400,0x33cc3,0x30000,0xf3ff),0x1f5ae5100),((0xc33f,0x314c3,0x3c3f0,15),(0xc3f0,0x300cc,0x3003,0x3ffff),0xfffe00000000),((0x33ccf,0x33d13,0x3fccf,0),(0x3ccf,0xc0cc,0x3f0c3,0x33f3f),0x2f403cf2),((0x330cf,0x8c0c,0xf3c,0x330c3),(0x33c0c,0x303ff,0x3300,0x3fcff),0x1dcf8f),((0x10f3f,0xb883,0x3000,831),(0x2300f,0x3ff0c,243,0xffff),0x5300011ac6e),((0xff3f,0x2ee23,0xcccf,0),(0xfff0,0xff0c,0x330f3,0xcfff),0xbac343420010),((0xcff0,0x30ffc,0xfff,0x3f000),(0x330f0,0x30f0,0x3cf0c,0x3ffff),0x9c123223070)] (0x3ffff,0x3ffff,0x3ffff,0)
private def rpA12 := rDense 0 [] (0,0,0,0)
private def rpC0 : List RSClause := []
private def rpM0 := rSparse [0,1]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck0 : rCandidate rpA0 0 35777249544923 rpC0 = rpM0 := by decide +kernel
private def rpP0 := rcPlan rpM0 196
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan0 : rcPlanOK rpP0 rpM0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry0 : rCompareState (rcPext rpP0) (rcExpand rpA0 35777249544923) rpA1 = true := by decide +kernel
private theorem rpStep0 : RStep rpA0 rpA1 0 35777249544923 :=
  rCheckedStep rpCheck0 (fun _ hi => rcLift rpPlan0 hi) rpCarry0 (rDense_trunc _ _ _)
private def rpC1 : List RSClause := [(0,2,12,12,2)]
private def rpM1 := rSparse [7,23,0,0,1,1,53,1]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck1 : rCandidate rpA1 1 16836275385376 rpC1 = rpM1 := by decide +kernel
private def rpP1 := rcPlan rpM1 392
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan1 : rcPlanOK rpP1 rpM1 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry1 : rCompareState (rcPext rpP1) (rcExpand rpA1 16836275385376) rpA2 = true := by decide +kernel
private theorem rpStep1 : RStep rpA1 rpA2 1 16836275385376 :=
  rCheckedStep rpCheck1 (fun _ hi => rcLift rpPlan1 hi) rpCarry1 (rDense_trunc _ _ _)
private def rpC2 : List RSClause := [(4,24,0,0,1),(0,24,2,2,2),(2,24,0,2,0),(2,24,2,0,0)]
private def rpM2 := rSparse [25,1,0,0,3,1,0,0,7,1,5,66,7,3,1,0,2,5,12,1,96,3,1,0,5,1,7,82,0,6,0,9,1,221,1,5,1]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck2 : rCandidate rpA2 2 70560147653389 rpC2 = rpM2 := by decide +kernel
private def rpP2 := rcPlan rpM2 1568
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan2 : rcPlanOK rpP2 rpM2 37 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry2 : rCompareState (rcPext rpP2) (rcExpand rpA2 70560147653389) rpA3 = true := by decide +kernel
private theorem rpStep2 : RStep rpA2 rpA3 2 70560147653389 :=
  rCheckedStep rpCheck2 (fun _ hi => rcLift rpPlan2 hi) rpCarry2 (rDense_trunc _ _ _)
private def rpC3 : List RSClause := [(6,24,2,0,0),(6,24,0,0,0),(6,24,2,2,0),(4,24,3,0,22),(5,7,0,0,1),(4,24,3,3,22),(0,24,2,3,23),(0,24,3,2,23),(0,24,3,3,23),(0,4,3,3,24),(0,6,2,2,2),(1,5,3,3,24),(1,7,2,2,2),(2,24,3,0,22),(2,24,0,3,22),(2,24,2,3,23),(2,24,3,2,23),(4,7,12,0,1),(4,24,0,3,22),(5,6,0,12,1),(6,24,0,2,0),(0,4,3,12,24),(0,4,12,3,24),(0,6,2,12,2),(0,6,12,2,2),(1,4,3,12,24),(1,6,2,12,2)]
private def rpM3 := rSparse [129,14,1,11,20,3,11,19,10,0,0,0,0,9,11,0,1,38,11,24,292,1,1,77,6,6,2,2,2,4,0,2,0,17,2,442,6,9,17,8,27,1,0,0,0,0,1,6,1,38,26,9,375,1,2,4,2,0,6,2,0,4,0,5,23,0,971,6,4,10,13,3,7,2,0,3,7,0,14,15,8,0,10,15,8,0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck3 : rCandidate rpA3 2 263891376406528 rpC3 = rpM3 := by decide +kernel
private def rpP3 := rcPlan rpM3 7252
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan3 : rcPlanOK rpP3 rpM3 86 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry3 : rCompareState (rcPext rpP3) (rcExpand rpA3 263891376406528) rpA4 = true := by decide +kernel
private theorem rpStep3 : RStep rpA3 rpA4 2 263891376406528 :=
  rCheckedStep rpCheck3 (fun _ hi => rcLift rpPlan3 hi) rpCarry3 (rDense_trunc _ _ _)
private def rpC4 : List RSClause := [(8,24,1,1,5),(4,24,4,3,24),(6,24,4,2,8),(3,5,4,4,24),(8,24,3,3,22),(3,7,4,4,8),(2,24,2,4,8),(2,24,3,4,23),(0,8,2,2,2),(1,9,3,3,44),(3,4,4,12,24),(3,6,4,12,8),(4,24,3,4,24),(6,24,2,4,8),(0,8,2,12,2),(0,8,3,2,46),(1,8,2,12,2),(1,8,3,2,46),(5,7,4,4,12),(0,8,3,3,44),(2,24,4,4,8),(1,8,2,2,2),(0,8,2,3,46),(0,24,2,4,8),(0,24,4,2,8),(1,8,2,3,46),(3,4,4,4,24),(3,6,4,4,8),(2,6,4,4,8),(2,24,4,3,23),(3,5,4,3,24),(3,7,4,2,8),(0,8,3,12,44),(1,8,3,12,44),(1,9,2,2,2),(2,24,4,2,8),(0,24,3,4,23),(0,24,4,3,23),(1,8,3,3,44),(2,4,4,4,24),(5,9,0,3,22),(7,9,0,2,0),(0,2,2,4,8),(1,3,2,4,8),(2,5,4,4,24),(2,7,4,4,8),(4,24,4,1,12),(5,9,3,3,22),(6,24,4,1,12),(7,9,2,2,0),(0,4,3,4,24),(0,6,2,4,8),(0,8,12,2,2),(0,24,1,4,12),(0,24,4,1,12),(1,4,3,4,24),(1,6,2,4,8)]
private def rpM4 := rSparse [289,0,40,0,5,0,2,0,1008,14,3,3,61,0,13,0,2,0,2,0,2,4,1,4,2,0,0,2,3,6,0,3,1,1,6,0,0,0,10,1,4,1,5,0,0,0,0,0,0,0,28,10,1,4,1,0,0,0,0,10,5,9,1,1,1,2,4,1,4,2,0,0,16,3,1,0,0,0,4,10,1,0,0,4,5,1,3,1,0,7,6,0,4,0,4,0,7,2,13,1,0,3,0,7,9,3,5,6,4,0,1,0,0,2,11,1,0,1,2,0,0,0,0,0,0,1,0,2,3,2,0,0,0,0,3,0,1,2,0,0,4,0,0,0,2,6,4,0,1,1,2,5,4,0,1,0,1,0,0,0,0,0,0,0,0,0,0,4,3,2,0,0,0,0,3,0,1,2,0,0,0,0,0,0,22,0,30,0,30,0,0,0,18,0,30,0,30,0,0,0,1751,41,6,3,7,5,2,0,0,0,0,6,7,19,12,10,1,1,1,4,4,0,0,0,2,3,3,9,0,0,3,1,1,6,0,0,20,1,4,3,0,0,0,0,2,2,15,1,0,1,9,1,0,10,0,12,12,3,4,0,1,0,1,0,0,0,0,0,2,1,0,2,1,3,2,0,0,0,5,0,0,6,0,0,11,3,2,0,0,0,0,7,0,0,0,2,0,1,0,1,0,0,0,0,0,0,0,0,0,4,1,3,2,0,0,0,5,0,0,6,1,2,8,1,1,2,0,0,0,0,3,0,0,0,22,0,30,0,30,0,0,0,18,0,30,0,30,0,0,0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck4 : rCandidate rpA4 1 8416809216 rpC4 = rpM4 := by decide +kernel
private def rpP4 := rcPlan rpM4 16856
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan4 : rcPlanOK rpP4 rpM4 350 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry4 : rCompareState (rcPext rpP4) (rcExpand rpA4 8416809216) rpA5 = true := by decide +kernel
private theorem rpStep4 : RStep rpA4 rpA5 1 8416809216 :=
  rCheckedStep rpCheck4 (fun _ hi => rcLift rpPlan4 hi) rpCarry4 (rDense_trunc _ _ _)
private def rpC5 : List RSClause := [(10,24,2,0,0),(10,24,3,0,22),(10,24,0,0,0),(4,24,5,0,33),(0,24,5,2,34),(0,24,2,5,34),(6,24,5,0,33),(9,11,1,1,5),(0,24,3,5,44),(0,24,5,3,44),(4,24,5,3,44),(0,24,5,1,36),(6,24,5,2,34),(0,24,1,5,36),(9,10,1,12,5),(8,24,5,1,36),(10,24,2,2,0),(5,11,3,0,22),(7,11,2,0,0),(10,24,3,3,22),(0,2,5,5,34),(0,8,5,1,36),(4,24,3,5,44),(6,24,2,5,34),(9,11,2,2,0),(7,11,0,2,0),(9,11,3,3,22),(1,9,5,1,36),(1,2,5,5,34),(5,9,5,1,36),(7,9,5,1,36),(8,24,1,5,36),(10,24,1,1,5),(9,10,2,12,0),(0,4,5,3,44),(0,6,5,2,34),(1,4,5,3,44),(1,6,5,2,34),(5,7,5,5,33),(0,6,2,5,34),(1,6,2,5,34),(9,10,3,12,22),(5,11,0,0,1),(7,11,0,0,0),(0,10,2,2,2),(5,7,0,5,33),(5,7,5,0,33),(5,11,0,3,22),(5,11,4,1,12),(7,11,4,1,12),(0,4,3,5,44),(0,4,5,5,36),(0,6,5,5,34),(0,10,3,3,23),(1,4,3,5,44),(1,5,5,5,36),(1,7,5,5,34),(1,11,2,2,2),(2,24,2,5,34),(2,24,3,5,44),(4,24,5,5,33),(6,24,5,5,33),(8,10,1,1,5),(1,11,3,3,23),(0,24,5,5,34),(2,24,0,5,33),(2,24,5,0,33),(2,24,5,2,34),(2,24,5,3,44),(4,7,5,0,33),(4,24,1,5,36),(4,24,5,1,36),(5,6,0,5,33),(5,10,0,3,22),(6,24,1,5,36),(6,24,5,1,36),(10,24,1,4,12),(0,10,2,3,23),(0,10,3,2,23),(1,3,5,5,34),(3,4,5,5,33),(3,4,5,12,33),(3,5,5,5,33),(3,6,5,5,33),(3,6,5,12,33),(3,7,5,5,33),(1,10,2,3,23),(1,10,3,2,23),(1,11,4,1,12),(2,24,5,5,33),(3,5,5,0,33),(3,7,5,0,33),(3,11,4,2,8),(4,24,0,5,33),(5,11,3,3,22),(5,11,4,3,24),(6,24,0,5,33),(7,11,2,2,0),(7,11,4,2,8),(8,10,1,12,5),(8,10,12,1,5),(8,11,1,1,5),(8,11,12,1,5),(9,10,1,1,5),(9,11,2,0,0),(9,11,3,0,22),(0,8,5,2,34),(1,8,5,1,36),(1,8,5,2,34)]
private def rpM5 := rSparse [1066,0,0,0,67,0,53,0,38,0,6,0,6,0,166,1,50,0,0,13,0,0,3,7,4,0,4,1,29,4,0,0,17,12,1,5,1,1,0,2,1,26,973,43,166,5,0,27,16,6,15,5,7,4,5,72,271,41,0,18,12,1,0,12,101,0,1,1,0,2,0,1,1,0,10,3,0,0,1,0,27,6,0,29,14,5,0,14,0,0,16,6,29,0,3,0,0,17,12,1,0,4,1,0,7,342,0,2,1,0,142,0,2,1,0,192,0,2,1,0,1204,0,0,0,232,0,51,0,37,0,6,0,6,0,583,0,0,2,0,1,114,0,201,0,6,0,487,0,249,96,0,350,0,146,0,0,2,1,0,0,0,0,0,1,1,3,2,1,1,1,111,10,1,2,2,0,0,0,0,0,0,0,3,4,0,0,0,22,0,536,0,1,1,142,0,0,0,0,0,0,0,2105,1,70,154,0,0,2,0,1,7,2,3,0,23,1,10,16,5,1,0,10,1,5,1,2,0,1,1,1020,24,8,0,38,157,13,16,4,10,2,3,24,50,173,3,0,1,0,0,0,1,0,0,3,3,0,1,0,0,73,53,5,1,11,0,0,13,8,0,40,154,14,15,0,3,0,0,15,25,9,0,16,5,1,0,10,0,0,5,0,0,6,195,0,1,0,0,144,0,1,0,0,344,0,1,0,0,1819,0,0,13,0,0,280,0,36,0,5,0,653,0,85,260,0,350,0,125,0,0,0,0,0,0,6,7,0,3,0,0,2,3,0,0,0,112,0,0,0,0,1,0,0,2,0,1,1,11,1,1,1,1,35,0,522,0,0,0,0,0,0,0,142,0,2,1,2866,3,1,11,29,12,9,89,6,1,0,21,11,15,133,7,6,0,6,9,121,8,3,0,3,11,159,3,9,3,0,0,0,102,36,0,5,2,0,0,0,98,81,0,6,71,0,4,1,4,1,0,7,1,4,1,41,8,0,59,2,4,2,0,0,12,2,0,4,1,87,0,6,7,0,0,136,8,0,3,0,0,302,0,1,1,142,0,2,1,2507,152,546,0,1,30,118,0,1,38,157,152,193,6,80,0,0,3,1,0,0,0,1,1,0,0,0,6,1,0,0,1,0,0,0,30,7,77,0,0,1,0,0,0,2,3,3,0,0,0,1,3,0,1,0,0,1,76,0,5,0,144,0,6,0,323,0,0,0,0,0,0,0,142,0,0,0,0,0,0,0,3606,3,2,21,0,121,12,9,4,1,205,3,1,15,8,0,118,12,0,9,5,1,134,13,143,12,259,1,147,1,3593,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,137,0,0,0,0,0,0,0,0,0,0,0,0,0,0,198,38,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,75,37,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,123,151,284,0,0,0,0,0,0,0,142,0,0,0,0,0,0,0,4388,0,148,0,206,0,148,0,4006,0,0,2,1,0,0,0,0,0,1,1,3,2,1,1,1,112,0,0,0,0,1,0,0,2,0,1,1,11,1,1,1,1,161,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,111,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,208,0,0,0,0,0,0,0,142,0,0,0,0,0,0,0,9644,0,1,1,142,0,2,1,193,0,0,0,0,0,0,0,142,0,0,0,0,0,0,0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck5 : rCandidate rpA5 16 281466386776064 rpC5 = rpM5 := by decide +kernel
private def rpP5 := rcPlan rpM5 68600
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan5 : rcPlanOK rpP5 rpM5 859 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry5 : rCompareState (rcPext rpP5) (rcExpand rpA5 281466386776064) rpA6 = true := by decide +kernel
private theorem rpStep5 : RStep rpA5 rpA6 16 281466386776064 :=
  rCheckedStep rpCheck5 (fun _ hi => rcLift rpPlan5 hi) rpCarry5 (rDense_trunc _ _ _)
private def rpC6 : List RSClause := [(12,24,4,1,17),(2,24,6,4,24),(8,24,6,1,5),(6,24,6,0,1),(5,13,3,4,30),(5,12,3,4,30),(9,11,6,0,1),(4,24,6,0,1),(0,24,3,6,24),(0,24,6,3,24),(12,24,3,4,23),(12,24,1,1,15),(12,24,1,4,17),(12,24,4,3,23),(12,24,5,1,36),(5,13,5,1,36),(3,9,6,6,1),(8,24,6,3,22),(5,13,3,0,45),(5,13,0,0,33),(11,13,2,4,8),(6,24,6,4,12),(7,13,5,1,36),(5,12,0,3,45),(4,24,6,3,22),(9,13,1,1,15),(0,12,2,4,8),(1,13,2,4,8),(2,24,4,6,24),(5,13,0,3,45),(3,7,6,6,1),(5,12,3,3,30),(0,2,6,6,24),(3,6,6,6,1),(3,6,6,12,1),(4,12,3,4,30),(5,13,3,3,30),(11,13,1,1,15),(1,2,6,6,24),(12,24,3,0,45),(12,24,4,4,8),(1,7,6,6,5),(2,24,0,6,1),(2,24,6,0,1),(5,12,4,4,17),(5,13,4,3,30),(9,11,6,3,22),(11,13,3,4,23),(2,12,4,4,8),(2,24,6,6,1),(3,5,6,0,1),(3,7,6,0,1),(5,7,0,6,1),(5,12,4,12,17),(8,24,3,6,22),(11,13,2,3,23),(12,24,2,4,8),(12,24,4,2,8),(0,24,6,6,5),(2,24,3,6,22),(2,24,6,3,22),(3,13,4,4,8),(4,12,4,3,30),(5,12,4,3,30),(5,13,5,0,33),(6,24,0,6,1),(11,13,3,3,23),(0,6,6,6,5),(1,3,6,6,24)]
private def rpM6 := rSparse [2725,17,1,15,6,6,11,1,0,3,3,1,3,10,1,15,2,6,10,3,3,2,5,9,678,1,1,1,1,39,12,8,4,339,4,1567,192,2,462,186,3,164,10,5,4,1,623,88,68,63,76,133,498,0,136,4,31,2,1899,16,22,0,0,3503,0,0,6,0,1,3,12,0,2,6,13,12,6,0,2,10,4,203,18,16,1,7,5,2313,1,303,44,1,1292,40,31,1,0,1,267,171,5,3,5,0,0,0,306,0,859,13,50,21,4,436,31,17,99,179,6,0,1,5,10,0,2,20,1461,19,62,7,4,10,18,3,0,3,80,1,23,26,6,0,2,8,1,1589,3,3,3,3444,1,1,1,1,320,8,22,3,162,3,1580,195,8,619,11,9,165,5,5,6,1,465,259,75,47,106,136,452,0,143,4,41,8,1872,10,2,0,34,6353,1,113,48,1,1484,30,35,1,0,6,73,180,2,2,7,0,0,0,493,1,859,13,49,16,9,245,31,16,103,358,9,3,3,1,14,1,15,2,1280,17,47,10,13,0,3,18,15,3,267,1,38,10,3,3,2,3,1,1409,2,4,2,5638,19,30,5,73,27,3,30,8,5,311,172,160,22,22,3,3,2,2,3,15,3,10,0,424,173,222,6,281,6,69,1,1,6,87,87,2,0,6,73,151,3,50,3,5,5,8,2,27,0,11,0,405,2,1,168,1,1,149,3,9,19,436,1,1,4,3,6,2,0,162,2,0,3,3,6,2,1,277,0,175,7,4,0,0,0,12,3,0,7,0,1,0,0,19,3,564,1,1,1,3,3,1,4,433,185,540,3,1,4,6045,5,0,181,4,0,193,13,22,0,2,0,93,1,3,1,7,0,0,0,1617,0,100,7,2,0,7,0,2,1857,0,5,0,3,1,0,0,0,8,0,0,3,10,0,0,0,2,8,0,0,1,3,0,2,20360,1,3,1,7,0,0,0,354,2,79,8,1,84,2,91,8,1,18,6,44,13,44,17,113,11,5,10,11,12,34,8,1,5,8,1,15,12,5,11,12,13,93,0,0,0,0,3,2,93,0,80,0,0,0,0,2,3,79,0,53,2,3,2,13,1,3,0,0,0,4,0,139,1,3,1,4,0,1,0,0,0,10,12,99,0,1,0,0,0,264,0,77,0,2,2,95,0,71,1,3,0,3,2,3,2,70,0,2,0,69,1,3,2,13,1,3,1,4,0,2,0,110,1,3,2,8,0,117,1,3,2,4,0,2,0,4,1,3,2,83,0,0,0,0,0,0,0,0,0,0,2,2,0,1,0,0,0,0,0,82,0,78,0,0,0,0,0,0,0,0,0,0,1,1,2,1,0,0,0,0,0,69,0,82,0,0,0,0,0,0,0,0,0,0,0,65,0,0,0,0,0,0,0,42,0,0,0,104,0,16,0,0,0,38,4,0,0,2,0,0,10,0,0,0,3,5,0,0,0,0,0,0,0,10,0,0,0,0,6,0,2,5,0,0,0,609,0,1,0,0,0,398,0,0,0,0,182,0,0,0,0,536,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck6 : rCandidate rpA6 36 792739058 rpC6 = rpM6 := by decide +kernel
private def rpP6 := rcPlan rpM6 168364
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan6 : rcPlanOK rpP6 rpM6 692 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry6 : rCompareState (rcPext rpP6) (rcExpand rpA6 792739058) rpA7 = true := by decide +kernel
private theorem rpStep6 : RStep rpA6 rpA7 36 792739058 :=
  rCheckedStep rpCheck6 (fun _ hi => rcLift rpPlan6 hi) rpCarry6 (rDense_trunc _ _ _)
private def rpC7 : List RSClause := [(14,24,6,1,5),(14,24,4,1,12),(14,24,1,4,12),(14,24,6,0,4),(8,24,7,1,10),(0,8,2,7,2),(1,8,2,7,2),(12,24,7,1,15),(7,15,0,6,4),(7,14,0,6,4),(14,24,2,4,23),(12,24,7,0,0),(4,24,7,0,1),(14,24,5,1,36),(7,15,5,1,36),(6,24,7,0,0),(5,12,7,4,18),(8,24,2,7,0),(0,24,2,7,2),(7,15,2,0,35),(0,24,7,2,2),(5,15,3,6,22),(14,24,1,1,5),(7,14,4,6,12),(13,15,1,1,17),(9,15,1,1,5),(0,14,3,4,23),(1,15,3,4,23),(3,4,7,7,1),(6,24,7,2,0),(7,15,0,2,35),(8,24,7,7,0),(14,24,4,2,23),(14,24,6,6,4),(0,8,7,6,10),(8,24,6,7,1),(3,15,6,6,4),(8,24,7,2,0),(9,12,1,7,15),(13,14,1,4,17),(2,24,4,7,8),(2,24,7,4,8),(3,9,7,7,0),(3,13,7,7,0),(7,15,0,0,4),(11,15,3,4,23),(12,24,7,4,8),(14,24,6,3,22),(14,24,6,4,12),(0,8,6,7,10),(1,8,6,7,10),(8,14,6,1,5),(8,15,6,1,5),(8,24,0,7,0),(8,24,1,7,10),(8,24,7,0,0),(12,24,0,7,0),(14,24,0,6,4),(0,8,7,7,2),(1,8,7,1,10),(3,15,4,4,23),(7,14,6,6,4),(7,15,2,2,34),(8,14,1,1,5),(8,24,7,6,1),(9,13,7,1,15),(9,15,1,6,5),(12,24,4,7,8),(13,15,4,1,17),(14,24,3,6,22),(14,24,4,6,12),(1,8,7,7,2)]
private def rpM7 := rSparse [2439,1,223,82,1701,0,688,595,49,3,15,39,19,35,6,41,71,41,100,5265,1,203,100,1885,41,265,772,1304,0,40,6,5,2,162,37,129,18,1,35,31,94,0,0,381,784,37,169,122,1,26,239,0,141,61,677,4591,0,687,494,150,4,14,39,26,28,6,41,71,41,113,7442,41,368,546,1359,2,167,0,40,6,78,30,124,19,10,28,54,77,0,0,379,778,39,169,224,1,22,145,0,144,78,652,4341,1,122,1,98,0,0,0,24,2,45,1,387,124,1042,1,15,1,182,0,3,119,0,3,217,0,0,137,1,13,0,69,3,124,124,100,0,467,124,274,0,1,0,42,0,459,1,6,0,24,1,0,1,217,1,85,3,625,1,5029,1,122,1,1217,3,52,3,47,18,0,81,17,0,282,1,16,0,9602,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1478,0,20,0,50,0,14,0,6309,124,850,0,1,3,1,1,396,124,153,0,411,124,568,124,221,0,0,6,0,18123,0,244,0,8,90,1,6,47,0,4,0,12,0,76,0,0,0,2,0,0,0,9,1,5,0,40,0,59,3,134,0,42,0,14,3,1,4,19,56,63,100,23,0,80,0,0,0,151,0,29,0,6,0,12,0,0,0,0,14,0,0,0,0,0,0,0,14,0,0,14,0,2,0,42,0,530,0,0,0,36,0,173,56,16,100,351,0,0,0,114,0,0,2,0,0,4,0,0,0,4,0,0,0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck7 : rCandidate rpA7 40 1953679 rpC7 = rpM7 := by decide +kernel
private def rpP7 := rcPlan rpM7 135632
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan7 : rcPlanOK rpP7 rpM7 328 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry7 : rCompareState (rcPext rpP7) (rcExpand rpA7 1953679) rpA8 = true := by decide +kernel
private theorem rpStep7 : RStep rpA7 rpA8 40 1953679 :=
  rCheckedStep rpCheck7 (fun _ hi => rcLift rpPlan7 hi) rpCarry7 (rDense_trunc _ _ _)
private def rpC8 : List RSClause := [(16,24,5,0,33),(16,24,6,0,4),(10,24,8,2,2),(16,24,7,0,0),(16,24,2,0,0),(16,24,5,1,38),(16,24,0,0,0),(16,24,5,5,33),(16,24,3,0,22),(16,24,5,2,34),(16,24,5,3,44),(2,24,6,8,1),(0,24,8,2,2),(5,12,8,7,15),(0,24,2,8,2),(10,24,1,8,5),(10,24,8,0,1),(11,15,8,1,5),(11,13,8,1,15),(16,24,1,5,38),(9,17,1,1,38),(7,14,2,8,37),(9,17,7,2,0),(10,24,8,1,5),(12,24,7,8,2),(0,24,8,5,36),(9,16,1,12,38),(14,24,6,8,5),(0,24,5,8,36),(0,2,8,7,2),(1,2,8,7,2),(9,17,7,6,7),(10,14,8,8,5),(6,24,8,2,2),(10,15,8,1,5),(9,17,6,3,22),(9,17,7,7,0),(8,24,6,8,1),(8,24,8,1,5),(12,24,8,1,15),(16,24,7,2,0),(5,17,5,0,33),(16,24,2,5,34),(3,4,8,7,1),(9,16,6,7,7),(9,17,1,5,38),(6,24,8,0,1),(0,16,5,5,34),(16,24,7,1,18),(0,2,8,8,2),(5,16,0,5,33),(9,16,7,6,7),(9,17,6,7,7),(15,17,1,5,38),(1,2,8,8,2),(4,24,8,0,1),(7,14,8,6,5),(7,16,5,5,33),(8,24,7,8,1),(11,13,8,8,2),(13,17,4,2,8),(0,2,8,5,37),(1,2,8,5,37),(3,6,6,8,1),(9,16,7,7,0),(11,15,8,8,5),(1,17,5,5,34),(0,16,2,5,34),(1,16,2,5,34),(5,12,5,8,36),(7,17,0,0,0),(9,16,7,12,0),(10,13,8,1,15),(0,2,5,8,37),(1,2,5,8,37),(1,17,7,7,8),(4,17,7,0,7),(5,17,5,5,33),(8,17,6,7,7),(9,17,2,7,0),(10,14,8,12,5),(1,16,5,1,38),(9,17,0,5,33),(0,16,4,1,12),(0,16,5,2,34),(0,16,5,12,34),(0,24,1,8,5),(0,24,8,1,5),(0,24,8,8,2),(1,16,5,2,34),(1,17,4,1,12),(3,4,6,8,1),(3,6,7,8,1),(5,13,8,1,15),(5,17,3,0,22),(6,24,8,5,36),(7,14,0,8,6),(7,14,5,8,36),(7,15,8,1,5),(7,16,0,5,33),(7,16,2,5,34),(7,17,2,2,0),(8,24,8,7,1),(9,16,2,7,0),(9,16,3,6,22),(9,17,7,0,0),(10,24,6,8,1),(13,17,1,7,18),(15,17,6,1,12),(16,24,6,1,12),(0,14,2,8,37),(0,24,6,8,5),(0,24,7,8,2),(0,24,8,6,5),(0,24,8,7,2),(1,14,2,8,37),(8,16,1,1,38),(8,17,1,1,38),(8,17,7,6,7)]
private def rpM8 := rSparse [1183,48,1,3,1,1,0,14,23,11,11,0,296,29,673,229,281,3,323,135,0,0,0,0,0,0,3,0,0,162,0,0,0,0,0,8,0,121,6,21,298,22,0,4,0,20,51,0,102,0,2,0,4,0,0,5,17,0,1,1,11,1,3,19,3,0,0,0,0,0,8,0,1,125,144,0,16,11,0,28,887,46,1,3,1,2,0,13,23,12,13,0,1477,6,89,2,390,1,87,9,95,1,1,1,311,1,140,1,74,8,0,0,4,2,0,67,6,0,131,2,6,0,0,0,3,3,284,0,0,0,1965,41,719,180,280,3,323,185,0,0,0,0,0,0,3,0,0,117,0,0,0,0,0,0,0,125,7,69,249,53,0,16,0,4,0,16,110,0,2,0,5,0,0,3,13,4,1,1,11,1,3,19,8,0,0,0,0,0,0,0,5,76,193,0,15,12,0,27,2491,1,93,0,410,1,21,9,141,1,1,1,306,12,154,1,6,10,0,0,4,2,0,116,1,0,135,0,5,0,0,1,3,3,280,0,11,0,3677,46,825,0,4471,0,131,0,3699,42,568,0,1,0,41,46,217,0,3762,0,0,36,1,189,2,1,40,2,2,84,1,0,0,0,0,0,0,131,0,2,1,184,2,89,0,328,0,3984,2,3814,0,130,18,82,1,57,1,164,1,16,1,20,3,2,0,38,3,2,0,78,0,36,0,2,3,76,0,0,0,0,0,24,15,2,21,25,20,44,0,58,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,0,157,46,8743,1,10,18,11,3,2,35,7,2,29,0,48,1,8,0,178,17,2,0,26,15,2,0,71,0,1,0,83,0,0,0,38,0,0,0,0,0,5,1,6,0,2,0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck8 : rCandidate rpA8 16 5703717727342 rpC8 = rpM8 := by decide +kernel
private def rpP8 := rcPlan rpM8 64288
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan8 : rcPlanOK rpP8 rpM8 388 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry8 : rCompareState (rcPext rpP8) (rcExpand rpA8 5703717727342) rpA9 = true := by decide +kernel
private theorem rpStep8 : RStep rpA8 rpA9 16 5703717727342 :=
  rCheckedStep rpCheck8 (fun _ hi => rcLift rpPlan8 hi) rpCarry8 (rDense_trunc _ _ _)
private def rpC9 : List RSClause := [(8,24,9,1,38),(18,24,6,4,12),(17,19,0,6,7),(18,24,1,4,12),(2,24,9,4,24),(18,24,4,1,12),(18,24,4,6,12),(18,24,7,6,1),(2,24,5,9,33),(12,24,9,1,17),(18,24,5,1,36),(0,2,5,9,44),(1,2,5,9,44),(12,24,4,9,17),(6,24,9,0,4),(3,6,9,5,33),(7,14,9,4,17),(17,19,7,1,18),(5,19,3,3,26),(5,19,3,4,26),(17,19,5,3,46),(5,18,3,3,26),(13,19,1,4,18),(17,19,1,6,12),(18,24,6,1,5),(18,24,7,4,8),(2,24,9,5,33),(3,12,4,9,30),(5,18,3,4,26),(5,19,3,0,27),(17,19,2,4,8),(2,7,6,9,4),(2,24,4,9,24),(5,18,0,3,27),(5,18,3,6,26),(10,24,9,0,4),(17,19,0,5,35),(18,24,8,6,1),(0,8,3,9,44),(0,24,9,5,38),(1,8,3,9,44),(17,19,0,0,0),(0,2,9,9,24),(0,24,5,9,38),(1,2,9,9,24),(2,24,9,6,4),(8,24,1,9,38),(11,13,3,9,30),(12,19,4,1,18),(13,19,4,1,18),(16,24,9,0,4),(17,19,6,6,7),(2,18,6,4,26),(2,19,6,4,26),(2,24,0,9,4),(2,24,9,0,4),(12,24,0,9,33),(12,24,9,0,33)]
private def rpM9 := rSparse [1638,0,0,0,0,6579,174,1592,809,11,18,1590,0,0,0,1,6776,53,1594,809,11,18,5124,3,8,0,0,0,8,87,7,9,0,0,0,8,127,2,8,0,4245,0,1190,0,0,0,0,9602,0,165,81,35,68,46,0,373,0,4,0,120,0,0,0,8,0,0,0,41,0,14,69,1,31,0,12,56,1,5,0,35,0,0,0,37,2,3,0,0,0,19,0,1,0,3,0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck9 : rCandidate rpA9 260 205347809787920 rpC9 = rpM9 := by decide +kernel
private def rpP9 := rcPlan rpM9 76048
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan9 : rcPlanOK rpP9 rpM9 95 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry9 : rCompareState (rcPext rpP9) (rcExpand rpA9 205347809787920) rpA10 = true := by decide +kernel
private theorem rpStep9 : RStep rpA9 rpA10 260 205347809787920 :=
  rCheckedStep rpCheck9 (fun _ hi => rcLift rpPlan9 hi) rpCarry9 (rDense_trunc _ _ _)
private def rpC10 : List RSClause := [(6,24,10,0,4),(10,24,10,0,4),(10,24,10,8,5),(20,24,3,0,22),(20,24,3,3,22),(17,19,10,6,12),(10,12,10,10,17),(20,24,3,4,23),(20,24,5,5,33),(20,24,5,1,36),(20,24,5,0,33),(20,24,6,3,22),(20,24,9,3,22),(20,24,8,5,36),(20,24,3,9,22),(20,24,5,2,34),(20,24,4,3,23),(20,24,3,2,23),(20,24,9,5,33),(6,24,0,10,4),(3,6,6,10,4),(3,6,5,10,39),(1,2,10,6,24),(16,24,10,5,38),(3,6,10,10,4),(20,24,5,3,44),(10,24,8,10,5),(2,24,10,4,24),(0,2,10,6,24),(7,20,0,5,33),(8,24,6,10,4),(10,24,10,3,24),(15,21,1,1,36),(20,24,5,9,33),(20,24,8,6,1),(7,21,5,0,33),(20,24,3,6,22),(7,13,10,4,17),(3,6,9,10,4),(5,12,0,10,39),(12,24,4,10,17),(15,20,1,9,41),(15,20,1,12,36),(4,24,10,0,4),(5,20,3,5,44),(7,20,2,5,34),(9,20,3,6,22),(14,20,6,9,22),(19,21,4,3,23),(20,24,0,0,0),(0,8,9,10,38),(0,20,3,5,44),(1,8,9,10,38),(1,20,3,5,44),(14,20,6,4,26),(4,12,0,10,39),(4,20,7,6,1),(5,12,3,10,32),(7,13,0,10,39),(13,21,1,5,36),(13,21,3,4,23),(14,21,8,1,36),(19,21,6,3,26),(0,4,10,10,5),(0,20,2,3,23),(0,20,5,3,44),(0,20,9,5,41),(0,24,6,10,5),(1,20,2,3,23),(1,20,5,3,44),(1,20,9,5,41),(3,6,10,5,39)]
private def rpM10 := rSparse [6140,1,3017,0,1201,10,4,6,70,10,31,1,1188,10,1456,1,1375,10]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck10 : rCandidate rpA10 128 10725122781296 rpC10 = rpM10 := by decide +kernel
private def rpP10 := rcPlan rpM10 18620
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpPlan10 : rcPlanOK rpP10 rpM10 18 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCarry10 : rCompareState (rcPext rpP10) (rcExpand rpA10 10725122781296) rpA11 = true := by decide +kernel
private theorem rpStep10 : RStep rpA10 rpA11 128 10725122781296 :=
  rCheckedStep rpCheck10 (fun _ hi => rcLift rpPlan10 hi) rpCarry10 (rDense_trunc _ _ _)
private def rpC11 : List RSClause := [(14,24,6,11,22),(22,24,4,3,24),(7,14,0,11,33),(18,24,11,6,7),(21,23,3,4,30),(0,18,6,11,26),(1,18,6,11,26),(4,24,11,6,7),(7,14,2,11,34),(8,24,11,2,0),(12,24,11,4,8),(21,23,3,9,30),(2,24,11,4,8),(3,4,4,11,26),(8,10,11,11,0),(8,24,7,11,0),(18,22,6,4,12),(21,23,3,5,47),(21,23,5,9,41),(0,8,3,11,44)]
private def rpM11 := rSparse []
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rpCheck11 : rCandidate rpA11 1280 123205914198913 rpC11 = rpM11 := by decide +kernel
private theorem rpStep11 : RStep rpA11 rpA12 1280 123205914198913 := rZeroStep rpCheck11
theorem pg3Exhaust : rcSearch [] 0 rcData = false :=
  (rpStep0.dead (rpStep1.dead (rpStep2.dead (rpStep3.dead (rpStep4.dead (rpStep5.dead (rpStep6.dead (rpStep7.dead (rpStep8.dead (rpStep9.dead (rpStep10.dead (rpStep11.dead (rEmptyDead rpA12 rfl []))))))))))))) [] 0 ⟨0, by decide, .nil, rfl⟩ ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461

private def pg3Masks : List ℕ := [7405575, 59244600, 192832, 33885824, 12853396, 17842785, 2757642, 4737289, 9474578, 16852260, 39878850, 17597457, 1456132, 10506408, 25297676, 34613360, 4917506, 115585, 52560968, 2904073, 43057698, 20980052, 1603616, 2143424, 33966600, 13140242, 23330829, 2688035, 5376070, 10559652, 17008384, 38013080, 18088469, 8925488, 8704640, 33646752, 3199041, 33719874, 5769235, 2425989, 34352144, 11669510, 21119304, 12648838, 4221376, 19931236, 25248544, 36176938, 33858704, 1378821, 732416, 9048330, 22052945, 6308041, 1202752, 58982936, 1871889, 2495500, 2720771, 50340976, 26280484, 34802178, 408580, 39977034, 21496089, 41976466, 19415081, 52445288, 6619269, 51119128, 17343760, 1656865, 9711636]
private abbrev pg3Inc (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
private abbrev pg3Oriented (a b : Fin 26) := a.val < 13 ∧ 13 ≤ b.val ∧
    (a.val + 26 - b.val) % 13 ∈ ([0,1,3,9] : List ℕ)
private abbrev pg3Bits (m : ℕ) (p : Fin 13) := m.testBit p.val = true
private abbrev pg3Miss (m : ℕ) (l : Fin 13) := ∀ p : Fin 13, pg3Bits m p → ¬ pg3Inc p l
private abbrev pg3Valid (m : ℕ) :=
    (∀ p : Fin 13, ¬pg3Bits m p → ∃ l, pg3Miss m l ∧ pg3Inc p l) ∧
    ((¬∃ l, ∀ p, pg3Bits m p → pg3Inc p l) ∧ ¬∃ p, ∀ l, pg3Miss m l → pg3Inc p l) ∧
    ∀ k : Fin 26, m.testBit k.val = true ↔
      (∃ p, pg3Bits m p ∧ k = Fin.castAdd 13 p) ∨ ∃ l, k = Fin.natAdd 13 l ∧ pg3Miss m l
set_option synthInstance.maxSize 2000 in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem pg3RowsValid : ∀ m ∈ pg3Masks, pg3Valid m := by
  have cert : pg3Masks.all (fun m => decide (pg3Valid m)) = true := by decide +kernel
  intro m hm
  exact of_decide_eq_true (List.all_eq_true.mp cert m hm)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem pg3RowsSeparate : ∀ v a b : Fin 26, a ≠ v → b ≠ v →
    ¬ (pg3Oriented a b ∨ pg3Oriented b a) →
    ∃ m ∈ pg3Masks, m.testBit a.val = true ∧ m.testBit b.val = true ∧ m.testBit v.val = false := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem pg3Geom :
      let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let oriented := fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧
        (a.val + 26 - b.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let free := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ q ∈ P, ¬ I q l
      let U := fun (P : Finset (Fin 13)) => Finset.univ.filter fun k : Fin 26 =>
        (∃ p ∈ P, k = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ free P l
      ∀ v a b : Fin 26, a ≠ v → b ≠ v → ¬ (oriented a b ∨ oriented b a) →
        ∃ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l, free P l ∧ I p l) ∧
          ((¬∃ l, ∀ p ∈ P, I p l) ∧ ¬∃ p, ∀ l, free P l → I p l) ∧
          a ∈ U P ∧ b ∈ U P ∧ v ∉ U P := by
  intro I oriented free U v a b ha hb hind
  obtain ⟨m, hmem, hma, hmb, hmv⟩ := pg3RowsSeparate v a b ha hb hind
  obtain ⟨hm, hg, hbits⟩ := pg3RowsValid m hmem
  let P : Finset (Fin 13) := Finset.univ.filter (pg3Bits m)
  have hp (p : Fin 13) : p ∈ P ↔ pg3Bits m p := by simp [P]
  refine ⟨P, ?_, ?_, ?_⟩
  · simpa only [free, hp, I, pg3Inc, pg3Miss] using hm
  · simpa only [free, hp, I, pg3Inc, pg3Miss] using hg
  · have hu (k : Fin 26) : k ∈ U P ↔ m.testBit k.val = true := by
      simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and, free, I, pg3Miss, pg3Inc, hp]
        using (hbits k).symm
    exact ⟨(hu a).mpr hma, (hu b).mpr hmb, fun h => by simpa [hmv] using (hu v).mp h⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem pg3StrongBounds :
      let I (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let pt := (Fin.castAdd 13 : Fin 13 → Fin 26)
      let ln := (Fin.natAdd 13 : Fin 13 → Fin 26)
      let free (P : Finset (Fin 13)) (l : Fin 13) := ∀ p ∈ P, ¬ I p l
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26, D.WellFormed →
        (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l, I p l → D.eval {pt p, ln l} = true) →
        (∀ P, (∀ p ∉ P, ∃ l, free P l ∧ I p l) →
          ((¬ ∃ l, ∀ p ∈ P, I p l) ∧ ¬ ∃ p, ∀ l, free P l → I p l) →
          D.eval (Finset.univ.filter fun k => (∃ p ∈ P, k = pt p) ∨ ∃ l, k = ln l ∧ free P l) = false) →
        let G (v : Fin 26) := Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
        let LB (T : Finset (Fin 26)) (k : ℕ) := ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
          (∀ U, T ⊆ U → E.eval U = D.eval U) → k ≤ E.size
        (D.outVars = ∅ ∧ 11 ≤ D.size ∧ (∀ v, (G v).card + 9 ≤ D.size) ∧
          (∀ p l, ¬ I p l → (G (pt p) ∪ G (ln l)).card + 7 ≤ D.size) ∧
          (∀ p q, p ≠ q → (G (pt p) ∪ G (pt q)).card + 6 ≤ D.size ∧
            (G (ln p) ∪ G (ln q)).card + 6 ≤ D.size)) ∧
        (∀ p q : Fin 13, p ≠ q → LB {pt p,pt q} 6 ∧ LB {ln p,ln q} 6) ∧
        ∀ p l, ¬I p l → LB {pt p,ln l} 8 := by

  have f13_sub_add : ∀ a b : Fin 13, a - b + b = a := by decide
  have f13_add_sub : ∀ a b : Fin 13, a + b - b = a := by decide
  have f13_add_neg : ∀ a b : Fin 13, a + b + (-b) = a := by decide
  have f13_neg_add : ∀ a b : Fin 13, a + (-b) + b = a := by decide
  have f13_neg_add2 : ∀ p l : Fin 13, -l + (p + l) = p := by decide
  have f13_neg_add3 : ∀ p l : Fin 13, -p + (p + l) = l := by decide
  have f13_sub_sub : ∀ a b c : Fin 13, a - b - c = a - (c + b) := by decide
  have f13_add_sub_sub : ∀ a b c : Fin 13, a + b - c = a - (c - b) := by decide
  have f13_sub_eq_add_neg : ∀ a b : Fin 13, a - b = a + (-b) := by decide
  have f13_neg_neg : ∀ a : Fin 13, -(-a) = a := by decide
  have f13_zero_add : ∀ a : Fin 13, 0 + a = a := by decide
  have f13_sub_zero : ∀ a b : Fin 13, a - b = 0 ↔ a = b := by decide
  have f13_neg_inj : ∀ a b : Fin 13, -a = -b ↔ a = b := by decide
  let incB (p l : Fin 13) : Bool := decide (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)
  let orbsP : List ℕ :=
    [29, 39, 71, 77, 83, 85, 101, 105, 135, 141, 195, 201, 275, 281, 297, 329, 337, 549,
     7, 13, 19, 21, 25, 35, 37, 41, 67, 69, 73, 81, 97, 131, 133, 137, 265, 273]
  let orbsW : List ℕ :=
    [2592, 392, 896, 2816, 644, 2688, 2432, 2306, 776, 800, 772, 770, 580, 2624, 2114, 2562, 2564, 2184,
     904, 2848, 708, 2720, 2656, 456, 2440, 2370, 900, 2944, 2818, 2692, 2434, 780, 808, 802, 2626, 2628]
  let orbP (r : Fin 36) (p : Fin 13) : Bool := (orbsP.getD r.val 0).testBit p.val
  let orbW (r : Fin 36) (l : Fin 13) : Bool := (orbsW.getD r.val 0).testBit l.val
  have horb_w_spec : ∀ (r : Fin 36) (l : Fin 13),
      orbW r l = (List.finRange 13).all (fun p => !(orbP r p && incB p l)) := by
    decide +kernel
  have horb_max : ∀ (r : Fin 36) (p : Fin 13),
      orbP r p = false → ∃ l : Fin 13, orbW r l = true ∧ incB p l = true := by
    decide +kernel
  have horb_noncoll : ∀ (r : Fin 36) (l : Fin 13),
      ∃ p : Fin 13, orbP r p = true ∧ incB p l = false := by
    decide +kernel
  have horb_nonconc : ∀ (r : Fin 36) (p : Fin 13),
      ∃ l : Fin 13, orbW r l = true ∧ incB p l = false := by
    decide +kernel
  have horb_ne : ∀ (r1 r2 : Fin 36) (c : Fin 13),
      (r1 ≠ r2 ∨ c ≠ 0) → ∃ p : Fin 13, orbP r1 p ≠ orbP r2 (p - c) := by
    decide +kernel
  let rows0 : List (Fin 36 × Fin 13) := [(0, 0), (0, 9), (0, 10), (0, 11), (1, 0), (1, 8), (1, 11), (1, 12), (2, 0), (2, 7), (2, 11), (2, 12), (3, 0), (3, 7), (3, 10), (3, 11), (4, 0), (4, 7), (4, 9), (4, 12), (5, 0), (5, 7), (5, 9), (5, 11), (6, 0), (6, 7), (6, 8), (6, 11), (7, 0), (7, 7), (7, 8), (7, 10), (8, 0), (8, 6), (8, 11), (8, 12), (9, 0), (9, 6), (9, 10), (9, 11), (10, 0), (10, 6), (10, 7), (10, 12), (11, 0), (11, 6), (11, 7), (11, 10), (12, 0), (12, 5), (12, 9), (12, 12), (13, 0), (13, 5), (13, 9), (13, 10), (14, 0), (14, 5), (14, 8), (14, 10), (15, 0), (15, 5), (15, 7), (15, 10), (16, 0), (16, 5), (16, 7), (16, 9), (17, 0), (17, 4), (17, 8), (17, 11), (18, 0), (18, 11), (18, 12), (19, 0), (19, 10), (19, 11), (20, 0), (20, 9), (20, 12), (21, 0), (21, 9), (21, 11), (22, 0), (22, 9), (22, 10), (23, 0), (23, 8), (23, 12), (24, 0), (24, 8), (24, 11), (25, 0), (25, 8), (25, 10), (26, 0), (26, 7), (26, 12), (27, 0), (27, 7), (27, 11), (28, 0), (28, 7), (28, 10), (29, 0), (29, 7), (29, 9), (30, 0), (30, 7), (30, 8), (31, 0), (31, 6), (31, 12), (32, 0), (32, 6), (32, 11), (33, 0), (33, 6), (33, 10), (34, 0), (34, 5), (34, 10), (35, 0), (35, 5), (35, 9)]
  have rows0_nodup : rows0.Nodup := by
    decide +kernel
  have rows0_ok : rows0.all (fun rc => orbP rc.1 (0 - rc.2)) = true := by
    decide +kernel
  have hL5_bool :
      (List.finRange 13).all (fun p2 =>
        (List.finRange 13).all (fun l =>
          (p2 == 0) || incB 0 l || incB p2 l ||
          (let Y := (List.finRange 13).filter (fun m => (m != l) && !incB 0 m && !incB p2 m)
           let R := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2) && orbW rc.1 (l - rc.2))
           (Y.length == 5) &&
           Y.all (fun m => Nat.ble 5 (R.filter (fun rc => orbW rc.1 (m - rc.2))).length) &&
           Y.all (fun m => R.any (fun rc => !orbW rc.1 (m - rc.2))) &&
           Y.all (fun m1 => Y.all (fun m2 => (m1 == m2) ||
             (R.any (fun rc => orbW rc.1 (m1 - rc.2) && !orbW rc.1 (m2 - rc.2)) &&
              R.any (fun rc => !orbW rc.1 (m1 - rc.2) && !orbW rc.1 (m2 - rc.2)))))))) = true := by
    decide +kernel
  have hL4_bool :
      (List.finRange 13).all (fun p2 =>
        (p2 == 0) ||
        (let Y := (List.finRange 13).filter (fun m => !incB 0 m && !incB p2 m)
         let R := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2))
         (Y.length == 6) &&
         Y.all (fun m => Nat.ble 9 (R.filter (fun rc => orbW rc.1 (m - rc.2))).length) &&
         Y.all (fun m => R.any (fun rc => !orbW rc.1 (m - rc.2))) &&
         Y.all (fun m1 => Y.all (fun m2 => (m1 == m2) ||
           (R.any (fun rc => orbW rc.1 (m1 - rc.2) && !orbW rc.1 (m2 - rc.2)) &&
            R.any (fun rc => !orbW rc.1 (m1 - rc.2) && !orbW rc.1 (m2 - rc.2))))))) = true := by
    decide +kernel
  have hL3_bool :
      (List.finRange 13).all (fun l0 =>
        incB 0 l0 ||
        (let X := (List.finRange 13).filter (fun q => (q != 0) && !incB q l0)
         let R := rows0.filter (fun rc => orbW rc.1 (l0 - rc.2))
         (X.length == 8) &&
         X.all (fun q => R.any (fun rc => orbP rc.1 (q - rc.2))) &&
         X.all (fun q => R.any (fun rc => !orbP rc.1 (q - rc.2))) &&
         X.all (fun q1 => X.all (fun q2 => (q1 == q2) ||
           (R.any (fun rc => orbP rc.1 (q1 - rc.2) && !orbP rc.1 (q2 - rc.2)) &&
            R.any (fun rc => !orbP rc.1 (q1 - rc.2) && !orbP rc.1 (q2 - rc.2))))))) = true := by
    decide +kernel
  have hL2_bool :
      (let Y := (List.finRange 13).filter (fun l => !incB 0 l)
       (Y.length == 9) &&
       Y.all (fun l => rows0.any (fun rc => orbW rc.1 (l - rc.2))) &&
       Y.all (fun l => rows0.any (fun rc => !orbW rc.1 (l - rc.2))) &&
       Y.all (fun l1 => Y.all (fun l2 => (l1 == l2) ||
         (rows0.any (fun rc => orbW rc.1 (l1 - rc.2) && !orbW rc.1 (l2 - rc.2)) &&
          rows0.any (fun rc => !orbW rc.1 (l1 - rc.2) && !orbW rc.1 (l2 - rc.2)))))) = true := by
    decide +kernel
  have hL1_geom :
      let R := (List.finRange 36).flatMap fun r => (List.finRange 13).map fun c => (r, c)
      (∀ p : Fin 13, ∃ rc ∈ R, orbP rc.1 (p - rc.2) = true) ∧
      (∀ p : Fin 13, ∃ rc ∈ R, orbP rc.1 (p - rc.2) = false) ∧
      (∀ l : Fin 13, ∃ rc ∈ R, orbW rc.1 (l - rc.2) = true) ∧
      (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃ rc ∈ R, orbP rc.1 (p1 - rc.2) = true ∧ orbP rc.1 (p2 - rc.2) = false) ∧
      (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃ rc ∈ R, orbP rc.1 (p1 - rc.2) = false ∧ orbP rc.1 (p2 - rc.2) = false) := by
    decide +kernel
  classical
  have sideTrue_def : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool),
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := fun _ _ _ _ _ => rfl
  have eval_def : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := fun _ _ => rfl

  have sideTrue_congr : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k)
      (val val' : Fin k → Bool), (∀ j : Fin k, j < i → val j = val' j) →
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val' := by
    intro k U B F i val val' h
    rw [sideTrue_def, sideTrue_def, decide_eq_decide]
    constructor
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩
  have fuel_indep : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (d d' : ℕ) (i : Fin E.size), i.val < d → i.val < d' →
      E.gateValFuel U d i = E.gateValFuel U d' i := by
    intro E U d
    induction d with
    | zero =>
      intro d' i h
      exact absurd h (Nat.not_lt_zero _)
    | succ e ih =>
      intro d' i h h'
      cases d' with
      | zero => exact absurd h' (Nat.not_lt_zero _)
      | succ e' =>
        have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateValFuel U e' j := by
          intro j hj
          have hji : j.val < i.val := hj
          exact ih e' j (by omega) (by omega)
        show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) =
             (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e') &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e'))
        rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
            sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateVal_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)) (i : Fin E.size),
      E.gateVal U i =
        (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateVal U) &&
         PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateVal U)) := by
    intro E U i
    have hi : i.val < E.size := i.2
    obtain ⟨e, he⟩ : ∃ e, E.size = e + 1 := ⟨E.size - 1, by omega⟩
    have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateVal U j := by
      intro j hj
      have hji : j.val < i.val := hj
      exact fuel_indep E U e E.size j (by omega) j.2
    have h1 : E.gateVal U i = E.gateValFuel U (e + 1) i :=
      fuel_indep E U E.size (e + 1) i i.2 (by omega)
    rw [h1]
    show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
          PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) = _
    rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
        sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateValFuel_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → ∀ (d : ℕ) (i : Fin E.size), E.gateValFuel U d i = true → E.gateValFuel V d i = true := by
    intro E U V hUV d
    induction d with
    | zero => intro i h; cases h
    | succ d ih =>
      intro i h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) = true at h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.leftVars i) (E.leftGates i) i (E.gateValFuel V d) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.rightVars i) (E.rightGates i) i (E.gateValFuel V d)) = true
      rw [Bool.and_eq_true] at h ⊢
      constructor
      · have hL := h.1
        rw [sideTrue_def] at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with h1 | h2
        · rcases h1 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, hv, hUV hu⟩
        · rcases h2 with ⟨j, hj, hlt, hv⟩
          exact Or.inr ⟨j, hj, hlt, ih j hv⟩
      · have hR := h.2
        rw [sideTrue_def] at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with h1 | h2
        · rcases h1 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, hv, hUV hu⟩
        · rcases h2 with ⟨j, hj, hlt, hv⟩
          exact Or.inr ⟨j, hj, hlt, ih j hv⟩
  have gateVal_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → ∀ i : Fin E.size, E.gateVal U i = true → E.gateVal V i = true := by
    intro E U V hUV i h
    exact gateValFuel_mono E hUV E.size i h
  have eval_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → E.eval U = true → E.eval V = true := by
    intro E U V hUV h
    rw [eval_def] at h ⊢
    rw [decide_eq_true_eq] at h ⊢
    rcases h with h1 | h2
    · rcases h1 with ⟨v, hv, hu⟩
      exact Or.inl ⟨v, hv, hUV hu⟩
    · rcases h2 with ⟨j, hj, hv⟩
      exact Or.inr ⟨j, hj, gateVal_mono E hUV j hv⟩

  let stripCircuit (E : PEqualNP.AndCount.AndCountCircuit 26) : PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨E.size,
     fun i => Finset.univ.filter (fun v =>
       (v ∈ E.leftVars i ∨ ∃ j ∈ E.leftGates i, j < i ∧ E.gateVal {v} j = true) ∧ E.gateVal {v} i = false),
     E.leftGates,
     fun i => Finset.univ.filter (fun v =>
       (v ∈ E.rightVars i ∨ ∃ j ∈ E.rightGates i, j < i ∧ E.gateVal {v} j = true) ∧ E.gateVal {v} i = false),
     E.rightGates,
     Finset.univ.filter (fun v => v ∈ E.outVars ∨ ∃ j ∈ E.outGates, E.gateVal {v} j = true),
     E.outGates⟩
  have strip_wf : ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed → (stripCircuit E).WellFormed :=
    fun _ hw => hw
  have strip_disj : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (i : Fin (stripCircuit E).size),
      Disjoint ((stripCircuit E).leftVars i) ((stripCircuit E).rightVars i) := by
    intro E i
    rw [Finset.disjoint_left]
    intro v hL hR
    have hL' := (Finset.mem_filter.mp hL).2
    have hR' := (Finset.mem_filter.mp hR).2
    have hvL : PEqualNP.AndCount.AndCountCircuit.sideTrue {v} (E.leftVars i) (E.leftGates i) i (E.gateVal {v}) = true := by
      rw [sideTrue_def]
      rw [decide_eq_true_eq]
      rcases hL'.1 with h1 | h2
      · exact Or.inl ⟨v, h1, Finset.mem_singleton_self v⟩
      · exact Or.inr h2
    have hvR : PEqualNP.AndCount.AndCountCircuit.sideTrue {v} (E.rightVars i) (E.rightGates i) i (E.gateVal {v}) = true := by
      rw [sideTrue_def]
      rw [decide_eq_true_eq]
      rcases hR'.1 with h1 | h2
      · exact Or.inl ⟨v, h1, Finset.mem_singleton_self v⟩
      · exact Or.inr h2
    have htrue : E.gateVal {v} i = true := by
      rw [gateVal_eq E {v} i, hvL, hvR]; rfl
    rw [hL'.2] at htrue
    cases htrue
  have strip_gateVal_le : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (k : ℕ) (i : Fin E.size), i.val < k → (stripCircuit E).gateVal U i = true → E.gateVal U i = true := by
    intro E U k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hval
      rw [gateVal_eq (stripCircuit E) U i, Bool.and_eq_true] at hval
      rw [gateVal_eq E U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        rw [sideTrue_def] at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with h1 | h2
        · rcases h1 with ⟨v, hv, hvU⟩
          have hv' := (Finset.mem_filter.mp hv).2.1
          rcases hv' with hvB | hjs
          · exact Or.inl ⟨v, hvB, hvU⟩
          · rcases hjs with ⟨j, hjF, hji, hvs⟩
            exact Or.inr ⟨j, hjF, hji, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
        · rcases h2 with ⟨j, hjF, hji, hjv⟩
          exact Or.inr ⟨j, hjF, hji, ih j (by have := hji; change j.val < i.val at this; omega) hjv⟩
      · have hR := hval.2
        rw [sideTrue_def] at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with h1 | h2
        · rcases h1 with ⟨v, hv, hvU⟩
          have hv' := (Finset.mem_filter.mp hv).2.1
          rcases hv' with hvB | hjs
          · exact Or.inl ⟨v, hvB, hvU⟩
          · rcases hjs with ⟨j, hjF, hji, hvs⟩
            exact Or.inr ⟨j, hjF, hji, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
        · rcases h2 with ⟨j, hjF, hji, hjv⟩
          exact Or.inr ⟨j, hjF, hji, ih j (by have := hji; change j.val < i.val at this; omega) hjv⟩
  have strip_gateVal_ge : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (k : ℕ) (i : Fin E.size), i.val < k → E.gateVal U i = true →
      (∃ v ∈ U, E.gateVal {v} i = true) ∨ (stripCircuit E).gateVal U i = true := by
    intro E U k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hval
      by_cases hsing : ∃ v ∈ U, E.gateVal {v} i = true
      · exact Or.inl hsing
      · right
        have hno : ∀ v ∈ U, E.gateVal {v} i = false := fun v hvU =>
          Bool.eq_false_iff.mpr (fun hv => hsing ⟨v, hvU, hv⟩)
        rw [gateVal_eq E U i, Bool.and_eq_true] at hval
        rw [gateVal_eq (stripCircuit E) U i, Bool.and_eq_true]
        constructor
        · have hL := hval.1
          rw [sideTrue_def] at hL ⊢
          rw [decide_eq_true_eq] at hL ⊢
          rcases hL with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvB, hno v hvU⟩, hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hjv⟩
            rcases ih j (by have := hji; change j.val < i.val at this; omega) hjv with h3 | hj'
            · rcases h3 with ⟨v, hvU, hvs⟩
              exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hj'⟩
        · have hR := hval.2
          rw [sideTrue_def] at hR ⊢
          rw [decide_eq_true_eq] at hR ⊢
          rcases hR with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvB, hno v hvU⟩, hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hjv⟩
            rcases ih j (by have := hji; change j.val < i.val at this; omega) hjv with h3 | hj'
            · rcases h3 with ⟨v, hvU, hvs⟩
              exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hj'⟩
  have strip_eval_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      (stripCircuit E).eval U = E.eval U := by
    intro E U
    rw [eval_def, eval_def]
    refine decide_eq_decide.mpr ?_
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        rcases (Finset.mem_filter.mp hvO).2 with hvC | hjs
        · exact Or.inl ⟨v, hvC, hvU⟩
        · rcases hjs with ⟨j, hjO, hvs⟩
          exact Or.inr ⟨j, hjO, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        exact Or.inr ⟨j, hjO, strip_gateVal_le E U E.size j j.isLt hjv⟩
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvO⟩, hvU⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        rcases strip_gateVal_ge E U E.size j j.isLt hjv with h3 | hj'
        · rcases h3 with ⟨v, hvU, hvs⟩
          exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjO, hvs⟩⟩, hvU⟩
        · exact Or.inr ⟨j, hjO, hj'⟩
  have strip_gateVal_singleton : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (i : Fin (stripCircuit E).size) (v : Fin 26), (stripCircuit E).gateVal {v} i = false := by
    intro E i v
    induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin E.size → Fin E.size → Prop)).induction with
    | h i ih =>
      rw [Bool.eq_false_iff]
      intro htrue
      rw [gateVal_eq (stripCircuit E) {v} i, Bool.and_eq_true] at htrue
      have getL : v ∈ (stripCircuit E).leftVars i := by
        have hL := htrue.1
        rw [sideTrue_def] at hL
        rw [decide_eq_true_eq] at hL
        rcases hL with h1 | h2
        · rcases h1 with ⟨u, hu, huv⟩
          rw [Finset.mem_singleton.mp huv] at hu
          exact hu
        · rcases h2 with ⟨j, _, hji, hjv⟩
          rw [ih j hji] at hjv; cases hjv
      have getR : v ∈ (stripCircuit E).rightVars i := by
        have hR := htrue.2
        rw [sideTrue_def] at hR
        rw [decide_eq_true_eq] at hR
        rcases hR with h1 | h2
        · rcases h1 with ⟨u, hu, huv⟩
          rw [Finset.mem_singleton.mp huv] at hu
          exact hu
        · rcases h2 with ⟨j, _, hji, hjv⟩
          rw [ih j hji] at hjv; cases hjv
      exact Finset.disjoint_left.mp (strip_disj E i) getL getR
  have strip_exists : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      ∃ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.size = E.size ∧ D.WellFormed ∧
        (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) ∧
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) ∧
        (∀ U, D.eval U = E.eval U) :=
    fun E hw => ⟨stripCircuit E, rfl, strip_wf E hw, strip_disj E, strip_gateVal_singleton E, strip_eval_eq E⟩

  let signal {k : ℕ} (U A : Finset (Fin 26)) (P : Finset (Fin k)) (val : Fin k → Bool) : Prop :=
    (∃ v ∈ A, v ∈ U) ∨ ∃ j ∈ P, val j = true
  have gate_spec : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      ∀ (U : Finset (Fin 26)) (i : Fin E.size),
        E.gateVal U i = true ↔
          signal U (E.leftVars i) (E.leftGates i) (E.gateVal U) ∧
          signal U (E.rightVars i) (E.rightGates i) (E.gateVal U) := by
    intro E hw U i
    rw [gateVal_eq, Bool.and_eq_true]
    rw [sideTrue_def, sideTrue_def]; simp only [signal, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rcases h.1 with h1 | h2
        · exact Or.inl h1
        · rcases h2 with ⟨j, hj, _, hv⟩; exact Or.inr ⟨j, hj, hv⟩
      · rcases h.2 with h1 | h2
        · exact Or.inl h1
        · rcases h2 with ⟨j, hj, _, hv⟩; exact Or.inr ⟨j, hj, hv⟩
    · intro h
      refine ⟨?_, ?_⟩
      · rcases h.1 with h1 | h2
        · exact Or.inl h1
        · rcases h2 with ⟨j, hj, hv⟩; exact Or.inr ⟨j, hj, (hw i).1 j hj, hv⟩
      · rcases h.2 with h1 | h2
        · exact Or.inl h1
        · rcases h2 with ⟨j, hj, hv⟩; exact Or.inr ⟨j, hj, (hw i).2 j hj, hv⟩
  let expandVars {m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin 26)) (P : Finset (Fin (m + 1))) : Finset (Fin 26) :=
    A ∪ if i ∈ P then B else ∅
  let expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1))) : Finset (Fin m) :=
    Finset.univ.filter (fun k => i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F)
  have signal_expand : ∀ {m : ℕ} (i : Fin (m + 1)) (U B A : Finset (Fin 26))
      (F P : Finset (Fin (m + 1))) (val : Fin (m + 1) → Bool) (val' : Fin m → Bool),
      (∀ j ∈ F, j < i) → (val i = true ↔ signal U B F val) →
      (∀ k ∈ expandRefs i F P, val' k = val (i.succAbove k)) →
      (signal U (expandVars i B A P) (expandRefs i F P) val' ↔ signal U A P val) := by
    intro m i U B A F P val val' before expand agree
    have memV : ∀ v : Fin 26, v ∈ expandVars i B A P ↔ v ∈ A ∨ i ∈ P ∧ v ∈ B := by
      intro v; by_cases h : i ∈ P <;> simp [expandVars, h]
    have memR : ∀ k : Fin m, k ∈ expandRefs i F P ↔ i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := by
      intro k; simp [expandRefs]
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hv, hu⟩
        rcases (memV v).mp hv with hvA | hB
        · exact Or.inl ⟨v, hvA, hu⟩
        · exact Or.inr ⟨i, hB.1, expand.mpr (Or.inl ⟨v, hB.2, hu⟩)⟩
      · rcases h2 with ⟨k, hk, ht⟩
        rw [agree k hk] at ht
        rcases (memR k).mp hk with hP | hF
        · exact Or.inr ⟨_, hP, ht⟩
        · exact Or.inr ⟨i, hF.1, expand.mpr (Or.inr ⟨_, hF.2, ht⟩)⟩
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hv, hu⟩
        exact Or.inl ⟨v, (memV v).mpr (Or.inl hv), hu⟩
      · rcases h2 with ⟨j, hj, ht⟩
        by_cases hji : j = i
        · subst j
          rcases expand.mp ht with h3 | h4
          · rcases h3 with ⟨v, hv, hu⟩
            exact Or.inl ⟨v, (memV v).mpr (Or.inr ⟨hj, hv⟩), hu⟩
          · rcases h4 with ⟨l, hl, ht'⟩
            obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (ne_of_lt (before l hl))
            have hk := (memR k).mpr (Or.inr ⟨hj, hl⟩)
            exact Or.inr ⟨k, hk, (agree k hk).trans ht'⟩
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
          have hk := (memR k).mpr (Or.inl hj)
          exact Or.inr ⟨k, hk, (agree k hk).trans ht⟩
  let Expandable (E : PEqualNP.AndCount.AndCountCircuit 26) (Dom : Set (Finset (Fin 26))) (i : Fin E.size) : Prop :=
    ∃ B : Finset (Fin 26), ∃ F : Finset (Fin E.size), (∀ j ∈ F, j < i) ∧
      ∀ U ∈ Dom, E.gateVal U i = true ↔ signal U B F (E.gateVal U)
  have remove_one : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (Dom : Set (Finset (Fin 26))) (i : Fin E.size),
      E.WellFormed → Expandable E Dom i →
      ∃ E' : PEqualNP.AndCount.AndCountCircuit 26, ∃ f : Fin E'.size → Fin E.size,
        E'.WellFormed ∧ E'.size + 1 = E.size ∧ StrictMono f ∧
        (∀ j, j ≠ i ↔ ∃ k, f k = j) ∧
        ∀ U ∈ Dom, E'.eval U = E.eval U ∧ ∀ j, E'.gateVal U j = E.gateVal U (f j) := by
    intro E Dom i hw hexp
    obtain ⟨B, F, before, same⟩ := hexp
    rcases E with ⟨s, lv, lg, rv, rg, ov, og⟩
    cases s with
    | zero => exact Fin.elim0 i
    | succ m =>
      let E0 : PEqualNP.AndCount.AndCountCircuit 26 := ⟨m + 1, lv, lg, rv, rg, ov, og⟩
      let E' : PEqualNP.AndCount.AndCountCircuit 26 :=
        ⟨m, fun j => expandVars i B (lv (i.succAbove j)) (lg (i.succAbove j)),
            fun j => expandRefs i F (lg (i.succAbove j)),
            fun j => expandVars i B (rv (i.succAbove j)) (rg (i.succAbove j)),
            fun j => expandRefs i F (rg (i.succAbove j)),
            expandVars i B ov og, expandRefs i F og⟩
      have lt_ref : ∀ (j k : Fin m) (P : Finset (Fin (m + 1))),
          (∀ l ∈ P, l < i.succAbove j) → k ∈ expandRefs i F P → k < j := by
        intro j k P old hk
        apply Fin.succAbove_lt_succAbove_iff.mp
        have hk' : i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := (Finset.mem_filter.mp hk).2
        rcases hk' with hp | hif
        · exact old _ hp
        · exact (before _ hif.2).trans (old i hif.1)
      have hw' : E'.WellFormed := fun j =>
        ⟨fun k hk => lt_ref j k _ (hw (i.succAbove j)).1 hk,
         fun k hk => lt_ref j k _ (hw (i.succAbove j)).2 hk⟩
      refine ⟨E', i.succAbove, hw', rfl, fun j k hjk => Fin.succAbove_lt_succAbove_iff.mpr hjk, ?_, ?_⟩
      · intro j
        refine ⟨Fin.exists_succAbove_eq, ?_⟩
        intro hex; rcases hex with ⟨k, rfl⟩; exact Fin.succAbove_ne i k
      · intro U hU
        have values : ∀ j : Fin m, E'.gateVal U j = E0.gateVal U (i.succAbove j) := by
          intro j
          induction j using (wellFounded_lt : WellFounded ((· < ·) : Fin m → Fin m → Prop)).induction with
          | h j ih =>
            rw [Bool.eq_iff_iff, gate_spec E' hw', gate_spec E0 hw]
            exact and_congr
              (signal_expand i U B _ F _ _ _ before (same U hU)
                (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).1 hk)))
              (signal_expand i U B _ F _ _ _ before (same U hU)
                (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).2 hk)))
        refine ⟨?_, values⟩
        rw [eval_def, eval_def]
        rw [decide_eq_decide]
        exact signal_expand i U B ov F og _ _ before (same U hU) (fun k _ => values k)
  have remove_many : ∀ (Dom : Set (Finset (Fin 26))) (k : ℕ) (E : PEqualNP.AndCount.AndCountCircuit 26),
      E.WellFormed → ∀ (S : Finset (Fin E.size)), S.card = k → (∀ i ∈ S, Expandable E Dom i) →
      ∃ E' : PEqualNP.AndCount.AndCountCircuit 26, E'.WellFormed ∧ E'.size + S.card ≤ E.size ∧
        ∀ U ∈ Dom, E'.eval U = E.eval U := by
    intro Dom k
    induction k with
    | zero =>
      intro E hw S hS _
      exact ⟨E, hw, by simp [hS], fun _ _ => rfl⟩
    | succ k ih =>
      intro E hw S hS expands
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      let i := S.max' hne
      have hi : i ∈ S := S.max'_mem hne
      obtain ⟨E', f, hw', hsize, hmono, hran, hsem⟩ := remove_one E Dom i hw (expands i hi)
      let S' : Finset (Fin E'.size) := Finset.univ.filter (fun j => f j ∈ S)
      have lift_mem : ∀ j : Fin E'.size, j ∈ S' ↔ f j ∈ S := fun j => by simp [S']
      have himg : S'.image f = S.erase i := by
        ext r
        simp only [Finset.mem_image, Finset.mem_erase]
        constructor
        · intro h; rcases h with ⟨j, hj, rfl⟩
          exact ⟨(hran _).mpr ⟨j, rfl⟩, (lift_mem j).mp hj⟩
        · intro h
          obtain ⟨j, rfl⟩ := (hran r).mp h.1
          exact ⟨j, (lift_mem j).mpr h.2, rfl⟩
      have hcard : S'.card = k := by
        have hc := Finset.card_image_of_injective S' hmono.injective
        rw [himg, Finset.card_erase_of_mem hi] at hc
        omega
      have hexp' : ∀ j ∈ S', Expandable E' Dom j := by
        intro j hj
        have hjS := (lift_mem j).mp hj
        obtain ⟨B, F, before, same⟩ := expands (f j) hjS
        let F' : Finset (Fin E'.size) := Finset.univ.filter (fun l => f l ∈ F)
        have hF' : ∀ l : Fin E'.size, l ∈ F' ↔ f l ∈ F := fun l => by simp [F']
        have hnotrem : i ∉ F := fun h =>
          (not_lt_of_ge (Finset.le_max' S (f j) hjS)) (before i h)
        refine ⟨B, F', ?_, ?_⟩
        · intro l hl
          exact hmono.lt_iff_lt.mp (before _ ((hF' l).mp hl))
        · intro U hU
          have values := (hsem U hU).2
          rw [values j, same U hU]
          constructor
          · intro h
            rcases h with h1 | h2
            · exact Or.inl h1
            · rcases h2 with ⟨l, hl, ht⟩
              have hli : l ≠ i := fun he => hnotrem (he ▸ hl)
              obtain ⟨q, rfl⟩ := (hran l).mp hli
              exact Or.inr ⟨q, (hF' q).mpr hl, (values q).trans ht⟩
          · intro h
            rcases h with h1 | h2
            · exact Or.inl h1
            · rcases h2 with ⟨l, hl, ht⟩
              exact Or.inr ⟨f l, (hF' l).mp hl, (values l).symm.trans ht⟩
      obtain ⟨E'', hw'', hbd, hout⟩ := ih E' hw' S' hcard hexp'
      exact ⟨E'', hw'', by omega, fun U hU => (hout U hU).trans (hsem U hU).1⟩
  have elim_vertices : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      ∀ (V0 : Finset (Fin 26)),
        let T := Finset.univ.filter (fun i : Fin E.size => ∃ v ∈ V0, v ∈ E.leftVars i ∨ v ∈ E.rightVars i)
        ∃ E' : PEqualNP.AndCount.AndCountCircuit 26, E'.WellFormed ∧ E'.size + T.card ≤ E.size ∧
          ∀ U : Finset (Fin 26), V0 ⊆ U → E'.eval U = E.eval U := by
    intro E hw V0 T
    let Dom : Set (Finset (Fin 26)) := {U : Finset (Fin 26) | V0 ⊆ U}
    apply remove_many Dom T.card E hw T rfl
    intro i hi
    obtain ⟨v, hv0, hvlr⟩ := (Finset.mem_filter.mp hi).2
    rcases hvlr with hvL | hvR
    · refine ⟨E.rightVars i, E.rightGates i, (hw i).2, ?_⟩
      intro U hU
      rw [gate_spec E hw U i]
      have hLtrue : signal U (E.leftVars i) (E.leftGates i) (E.gateVal U) := Or.inl ⟨v, hvL, hU hv0⟩
      exact ⟨fun h => h.2, fun h => ⟨hLtrue, h⟩⟩
    · refine ⟨E.leftVars i, E.leftGates i, (hw i).1, ?_⟩
      intro U hU
      rw [gate_spec E hw U i]
      have hRtrue : signal U (E.rightVars i) (E.rightGates i) (E.gateVal U) := Or.inl ⟨v, hvR, hU hv0⟩
      exact ⟨fun h => h.1, fun h => ⟨h, hRtrue⟩⟩

  let Separates (E : PEqualNP.AndCount.AndCountCircuit 26) (Rows : Finset (Finset (Fin 26))) : Prop :=
    ∀ I ∈ Rows, E.eval I = false ∧ ∀ w : Fin 26, w ∉ I → E.eval (insert w I) = true
  let Free (E : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin E.size) :=
    Finset.univ.filter (fun i => v ∉ E.leftVars i ∧ v ∉ E.rightVars i)
  let sideL (E : PEqualNP.AndCount.AndCountCircuit 26) (I : Finset (Fin 26)) (i : Fin E.size) : Bool :=
    PEqualNP.AndCount.AndCountCircuit.sideTrue I (E.leftVars i) (E.leftGates i) i (E.gateVal I)
  let sideR (E : PEqualNP.AndCount.AndCountCircuit 26) (I : Finset (Fin 26)) (i : Fin E.size) : Bool :=
    PEqualNP.AndCount.AndCountCircuit.sideTrue I (E.rightVars i) (E.rightGates i) i (E.gateVal I)
  let litSet (E : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin E.size × Bool) :=
    Finset.univ.filter (fun p => if p.2 then v ∈ E.rightVars p.1 else v ∈ E.leftVars p.1)
  have litSet_touch_card : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26),
      (∀ i, Disjoint (E.leftVars i) (E.rightVars i)) →
      ∀ v : Fin 26,
        (litSet E v).card = (Finset.univ.filter (fun i : Fin E.size => v ∈ E.leftVars i ∨ v ∈ E.rightVars i)).card ∧
        (litSet E v).card + (Free E v).card = E.size := by
    intro E hdisj v
    have hinj : Set.InjOn Prod.fst (litSet E v : Set (Fin E.size × Bool)) := by
      intro p1 hp1 p2 hp2 heq
      rcases p1 with ⟨g1, b1⟩; rcases p2 with ⟨g2, b2⟩
      dsimp at heq; subst heq
      have h1 := (Finset.mem_filter.mp hp1).2
      have h2 := (Finset.mem_filter.mp hp2).2
      cases b1 <;> cases b2
      · rfl
      · exact (Finset.disjoint_left.mp (hdisj g1) h1 h2).elim
      · exact (Finset.disjoint_left.mp (hdisj g1) h2 h1).elim
      · rfl
    have himg : (litSet E v).image Prod.fst =
        Finset.univ.filter (fun i : Fin E.size => v ∈ E.leftVars i ∨ v ∈ E.rightVars i) := by
      ext g
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, litSet]
      constructor
      · intro h; rcases h with ⟨⟨g', b⟩, hb, rfl⟩
        cases b
        · exact Or.inl hb
        · exact Or.inr hb
      · intro h; rcases h with hL | hR
        · exact ⟨(g, false), hL, rfl⟩
        · exact ⟨(g, true), hR, rfl⟩
    have hc1 : (litSet E v).card =
        (Finset.univ.filter (fun i : Fin E.size => v ∈ E.leftVars i ∨ v ∈ E.rightVars i)).card := by
      rw [← himg, Finset.card_image_of_injOn hinj]
    have hcomp : Finset.univ.filter (fun i : Fin E.size => v ∈ E.leftVars i ∨ v ∈ E.rightVars i) =
        Finset.univ \ Free E v := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Free]
      tauto
    have htot := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Free E v))
    simp only [Finset.card_univ, Fintype.card_fin] at htot
    rw [← hcomp, ← hc1] at htot
    exact ⟨hc1, htot⟩
  have mergeInput : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (I J U : Finset (Fin 26)) (v : Fin 26),
      v ∈ I → v ∈ J → U ⊆ I ∪ J → (∀ i ∈ Free E v, sideL E I i = sideL E J i) →
      E.eval U = true → E.eval I = true ∨ E.eval J = true := by
    intro E I J U v hi hj hU hs hev
    have unionSide : ∀ (B : Finset (Fin 26)) (F : Finset (Fin E.size)) (i : Fin E.size),
        (∀ j < i, E.gateVal U j = true → E.gateVal I j = true ∨ E.gateVal J j = true) →
        PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i (E.gateVal U) = true →
        PEqualNP.AndCount.AndCountCircuit.sideTrue I B F i (E.gateVal I) = true ∨
        PEqualNP.AndCount.AndCountCircuit.sideTrue J B F i (E.gateVal J) = true := by
      intro B F i ih hst
      rw [sideTrue_def] at hst; rw [sideTrue_def, sideTrue_def]; simp only [decide_eq_true_eq] at hst ⊢
      rcases hst with h1 | h2
      · rcases h1 with ⟨w, hw, hu⟩
        rcases Finset.mem_union.mp (hU hu) with hI | hJ
        · exact Or.inl (Or.inl ⟨w, hw, hI⟩)
        · exact Or.inr (Or.inl ⟨w, hw, hJ⟩)
      · rcases h2 with ⟨j, hjF, hji, ht⟩
        rcases ih j hji ht with hI | hJ
        · exact Or.inl (Or.inr ⟨j, hjF, hji, hI⟩)
        · exact Or.inr (Or.inr ⟨j, hjF, hji, hJ⟩)
    have gate : ∀ i : Fin E.size, E.gateVal U i = true → E.gateVal I i = true ∨ E.gateVal J i = true := by
      intro i
      induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin E.size → Fin E.size → Prop)).induction with
      | h i ih =>
        intro ht
        rw [gateVal_eq, Bool.and_eq_true] at ht
        rw [gateVal_eq E I, gateVal_eq E J]
        change (sideL E I i && sideR E I i) = true ∨ (sideL E J i && sideR E J i) = true
        have hl : sideL E I i = true ∨ sideL E J i = true := unionSide _ _ i ih ht.1
        have hr : sideR E I i = true ∨ sideR E J i = true := unionSide _ _ i ih ht.2
        simp only [Bool.and_eq_true]
        by_cases h1 : v ∈ E.leftVars i
        · have a : sideL E I i = true := decide_eq_true (Or.inl ⟨v, h1, hi⟩)
          have b : sideL E J i = true := decide_eq_true (Or.inl ⟨v, h1, hj⟩)
          rcases hr with hr | hr
          · exact Or.inl ⟨a, hr⟩
          · exact Or.inr ⟨b, hr⟩
        by_cases h2 : v ∈ E.rightVars i
        · have a : sideR E I i = true := decide_eq_true (Or.inl ⟨v, h2, hi⟩)
          have b : sideR E J i = true := decide_eq_true (Or.inl ⟨v, h2, hj⟩)
          rcases hl with hl | hl
          · exact Or.inl ⟨hl, a⟩
          · exact Or.inr ⟨hl, b⟩
        have hh := hs i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
        have hlj : sideL E J i = true := by
          rcases hl with hl | hl
          · exact hh.symm.trans hl
          · exact hl
        have hli : sideL E I i = true := hh.trans hlj
        rcases hr with hr | hr
        · exact Or.inl ⟨hli, hr⟩
        · exact Or.inr ⟨hlj, hr⟩
    rw [eval_def] at hev; rw [eval_def, eval_def]; simp only [decide_eq_true_eq] at hev ⊢
    rcases hev with h1 | h2
    · rcases h1 with ⟨w, hw, hwu⟩
      rcases Finset.mem_union.mp (hU hwu) with hI | hJ
      · exact Or.inl (Or.inl ⟨w, hw, hI⟩)
      · exact Or.inr (Or.inl ⟨w, hw, hJ⟩)
    · rcases h2 with ⟨i, hi', hgt⟩
      rcases gate i hgt with hI | hJ
      · exact Or.inl (Or.inr ⟨i, hi', hI⟩)
      · exact Or.inr (Or.inr ⟨i, hi', hJ⟩)
  have free_bound_gen : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (Rows : Finset (Finset (Fin 26))) (v : Fin 26),
      Separates E Rows →
      (∀ I ∈ Rows, ∀ J ∈ Rows, I ≠ J → ∃ w ∈ I, w ∉ J) →
      (Rows.filter (fun I => v ∈ I)).card ≤ 2 ^ (Free E v).card := by
    intro E Rows v hsep hincomp
    let Rv := Rows.filter (fun I => v ∈ I)
    let code (x : ↥Rv) (i : ↥(Free E v)) : Bool := sideL E x.1 i.1
    have hinj : Function.Injective code := by
      intro a b hab
      by_contra hne
      have hne1 : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
      have haR : a.1 ∈ Rows := (Finset.mem_filter.mp a.2).1
      have hbR : b.1 ∈ Rows := (Finset.mem_filter.mp b.2).1
      have hav : v ∈ a.1 := (Finset.mem_filter.mp a.2).2
      have hbv : v ∈ b.1 := (Finset.mem_filter.mp b.2).2
      obtain ⟨w, hwa, hwb⟩ := hincomp a.1 haR b.1 hbR hne1
      have he := mergeInput E a.1 b.1 (insert w b.1) v hav hbv
        (Finset.insert_subset (Finset.mem_union_left b.1 hwa) Finset.subset_union_right)
        (fun i hi => congrFun hab ⟨i, hi⟩) ((hsep b.1 hbR).2 w hwb)
      rw [(hsep a.1 haR).1, (hsep b.1 hbR).1] at he
      simp at he
    have hc := Fintype.card_le_of_injective code hinj
    simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool] using hc
  have mis_cover_gen : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (Rows : Finset (Finset (Fin 26))) (Active : Finset (Fin 26)),
      Separates E Rows → (∀ u ∈ Active, ∃ J ∈ Rows, u ∈ J) →
      ∀ I ∈ Rows, ∃ f : Fin E.size → Option Bool,
        (∀ v ∈ I, ∀ l ∈ litSet E v, f l.1 ≠ some l.2) ∧
        (∀ w ∈ Active, w ∉ I → ∃ l ∈ litSet E w, f l.1 = some l.2) := by
    intro E Rows Active hsep hact I hI
    let f : Fin E.size → Option Bool := fun i =>
      if sideL E I i = false then some false
      else if sideR E I i = false then some true
      else none
    refine ⟨f, ?_, ?_⟩
    · intro v hv l hl
      rcases l with ⟨g, b⟩
      have hlb := (Finset.mem_filter.mp hl).2
      cases b
      · have hsL : sideL E I g = true := decide_eq_true (Or.inl ⟨v, hlb, hv⟩)
        simp only [f, hsL, Bool.true_eq_false, ↓reduceIte]
        split_ifs <;> simp
      · have hsR : sideR E I g = true := decide_eq_true (Or.inl ⟨v, hlb, hv⟩)
        simp only [f, hsR, Bool.true_eq_false, ↓reduceIte]
        split_ifs <;> simp
    · intro w hwA hwI
      have hev : E.eval (insert w I) = true := (hsep I hI).2 w hwI
      have hfl : E.eval I = false := (hsep I hI).1
      let S : Finset (Fin E.size) :=
        Finset.univ.filter (fun i => E.gateVal I i = false ∧ E.gateVal (insert w I) i = true)
      have hSne : S.Nonempty := by
        rw [eval_def] at hev
        rw [decide_eq_true_eq] at hev
        rcases hev with h1 | h2
        · rcases h1 with ⟨u, huO, huIn⟩
          rcases Finset.mem_insert.mp huIn with rfl | huI
          · obtain ⟨J, hJR, hwJ⟩ := hact u hwA
            have het : E.eval J = true := decide_eq_true (Or.inl ⟨u, huO, hwJ⟩)
            rw [(hsep J hJR).1] at het; cases het
          · have het : E.eval I = true := decide_eq_true (Or.inl ⟨u, huO, huI⟩)
            rw [hfl] at het; cases het
        · rcases h2 with ⟨i, hiO, hit⟩
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hit⟩⟩
          rw [Bool.eq_false_iff]
          intro hti
          have het : E.eval I = true := decide_eq_true (Or.inr ⟨i, hiO, hti⟩)
          rw [hfl] at het; cases het
      let g := S.min' hSne
      have hgS : g ∈ S := S.min'_mem hSne
      have hgF : E.gateVal I g = false := (Finset.mem_filter.mp hgS).2.1
      have hgT : E.gateVal (insert w I) g = true := (Finset.mem_filter.mp hgS).2.2
      have hmin : ∀ j : Fin E.size, j < g → E.gateVal (insert w I) j = true → E.gateVal I j = true := by
        intro j hj hjt
        by_contra hnf
        have hjf : E.gateVal I j = false := Bool.eq_false_iff.mpr hnf
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjf, hjt⟩
        exact (not_le_of_gt hj) (S.min'_le j hjS)
      rw [gateVal_eq E (insert w I) g, Bool.and_eq_true] at hgT
      rw [gateVal_eq E I g] at hgF
      change (sideL E I g && sideR E I g) = false at hgF
      change sideL E (insert w I) g = true ∧ sideR E (insert w I) g = true at hgT
      by_cases hL : sideL E I g = false
      · refine ⟨(g, false), ?_, by simp [f, hL]⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hLT : sideL E (insert w I) g = true := hgT.1
        dsimp only [sideL] at hLT hL; rw [sideTrue_def] at hLT hL
        rw [decide_eq_true_eq] at hLT
        rcases hLT with h1 | h2
        · rcases h1 with ⟨v, hv, hvI⟩
          rcases Finset.mem_insert.mp hvI with rfl | hvi
          · exact hv
          · have ht : decide ((∃ u ∈ E.leftVars g, u ∈ I) ∨
                ∃ j ∈ E.leftGates g, j < g ∧ E.gateVal I j = true) = true :=
              decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
            rw [hL] at ht; cases ht
        · rcases h2 with ⟨j, hj, hji, hjt⟩
          have hjiT := hmin j hji hjt
          have ht : decide ((∃ u ∈ E.leftVars g, u ∈ I) ∨
              ∃ j ∈ E.leftGates g, j < g ∧ E.gateVal I j = true) = true :=
            decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
          rw [hL] at ht; cases ht
      · have hLt : sideL E I g = true := by
          cases h' : sideL E I g
          · exact (hL h').elim
          · rfl
        have hR : sideR E I g = false := by simp [hLt] at hgF; exact hgF
        refine ⟨(g, true), ?_, by simp [f, hLt, hR]⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hRT : sideR E (insert w I) g = true := hgT.2
        dsimp only [sideR] at hRT hR; rw [sideTrue_def] at hRT hR
        rw [decide_eq_true_eq] at hRT
        rcases hRT with h1 | h2
        · rcases h1 with ⟨v, hv, hvI⟩
          rcases Finset.mem_insert.mp hvI with rfl | hvi
          · exact hv
          · have ht : decide ((∃ u ∈ E.rightVars g, u ∈ I) ∨
                ∃ j ∈ E.rightGates g, j < g ∧ E.gateVal I j = true) = true :=
              decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
            rw [hR] at ht; cases ht
        · rcases h2 with ⟨j, hj, hji, hjt⟩
          have hjiT := hmin j hji hjt
          have ht : decide ((∃ u ∈ E.rightVars g, u ∈ I) ∨
              ∃ j ∈ E.rightGates g, j < g ∧ E.gateVal I j = true) = true :=
            decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
          rw [hR] at ht; cases ht
  have card_le_size_of_deg_le_one : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (Rows : Finset (Finset (Fin 26))) (Z : Finset (Fin 26)),
      Separates E Rows →
      (∀ z ∈ Z, ∃ I ∈ Rows, z ∈ I) →
      (∀ z ∈ Z, ∃ I ∈ Rows, z ∉ I) →
      (∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ≠ z2 → ∃ I ∈ Rows, z1 ∈ I ∧ z2 ∉ I) →
      (∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ≠ z2 → ∃ I ∈ Rows, z1 ∉ I ∧ z2 ∉ I) →
      (∀ z ∈ Z, (litSet E z).card ≤ 1) →
      Z.card ≤ E.size := by
    intro E Rows Z hsep hmem hout hsame hopp hdeg1
    have hexLit : ∀ z : ↥Z, ∃ l : Fin E.size × Bool, l ∈ litSet E z.1 := by
      intro z
      obtain ⟨I, hIR, hzI⟩ := hout z.1 z.2
      obtain ⟨f, _, hfhit⟩ := mis_cover_gen E Rows Z hsep hmem I hIR
      obtain ⟨l, hl, _⟩ := hfhit z.1 z.2 hzI
      exact ⟨l, hl⟩
    choose pickL hpickL using hexLit
    have huniq : ∀ (z : ↥Z) (l : Fin E.size × Bool), l ∈ litSet E z.1 → l = pickL z := by
      intro z l hl
      exact Finset.card_le_one.mp (hdeg1 z.1 z.2) l hl (pickL z) (hpickL z)
    let phi (z : ↥Z) : Fin E.size := (pickL z).1
    have hinj : Function.Injective phi := by
      intro z1 z2 hphi
      by_contra hne
      have hneV : z1.1 ≠ z2.1 := fun h => hne (Subtype.ext h)
      by_cases hb : (pickL z1).2 = (pickL z2).2
      · have hleq : pickL z1 = pickL z2 := Prod.ext hphi hb
        obtain ⟨I, hIR, hz1I, hz2nI⟩ := hsame z1.1 z1.2 z2.1 z2.2 hneV
        obtain ⟨f, hfav, hfhit⟩ := mis_cover_gen E Rows Z hsep hmem I hIR
        obtain ⟨l, hl2, hfl⟩ := hfhit z2.1 z2.2 hz2nI
        have hl_eq : l = pickL z1 := (huniq z2 l hl2).trans hleq.symm
        exact hfav z1.1 hz1I (pickL z1) (hpickL z1) (hl_eq ▸ hfl)
      · obtain ⟨I, hIR, hz1nI, hz2nI⟩ := hopp z1.1 z1.2 z2.1 z2.2 hneV
        obtain ⟨f, _, hfhit⟩ := mis_cover_gen E Rows Z hsep hmem I hIR
        obtain ⟨l1, hl1, hfl1⟩ := hfhit z1.1 z1.2 hz1nI
        obtain ⟨l2, hl2, hfl2⟩ := hfhit z2.1 z2.2 hz2nI
        rw [huniq z1 l1 hl1] at hfl1
        rw [huniq z2 l2 hl2] at hfl2
        have h1 : f (pickL z2).1 = some (pickL z1).2 := by dsimp only [phi] at hphi; rw [← hphi]; exact hfl1
        have h2 : some (pickL z1).2 = some (pickL z2).2 := h1.symm.trans hfl2
        exact hb (Option.some.inj h2)
    have hc := Fintype.card_le_of_injective phi hinj
    simpa only [Fintype.card_coe, Fintype.card_fin] using hc

  let mapCirc (σ : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26) :
      PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨E.size,
     fun i => (E.leftVars i).map σ.toEmbedding,
     E.leftGates,
     fun i => (E.rightVars i).map σ.toEmbedding,
     E.rightGates,
     E.outVars.map σ.toEmbedding,
     E.outGates⟩
  have mapCirc_wf : ∀ (σ : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26),
      E.WellFormed → (mapCirc σ E).WellFormed := fun _ _ hw => hw
  have mapCirc_gateValFuel : ∀ (σ : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26)
      (U : Finset (Fin 26)) (d : ℕ) (i : Fin E.size),
      (mapCirc σ E).gateValFuel (U.map σ.toEmbedding) d i = E.gateValFuel U d i := by
    intro σ E U d
    induction d with
    | zero => intro i; rfl
    | succ d ih =>
      intro i
      have hside : ∀ (B : Finset (Fin 26)) (F : Finset (Fin E.size)),
          PEqualNP.AndCount.AndCountCircuit.sideTrue (U.map σ.toEmbedding) (B.map σ.toEmbedding) F i
            ((mapCirc σ E).gateValFuel (U.map σ.toEmbedding) d) =
          PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i (E.gateValFuel U d) := by
        intro B F
        rw [sideTrue_def, sideTrue_def, decide_eq_decide]
        constructor
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            obtain ⟨u, huB, rfl⟩ := Finset.mem_map.mp hvB
            exact Or.inl ⟨u, huB, by simpa using Finset.mem_map_equiv.mp hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hv⟩
            exact Or.inr ⟨j, hjF, hji, (ih j).symm.trans hv⟩
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨u, huB, huU⟩
            exact Or.inl ⟨σ u, Finset.mem_map.mpr ⟨u, huB, rfl⟩, Finset.mem_map.mpr ⟨u, huU, rfl⟩⟩
          · rcases h2 with ⟨j, hjF, hji, hv⟩
            exact Or.inr ⟨j, hjF, hji, (ih j).trans hv⟩
      show (PEqualNP.AndCount.AndCountCircuit.sideTrue (U.map σ.toEmbedding) ((E.leftVars i).map σ.toEmbedding)
              (E.leftGates i) i ((mapCirc σ E).gateValFuel (U.map σ.toEmbedding) d) &&
            PEqualNP.AndCount.AndCountCircuit.sideTrue (U.map σ.toEmbedding) ((E.rightVars i).map σ.toEmbedding)
              (E.rightGates i) i ((mapCirc σ E).gateValFuel (U.map σ.toEmbedding) d)) = _
      rw [hside (E.leftVars i) (E.leftGates i), hside (E.rightVars i) (E.rightGates i)]
      rfl
  have mapCirc_eval : ∀ (σ : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      (mapCirc σ E).eval (U.map σ.toEmbedding) = E.eval U := by
    intro σ E U
    rw [eval_def, eval_def]
    rw [decide_eq_decide]
    have hg : ∀ j : Fin E.size, (mapCirc σ E).gateVal (U.map σ.toEmbedding) j = E.gateVal U j :=
      fun j => mapCirc_gateValFuel σ E U E.size j
    constructor
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        obtain ⟨u, huO, rfl⟩ := Finset.mem_map.mp hvO
        exact Or.inl ⟨u, huO, by simpa using Finset.mem_map_equiv.mp hvU⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        exact Or.inr ⟨j, hjO, (hg j).symm.trans hjv⟩
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨u, huO, huU⟩
        exact Or.inl ⟨σ u, Finset.mem_map.mpr ⟨u, huO, rfl⟩, Finset.mem_map.mpr ⟨u, huU, rfl⟩⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        exact Or.inr ⟨j, hjO, (hg j).trans hjv⟩

  let inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  have inc_iff : ∀ p l : Fin 13, incB p l = true ↔ inc p l := by
    intro p l; simp only [incB, inc, decide_eq_true_eq]
  have inc_shift : ∀ (p l c : Fin 13), inc (p + c) (l + c) ↔ inc p l := by
    intro p l c
    simp only [inc]
    have h1 : p + c = l + c ↔ p = l := add_left_inj c
    have h2 : p + c = l + c + 1 ↔ p = l + 1 := by
      rw [add_right_comm l c 1]; exact add_left_inj c
    have h3 : p + c = l + c + 3 ↔ p = l + 3 := by
      rw [add_right_comm l c 3]; exact add_left_inj c
    have h4 : p + c = l + c + 9 ↔ p = l + 9 := by
      rw [add_right_comm l c 9]; exact add_left_inj c
    rw [h1, h2, h3, h4]
  have inc_sub : ∀ (p l c : Fin 13), inc (p - c) (l - c) ↔ inc p l := by
    intro p l c
    rw [f13_sub_eq_add_neg p c, f13_sub_eq_add_neg l c]
    exact inc_shift p l (-c)
  have inc_neg : ∀ (p l : Fin 13), inc (-l) (-p) ↔ inc p l := by
    intro p l
    have h := inc_shift (-l) (-p) (p + l)
    rw [f13_neg_add2 p l, f13_neg_add3 p l] at h
    exact h.symm
  let rowP (rc : Fin 36 × Fin 13) (p : Fin 13) : Bool := orbP rc.1 (p - rc.2)
  let rowW (rc : Fin 36 × Fin 13) (l : Fin 13) : Bool := orbW rc.1 (l - rc.2)
  let rowPSet (rc : Fin 36 × Fin 13) : Finset (Fin 13) :=
    Finset.univ.filter (fun p => rowP rc p = true)
  let liftRow (P : Finset (Fin 13)) : Finset (Fin 26) :=
    Finset.univ.filter fun k : Fin 26 =>
      (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
      ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ inc q l
  let rowSet (rc : Fin 36 × Fin 13) : Finset (Fin 26) := liftRow (rowPSet rc)
  have rowW_iff : ∀ (rc : Fin 36 × Fin 13) (l : Fin 13),
      rowW rc l = true ↔ ∀ q ∈ rowPSet rc, ¬ inc q l := by
    intro rc l
    dsimp only [rowW]
    rw [horb_w_spec rc.1 (l - rc.2), List.all_eq_true]
    constructor
    · intro hall q hq hinc
      have hqp : orbP rc.1 (q - rc.2) = true := (Finset.mem_filter.mp hq).2
      have h1 := hall (q - rc.2) (List.mem_finRange _)
      have hinc' : incB (q - rc.2) (l - rc.2) = true := (inc_iff _ _).mpr ((inc_sub q l rc.2).mpr hinc)
      simp [hqp, hinc'] at h1
    · intro hall p _
      by_cases hp : orbP rc.1 p = true
      · have hq : p + rc.2 ∈ rowPSet rc := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simpa [rowP] using hp
        have hni : ¬ inc (p + rc.2) l := hall (p + rc.2) hq
        have hni' : ¬ inc p (l - rc.2) := by
          intro h
          have h' := (inc_shift p (l - rc.2) rc.2).mpr h
          rw [f13_sub_add] at h'; exact hni h'
        have hbf : incB p (l - rc.2) = false := Bool.eq_false_iff.mpr (fun ht => hni' ((inc_iff _ _).mp ht))
        simp [hp, hbf]
      · have hpf : orbP rc.1 p = false := Bool.eq_false_iff.mpr hp
        simp [hpf]
  have mem_rowSet_cast : ∀ (rc : Fin 36 × Fin 13) (p : Fin 13),
      Fin.castAdd 13 p ∈ rowSet rc ↔ rowP rc p = true := by
    intro rc p
    simp only [rowSet, liftRow, Finset.mem_filter, Finset.mem_univ, true_and, rowPSet]
    constructor
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨q, hq, heq⟩
        have hpq : p = q := by
          have hv := congrArg Fin.val heq
          exact Fin.ext hv
        exact hpq ▸ hq
      · rcases h2 with ⟨l, heq, _⟩
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    · intro hp
      exact Or.inl ⟨p, hp, rfl⟩
  have mem_rowSet_nat : ∀ (rc : Fin 36 × Fin 13) (l : Fin 13),
      Fin.natAdd 13 l ∈ rowSet rc ↔ rowW rc l = true := by
    intro rc l
    rw [rowW_iff]
    simp only [rowSet, liftRow, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨p, _, heq⟩
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      · rcases h2 with ⟨l', heq, hall⟩
        have hll : l = l' := by
          have hv := congrArg Fin.val heq
          simp only [Fin.val_natAdd] at hv
          exact Fin.ext (by omega)
        exact hll ▸ hall
    · intro hall
      exact Or.inr ⟨l, rfl, hall⟩
  have row_max : ∀ (rc : Fin 36 × Fin 13) (p : Fin 13),
      p ∉ rowPSet rc → ∃ l : Fin 13, (∀ q ∈ rowPSet rc, ¬ inc q l) ∧ inc p l := by
    intro rc p hp
    have hpf : orbP rc.1 (p - rc.2) = false := by
      rw [Bool.eq_false_iff]
      intro ht
      exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
    obtain ⟨l0, hl0W, hl0inc⟩ := horb_max rc.1 (p - rc.2) hpf
    refine ⟨l0 + rc.2, ?_, ?_⟩
    · rw [← rowW_iff]
      simpa [rowW] using hl0W
    · have h1 := (inc_shift (p - rc.2) l0 rc.2).mpr ((inc_iff _ _).mp hl0inc)
      rw [f13_sub_add] at h1; exact h1
  have row_generic : ∀ (rc : Fin 36 × Fin 13),
      (¬∃ l : Fin 13, ∀ p ∈ rowPSet rc, inc p l) ∧
      (¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ rowPSet rc, ¬ inc q l) → inc p l) := by
    intro rc
    constructor
    · intro hex; rcases hex with ⟨l, hl⟩
      obtain ⟨p0, hp0, hni⟩ := horb_noncoll rc.1 (l - rc.2)
      have hp : p0 + rc.2 ∈ rowPSet rc := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [rowP] using hp0
      have hinc : inc (p0 + rc.2) l := hl (p0 + rc.2) hp
      have hinc' : inc p0 (l - rc.2) := by
        have h1 := (inc_sub (p0 + rc.2) l rc.2).mpr hinc
        rw [f13_add_sub] at h1; exact h1
      have ht : incB p0 (l - rc.2) = true := (inc_iff _ _).mpr hinc'
      rw [hni] at ht; cases ht
    · intro hex; rcases hex with ⟨p, hp⟩
      obtain ⟨l0, hl0, hni⟩ := horb_nonconc rc.1 (p - rc.2)
      have hlW : rowW rc (l0 + rc.2) = true := by simpa [rowW] using hl0
      have hinc : inc p (l0 + rc.2) := hp (l0 + rc.2) ((rowW_iff rc (l0 + rc.2)).mp hlW)
      have hinc' : inc (p - rc.2) l0 := by
        have h1 := (inc_sub p (l0 + rc.2) rc.2).mpr hinc
        rw [f13_add_sub] at h1; exact h1
      have ht : incB (p - rc.2) l0 = true := (inc_iff _ _).mpr hinc'
      rw [hni] at ht; cases ht
  have row_inj : Function.Injective rowSet := by
    intro a b hab
    by_contra hne
    have hcase : a.1 ≠ b.1 ∨ (b.2 - a.2) ≠ 0 := by
      by_cases h1 : a.1 = b.1
      · right
        intro h2
        apply hne
        have hc : b.2 = a.2 := (f13_sub_zero b.2 a.2).mp h2
        exact Prod.ext h1 hc.symm
      · exact Or.inl h1
    obtain ⟨p0, hdiff⟩ := horb_ne a.1 b.1 (b.2 - a.2) hcase
    have hma := mem_rowSet_cast a (p0 + a.2)
    have hmb := mem_rowSet_cast b (p0 + a.2)
    rw [hab] at hma
    have heq : rowP a (p0 + a.2) = rowP b (p0 + a.2) := Bool.eq_iff_iff.mpr (hma.symm.trans hmb)
    dsimp only [rowP] at heq
    have hs1 : p0 + a.2 - a.2 = p0 := f13_add_sub p0 a.2
    have hs2 : p0 + a.2 - b.2 = p0 - (b.2 - a.2) := f13_add_sub_sub p0 a.2 b.2
    rw [hs1, hs2] at heq
    exact hdiff heq
  let allRows : Finset (Finset (Fin 26)) := Finset.univ.image rowSet
  have row_incomp : ∀ I ∈ allRows, ∀ J ∈ allRows, I ≠ J → ∃ w ∈ I, w ∉ J := by
    intro I hI J hJ hne
    by_contra hall
    push Not at hall
    have hsub : I ⊆ J := hall
    have hssub : ∃ w ∈ J, w ∉ I := by
      by_contra h2
      push Not at h2
      exact hne (Finset.Subset.antisymm hsub h2)
    obtain ⟨w, hwJ, hwnI⟩ := hssub
    obtain ⟨rcI, _, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨rcJ, _, rfl⟩ := Finset.mem_image.mp hJ
    by_cases hlt : w.val < 13
    · let p : Fin 13 := ⟨w.val, hlt⟩
      have hw_eq : w = Fin.castAdd 13 p := Fin.ext rfl
      rw [hw_eq] at hwJ hwnI
      have hpJ : p ∈ rowPSet rcJ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_rowSet_cast rcJ p).mp hwJ⟩
      have hpnI : p ∉ rowPSet rcI := fun h => hwnI ((mem_rowSet_cast rcI p).mpr (Finset.mem_filter.mp h).2)
      obtain ⟨l, hlWI, hinc⟩ := row_max rcI p hpnI
      have hlI : Fin.natAdd 13 l ∈ rowSet rcI := (mem_rowSet_nat rcI l).mpr ((rowW_iff rcI l).mpr hlWI)
      have hlJ : Fin.natAdd 13 l ∈ rowSet rcJ := hsub hlI
      exact (rowW_iff rcJ l).mp ((mem_rowSet_nat rcJ l).mp hlJ) p hpJ hinc
    · let l : Fin 13 := ⟨w.val - 13, by omega⟩
      have hw_eq : w = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      rw [hw_eq] at hwJ hwnI
      have hlJ : ∀ q ∈ rowPSet rcJ, ¬ inc q l := (rowW_iff rcJ l).mp ((mem_rowSet_nat rcJ l).mp hwJ)
      have hlnI : ¬ ∀ q ∈ rowPSet rcI, ¬ inc q l := fun h =>
        hwnI ((mem_rowSet_nat rcI l).mpr ((rowW_iff rcI l).mpr h))
      push Not at hlnI
      obtain ⟨q, hqI, hinc⟩ := hlnI
      have hqInI : Fin.castAdd 13 q ∈ rowSet rcI := (mem_rowSet_cast rcI q).mpr (Finset.mem_filter.mp hqI).2
      have hqInJ : Fin.castAdd 13 q ∈ rowSet rcJ := hsub hqInI
      have hqJ : q ∈ rowPSet rcJ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_rowSet_cast rcJ q).mp hqInJ⟩
      exact hlJ q hqJ hinc

  let shiftFn (c : Fin 13) (k : Fin 26) : Fin 26 :=
    if h : k.val < 13 then Fin.castAdd 13 (⟨k.val, h⟩ + c)
    else Fin.natAdd 13 (⟨k.val - 13, by omega⟩ + c)
  have shiftFn_cast : ∀ (c p : Fin 13), shiftFn c (Fin.castAdd 13 p) = Fin.castAdd 13 (p + c) := by
    intro c p
    have hlt : (Fin.castAdd 13 p).val < 13 := p.isLt
    simp only [shiftFn, hlt, ↓reduceDIte]
    rfl
  have shiftFn_nat : ∀ (c l : Fin 13), shiftFn c (Fin.natAdd 13 l) = Fin.natAdd 13 (l + c) := by
    intro c l
    have hlt : ¬ (Fin.natAdd 13 l).val < 13 := by simp
    simp only [shiftFn, hlt, ↓reduceDIte]
    apply Fin.ext
    simp
  let shiftEquiv (c : Fin 13) : Fin 26 ≃ Fin 26 :=
    { toFun := shiftFn c
      invFun := shiftFn (-c)
      left_inv := by
        intro k
        by_cases h : k.val < 13
        · let p : Fin 13 := ⟨k.val, h⟩
          have hk : k = Fin.castAdd 13 p := Fin.ext rfl
          rw [hk, shiftFn_cast, shiftFn_cast, f13_add_neg]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
          rw [hk, shiftFn_nat, shiftFn_nat, f13_add_neg]
      right_inv := by
        intro k
        by_cases h : k.val < 13
        · let p : Fin 13 := ⟨k.val, h⟩
          have hk : k = Fin.castAdd 13 p := Fin.ext rfl
          rw [hk, shiftFn_cast, shiftFn_cast, f13_neg_add]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
          rw [hk, shiftFn_nat, shiftFn_nat, f13_neg_add] }
  have shift_rowSet : ∀ (c : Fin 13) (rc : Fin 36 × Fin 13),
      (rowSet rc).map (shiftEquiv c).toEmbedding = rowSet (rc.1, rc.2 + c) := by
    intro c rc
    ext k
    by_cases h : k.val < 13
    · let p : Fin 13 := ⟨k.val, h⟩
      have hk : k = Fin.castAdd 13 p := Fin.ext rfl
      rw [hk, Finset.mem_map_equiv, mem_rowSet_cast]
      have hinv : (shiftEquiv c).symm (Fin.castAdd 13 p) = Fin.castAdd 13 (p - c) := by
        change shiftFn (-c) (Fin.castAdd 13 p) = Fin.castAdd 13 (p - c)
        rw [shiftFn_cast, f13_sub_eq_add_neg]
      rw [hinv, mem_rowSet_cast]
      dsimp only [rowP]
      have hs : p - c - rc.2 = p - (rc.2 + c) := f13_sub_sub p c rc.2
      rw [hs]
    · let l : Fin 13 := ⟨k.val - 13, by omega⟩
      have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      rw [hk, Finset.mem_map_equiv, mem_rowSet_nat]
      have hinv : (shiftEquiv c).symm (Fin.natAdd 13 l) = Fin.natAdd 13 (l - c) := by
        change shiftFn (-c) (Fin.natAdd 13 l) = Fin.natAdd 13 (l - c)
        rw [shiftFn_nat, f13_sub_eq_add_neg]
      rw [hinv, mem_rowSet_nat]
      dsimp only [rowW]
      have hs : l - c - rc.2 = l - (rc.2 + c) := f13_sub_sub l c rc.2
      rw [hs]
  have shift_allRows : ∀ (c : Fin 13) (I : Finset (Fin 26)),
      I ∈ allRows → I.map (shiftEquiv c).toEmbedding ∈ allRows := by
    intro c I hI
    obtain ⟨rc, _, rfl⟩ := Finset.mem_image.mp hI
    rw [shift_rowSet c rc]
    exact Finset.mem_image.mpr ⟨(rc.1, rc.2 + c), Finset.mem_univ _, rfl⟩

  have rows0_mem_0 : ∀ rc ∈ rows0, rowP rc 0 = true := by
    intro rc hrc
    exact List.all_eq_true.mp rows0_ok rc hrc
  have hL5_geom : ∀ (p2 l : Fin 13), p2 ≠ 0 → incB 0 l = false → incB p2 l = false →
      let Y := (List.finRange 13).filter (fun m => (m != l) && !incB 0 m && !incB p2 m)
      let R := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2) && orbW rc.1 (l - rc.2))
      Y.length = 5 ∧
      (∀ m ∈ Y, 5 ≤ (R.filter (fun rc => orbW rc.1 (m - rc.2))).length) ∧
      (∀ m ∈ Y, ∃ rc ∈ R, orbW rc.1 (m - rc.2) = false) ∧
      (∀ m1 ∈ Y, ∀ m2 ∈ Y, m1 ≠ m2 → ∃ rc ∈ R, orbW rc.1 (m1 - rc.2) = true ∧ orbW rc.1 (m2 - rc.2) = false) ∧
      (∀ m1 ∈ Y, ∀ m2 ∈ Y, m1 ≠ m2 → ∃ rc ∈ R, orbW rc.1 (m1 - rc.2) = false ∧ orbW rc.1 (m2 - rc.2) = false) := by
    intro p2 l hp2 h0l hp2l
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hL5_bool p2 (List.mem_finRange p2)) l (List.mem_finRange l)
    have hne0 : (p2 == 0) = false := beq_false_of_ne hp2
    rw [hne0, h0l, hp2l] at h1
    simp only [Bool.false_or, Bool.and_eq_true] at h1
    refine ⟨beq_iff_eq.mp h1.1.1.1, ?_, ?_, ?_, ?_⟩
    · intro m hm
      exact Nat.ble_eq.mp (List.all_eq_true.mp h1.1.1.2 m hm)
    · intro m hm
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1.1.2 m hm)
      exact ⟨rc, hrc, by simpa using hf⟩
    · intro m1 hm1 m2 hm2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 m1 hm1) m2 hm2
      have hne' : (m1 == m2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
    · intro m1 hm1 m2 hm2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 m1 hm1) m2 hm2
      have hne' : (m1 == m2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
  have hL4_geom : ∀ (p2 : Fin 13), p2 ≠ 0 →
      let Y := (List.finRange 13).filter (fun m => !incB 0 m && !incB p2 m)
      let R := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2))
      Y.length = 6 ∧
      (∀ m ∈ Y, 9 ≤ (R.filter (fun rc => orbW rc.1 (m - rc.2))).length) ∧
      (∀ m ∈ Y, ∃ rc ∈ R, orbW rc.1 (m - rc.2) = false) ∧
      (∀ m1 ∈ Y, ∀ m2 ∈ Y, m1 ≠ m2 → ∃ rc ∈ R, orbW rc.1 (m1 - rc.2) = true ∧ orbW rc.1 (m2 - rc.2) = false) ∧
      (∀ m1 ∈ Y, ∀ m2 ∈ Y, m1 ≠ m2 → ∃ rc ∈ R, orbW rc.1 (m1 - rc.2) = false ∧ orbW rc.1 (m2 - rc.2) = false) := by
    intro p2 hp2
    have h1 := List.all_eq_true.mp hL4_bool p2 (List.mem_finRange p2)
    have hne0 : (p2 == 0) = false := beq_false_of_ne hp2
    rw [hne0] at h1
    simp only [Bool.false_or, Bool.and_eq_true] at h1
    refine ⟨beq_iff_eq.mp h1.1.1.1, ?_, ?_, ?_, ?_⟩
    · intro m hm
      exact Nat.ble_eq.mp (List.all_eq_true.mp h1.1.1.2 m hm)
    · intro m hm
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1.1.2 m hm)
      exact ⟨rc, hrc, by simpa using hf⟩
    · intro m1 hm1 m2 hm2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 m1 hm1) m2 hm2
      have hne' : (m1 == m2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
    · intro m1 hm1 m2 hm2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 m1 hm1) m2 hm2
      have hne' : (m1 == m2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
  have hL3_geom : ∀ (l0 : Fin 13), incB 0 l0 = false →
      let X := (List.finRange 13).filter (fun q => (q != 0) && !incB q l0)
      let R := rows0.filter (fun rc => orbW rc.1 (l0 - rc.2))
      X.length = 8 ∧
      (∀ q ∈ X, ∃ rc ∈ R, orbP rc.1 (q - rc.2) = true) ∧
      (∀ q ∈ X, ∃ rc ∈ R, orbP rc.1 (q - rc.2) = false) ∧
      (∀ q1 ∈ X, ∀ q2 ∈ X, q1 ≠ q2 → ∃ rc ∈ R, orbP rc.1 (q1 - rc.2) = true ∧ orbP rc.1 (q2 - rc.2) = false) ∧
      (∀ q1 ∈ X, ∀ q2 ∈ X, q1 ≠ q2 → ∃ rc ∈ R, orbP rc.1 (q1 - rc.2) = false ∧ orbP rc.1 (q2 - rc.2) = false) := by
    intro l0 h0l
    have h1 := List.all_eq_true.mp hL3_bool l0 (List.mem_finRange l0)
    rw [h0l] at h1
    simp only [Bool.false_or, Bool.and_eq_true] at h1
    refine ⟨beq_iff_eq.mp h1.1.1.1, ?_, ?_, ?_, ?_⟩
    · intro q hq
      exact List.any_eq_true.mp (List.all_eq_true.mp h1.1.1.2 q hq)
    · intro q hq
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1.1.2 q hq)
      exact ⟨rc, hrc, by simpa using hf⟩
    · intro q1 hq1 q2 hq2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 q1 hq1) q2 hq2
      have hne' : (q1 == q2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
    · intro q1 hq1 q2 hq2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 q1 hq1) q2 hq2
      have hne' : (q1 == q2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
  have hL2_geom :
      let Y := (List.finRange 13).filter (fun l => !incB 0 l)
      Y.length = 9 ∧
      (∀ l ∈ Y, ∃ rc ∈ rows0, orbW rc.1 (l - rc.2) = true) ∧
      (∀ l ∈ Y, ∃ rc ∈ rows0, orbW rc.1 (l - rc.2) = false) ∧
      (∀ l1 ∈ Y, ∀ l2 ∈ Y, l1 ≠ l2 → ∃ rc ∈ rows0, orbW rc.1 (l1 - rc.2) = true ∧ orbW rc.1 (l2 - rc.2) = false) ∧
      (∀ l1 ∈ Y, ∀ l2 ∈ Y, l1 ≠ l2 → ∃ rc ∈ rows0, orbW rc.1 (l1 - rc.2) = false ∧ orbW rc.1 (l2 - rc.2) = false) := by
    have h1 := hL2_bool
    simp only [Bool.and_eq_true] at h1
    refine ⟨beq_iff_eq.mp h1.1.1.1, ?_, ?_, ?_, ?_⟩
    · intro l hl
      exact List.any_eq_true.mp (List.all_eq_true.mp h1.1.1.2 l hl)
    · intro l hl
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1.1.2 l hl)
      exact ⟨rc, hrc, by simpa using hf⟩
    · intro l1 hl1 l2 hl2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 l1 hl1) l2 hl2
      have hne' : (l1 == l2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
    · intro l1 hl1 l2 hl2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 l1 hl1) l2 hl2
      have hne' : (l1 == l2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩

  have list_to_rows_card : ∀ (L : List (Fin 36 × Fin 13)) (Rows : Finset (Finset (Fin 26))),
      L.Nodup → (∀ rc ∈ L, rowSet rc ∈ Rows) → L.length ≤ Rows.card := by
    intro L Rows hnd hsub
    have h1 : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
    have h2 : (L.toFinset.image rowSet).card = L.toFinset.card :=
      Finset.card_image_of_injective L.toFinset row_inj
    have h3 : L.toFinset.image rowSet ⊆ Rows := by
      intro I hI
      obtain ⟨rc, hrc, rfl⟩ := Finset.mem_image.mp hI
      exact hsub rc (List.mem_toFinset.mp hrc)
    calc L.length = (L.toFinset.image rowSet).card := by rw [h2, h1]
      _ ≤ Rows.card := Finset.card_le_card h3

  have hLevel5_0 : ∀ (p2 l : Fin 13), p2 ≠ 0 → ¬ inc 0 l → ¬ inc p2 l →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 p2 ∈ I ∧ Fin.natAdd 13 l ∈ I) →
        5 ≤ E.size := by
    intro p2 l hp2 hni0 hnip2 E hw hsep
    by_contra! hlt
    have hsz : E.size ≤ 4 := by omega
    obtain ⟨D, hDsz, _, hDdisj, _, hDeval⟩ := strip_exists E hw
    let Rows := allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 p2 ∈ I ∧ Fin.natAdd 13 l ∈ I
    have hDsep : Separates D Rows := by
      intro I hI
      have h := hsep I hI
      exact ⟨by rw [hDeval]; exact h.1, fun w hw => by rw [hDeval]; exact h.2 w hw⟩
    have hbi0 : incB 0 l = false := Bool.eq_false_iff.mpr (fun ht => hni0 ((inc_iff _ _).mp ht))
    have hbip2 : incB p2 l = false := Bool.eq_false_iff.mpr (fun ht => hnip2 ((inc_iff _ _).mp ht))
    obtain ⟨hYlen, hYcnt, hYout, hYsame, hYopp⟩ := hL5_geom p2 l hp2 hbi0 hbip2
    let Ylist := (List.finRange 13).filter (fun m => (m != l) && !incB 0 m && !incB p2 m)
    let Rlist := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2) && orbW rc.1 (l - rc.2))
    let Z : Finset (Fin 26) := Ylist.toFinset.image (Fin.natAdd 13)
    have hZcard : Z.card = 5 := by
      have hnd : Ylist.Nodup := List.Nodup.filter _ (List.nodup_finRange 13)
      have hinj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := fun a b h => by
        have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
      rw [Finset.card_image_of_injective _ hinj, List.toFinset_card_of_nodup hnd, hYlen]
    have hRmem : ∀ rc ∈ Rlist, rowSet rc ∈ Rows := by
      intro rc hrc
      have h1 := List.mem_filter.mp hrc
      have h0 : rowP rc 0 = true := rows0_mem_0 rc h1.1
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, ?_, ?_, ?_⟩
      · exact (mem_rowSet_cast rc 0).mpr h0
      · exact (mem_rowSet_cast rc p2).mpr h2.1
      · exact (mem_rowSet_nat rc l).mpr h2.2
    have hZdeg1 : ∀ z ∈ Z, (litSet D z).card ≤ 1 := by
      intro z hz
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
      have hmL : m ∈ Ylist := List.mem_toFinset.mp hm
      have hcnt5 : 5 ≤ (Rlist.filter (fun rc => orbW rc.1 (m - rc.2))).length := hYcnt m hmL
      have hndR : (Rlist.filter (fun rc => orbW rc.1 (m - rc.2))).Nodup :=
        List.Nodup.filter _ (List.Nodup.filter _ rows0_nodup)
      have hcard5 : 5 ≤ (Rows.filter (fun I => Fin.natAdd 13 m ∈ I)).card := by
        refine hcnt5.trans (list_to_rows_card _ _ hndR ?_)
        intro rc hrc
        have hf := List.mem_filter.mp hrc
        exact Finset.mem_filter.mpr ⟨hRmem rc hf.1, (mem_rowSet_nat rc m).mpr hf.2⟩
      have hfb := free_bound_gen D Rows (Fin.natAdd 13 m) hDsep
        (fun I hI J hJ hne => row_incomp I (Finset.mem_filter.mp hI).1 J (Finset.mem_filter.mp hJ).1 hne)
      have hpow : 3 ≤ (Free D (Fin.natAdd 13 m)).card := by
        by_contra! hlt3
        have hp : 2 ^ (Free D (Fin.natAdd 13 m)).card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hsum := (litSet_touch_card D hDdisj (Fin.natAdd 13 m)).2
      omega
    have hZle := card_le_size_of_deg_le_one D Rows Z hDsep
      (fun z hz => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        have hcnt5 := hYcnt m (List.mem_toFinset.mp hm)
        obtain ⟨rc, hrc⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (by decide : 0 < 5) (by exact hcnt5)))
        have hf := List.mem_filter.mp hrc
        exact ⟨rowSet rc, hRmem rc hf.1, (mem_rowSet_nat rc m).mpr hf.2⟩)
      (fun z hz => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hmf⟩ := hYout m (List.mem_toFinset.mp hm)
        exact ⟨rowSet rc, hRmem rc hrc, (fun hmem => by have ht := (mem_rowSet_nat rc m).mp hmem; dsimp only [rowW] at ht; rw [hmf] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨m2, hm2, rfl⟩ := Finset.mem_image.mp hz2
        have hmn : m1 ≠ m2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYsame m1 (List.mem_toFinset.mp hm1) m2 (List.mem_toFinset.mp hm2) hmn
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_nat rc m1).mpr h1, (fun hmem => by have ht := (mem_rowSet_nat rc m2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨m2, hm2, rfl⟩ := Finset.mem_image.mp hz2
        have hmn : m1 ≠ m2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYopp m1 (List.mem_toFinset.mp hm1) m2 (List.mem_toFinset.mp hm2) hmn
        exact ⟨rowSet rc, hRmem rc hrc,
          (fun hmem => by have ht := (mem_rowSet_nat rc m1).mp hmem; dsimp only [rowW] at ht; rw [h1] at ht; cases ht),
          (fun hmem => by have ht := (mem_rowSet_nat rc m2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      hZdeg1
    omega

  have hLevel4_0 : ∀ (p2 : Fin 13), p2 ≠ 0 →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 p2 ∈ I) →
        6 ≤ E.size := by
    intro p2 hp2 E hw hsep
    by_contra! hlt
    have hsz : E.size ≤ 5 := by omega
    obtain ⟨D, hDsz, _, hDdisj, _, hDeval⟩ := strip_exists E hw
    let Rows := allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 p2 ∈ I
    have hDsep : Separates D Rows := by
      intro I hI
      have h := hsep I hI
      exact ⟨by rw [hDeval]; exact h.1, fun w hw => by rw [hDeval]; exact h.2 w hw⟩
    obtain ⟨hYlen, hYcnt, hYout, hYsame, hYopp⟩ := hL4_geom p2 hp2
    let Ylist := (List.finRange 13).filter (fun m => !incB 0 m && !incB p2 m)
    let Rlist := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2))
    let Z : Finset (Fin 26) := Ylist.toFinset.image (Fin.natAdd 13)
    have hZcard : Z.card = 6 := by
      have hnd : Ylist.Nodup := List.Nodup.filter _ (List.nodup_finRange 13)
      have hinj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := fun a b h => by
        have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
      rw [Finset.card_image_of_injective _ hinj, List.toFinset_card_of_nodup hnd, hYlen]
    have hRmem : ∀ rc ∈ Rlist, rowSet rc ∈ Rows := by
      intro rc hrc
      have h1 := List.mem_filter.mp hrc
      have h0 : rowP rc 0 = true := rows0_mem_0 rc h1.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
      · exact (mem_rowSet_cast rc 0).mpr h0
      · exact (mem_rowSet_cast rc p2).mpr h1.2
    have hZdeg1 : ∀ z ∈ Z, (litSet D z).card ≤ 1 := by
      intro z hz
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
      have hmL : m ∈ Ylist := List.mem_toFinset.mp hm
      have hcnt9 : 9 ≤ (Rlist.filter (fun rc => orbW rc.1 (m - rc.2))).length := hYcnt m hmL
      have hndR : (Rlist.filter (fun rc => orbW rc.1 (m - rc.2))).Nodup :=
        List.Nodup.filter _ (List.Nodup.filter _ rows0_nodup)
      have hcard9 : 9 ≤ (Rows.filter (fun I => Fin.natAdd 13 m ∈ I)).card := by
        refine hcnt9.trans (list_to_rows_card _ _ hndR ?_)
        intro rc hrc
        have hf := List.mem_filter.mp hrc
        exact Finset.mem_filter.mpr ⟨hRmem rc hf.1, (mem_rowSet_nat rc m).mpr hf.2⟩
      have hfb := free_bound_gen D Rows (Fin.natAdd 13 m) hDsep
        (fun I hI J hJ hne => row_incomp I (Finset.mem_filter.mp hI).1 J (Finset.mem_filter.mp hJ).1 hne)
      have hpow : 4 ≤ (Free D (Fin.natAdd 13 m)).card := by
        by_contra! hlt4
        have hp : 2 ^ (Free D (Fin.natAdd 13 m)).card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hsum := (litSet_touch_card D hDdisj (Fin.natAdd 13 m)).2
      omega
    have hZle := card_le_size_of_deg_le_one D Rows Z hDsep
      (fun z hz => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        have hcnt9 := hYcnt m (List.mem_toFinset.mp hm)
        obtain ⟨rc, hrc⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (by decide : 0 < 9) (by exact hcnt9)))
        have hf := List.mem_filter.mp hrc
        exact ⟨rowSet rc, hRmem rc hf.1, (mem_rowSet_nat rc m).mpr hf.2⟩)
      (fun z hz => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hmf⟩ := hYout m (List.mem_toFinset.mp hm)
        exact ⟨rowSet rc, hRmem rc hrc, (fun hmem => by have ht := (mem_rowSet_nat rc m).mp hmem; dsimp only [rowW] at ht; rw [hmf] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨m2, hm2, rfl⟩ := Finset.mem_image.mp hz2
        have hmn : m1 ≠ m2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYsame m1 (List.mem_toFinset.mp hm1) m2 (List.mem_toFinset.mp hm2) hmn
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_nat rc m1).mpr h1, (fun hmem => by have ht := (mem_rowSet_nat rc m2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨m2, hm2, rfl⟩ := Finset.mem_image.mp hz2
        have hmn : m1 ≠ m2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYopp m1 (List.mem_toFinset.mp hm1) m2 (List.mem_toFinset.mp hm2) hmn
        exact ⟨rowSet rc, hRmem rc hrc,
          (fun hmem => by have ht := (mem_rowSet_nat rc m1).mp hmem; dsimp only [rowW] at ht; rw [h1] at ht; cases ht),
          (fun hmem => by have ht := (mem_rowSet_nat rc m2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      hZdeg1
    omega

  have hLevel3_0 : ∀ (l0 : Fin 13), ¬ inc 0 l0 →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.natAdd 13 l0 ∈ I) →
        7 ≤ E.size := by
    intro l0 hni0 E hw hsep
    by_contra! hlt
    have hsz : E.size ≤ 6 := by omega
    obtain ⟨D, hDsz, hDwf, hDdisj, _, hDeval⟩ := strip_exists E hw
    let Rows := allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.natAdd 13 l0 ∈ I
    have hDsep : Separates D Rows := by
      intro I hI
      have h := hsep I hI
      exact ⟨by rw [hDeval]; exact h.1, fun w hw => by rw [hDeval]; exact h.2 w hw⟩
    have hbi0 : incB 0 l0 = false := Bool.eq_false_iff.mpr (fun ht => hni0 ((inc_iff _ _).mp ht))
    obtain ⟨hXlen, hXin, hXout, hXsame, hXopp⟩ := hL3_geom l0 hbi0
    let Xlist := (List.finRange 13).filter (fun q => (q != 0) && !incB q l0)
    let Rlist := rows0.filter (fun rc => orbW rc.1 (l0 - rc.2))
    let Z : Finset (Fin 26) := Xlist.toFinset.image (Fin.castAdd 13)
    have hZcard : Z.card = 8 := by
      have hnd : Xlist.Nodup := List.Nodup.filter _ (List.nodup_finRange 13)
      have hinj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := fun a b h => Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val h)
      rw [Finset.card_image_of_injective _ hinj, List.toFinset_card_of_nodup hnd, hXlen]
    have hRmem : ∀ rc ∈ Rlist, rowSet rc ∈ Rows := by
      intro rc hrc
      have h1 := List.mem_filter.mp hrc
      have h0 : rowP rc 0 = true := rows0_mem_0 rc h1.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
      · exact (mem_rowSet_cast rc 0).mpr h0
      · exact (mem_rowSet_nat rc l0).mpr h1.2
    have hZdeg1 : ∀ z ∈ Z, (litSet D z).card ≤ 1 := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hqL : q ∈ Xlist := List.mem_toFinset.mp hq
      have hqcond := Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hqL).2
      have hqne : q ≠ 0 := bne_iff_ne.mp hqcond.1
      have hqni : ¬ inc q l0 := by
        intro h
        have ht : incB q l0 = true := (inc_iff _ _).mpr h
        have hf := hqcond.2
        rw [ht] at hf; cases hf
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices D hDwf {Fin.castAdd 13 q}
      have hsep' : Separates E' (allRows.filter fun I =>
          Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 q ∈ I ∧ Fin.natAdd 13 l0 ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hIR : I ∈ Rows := Finset.mem_filter.mpr ⟨hf.1, hf.2.1, hf.2.2.2⟩
        have hsub : ({Fin.castAdd 13 q} : Finset (Fin 26)) ⊆ I := Finset.singleton_subset_iff.mpr hf.2.2.1
        refine ⟨(heq I hsub).trans (hDsep I hIR).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hDsep I hIR).2 w hw)
      have h5 : 5 ≤ E'.size := hLevel5_0 q l0 hqne hni0 hqni E' hw' hsep'
      have htc : (litSet D (Fin.castAdd 13 q)).card =
          (Finset.univ.filter fun i : Fin D.size =>
            ∃ v ∈ ({Fin.castAdd 13 q} : Finset (Fin 26)), v ∈ D.leftVars i ∨ v ∈ D.rightVars i).card := by
        rw [(litSet_touch_card D hDdisj (Fin.castAdd 13 q)).1]
        apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left]
      rw [← htc] at hbd
      omega
    have hZle := card_le_size_of_deg_le_one D Rows Z hDsep
      (fun z hz => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hqt⟩ := hXin q (List.mem_toFinset.mp hq)
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_cast rc q).mpr hqt⟩)
      (fun z hz => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hqf⟩ := hXout q (List.mem_toFinset.mp hq)
        exact ⟨rowSet rc, hRmem rc hrc, (fun hmem => by have ht := (mem_rowSet_cast rc q).mp hmem; dsimp only [rowP] at ht; rw [hqf] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨q1, hq1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨q2, hq2, rfl⟩ := Finset.mem_image.mp hz2
        have hqn : q1 ≠ q2 := fun h => hne (congrArg (Fin.castAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hXsame q1 (List.mem_toFinset.mp hq1) q2 (List.mem_toFinset.mp hq2) hqn
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_cast rc q1).mpr h1, (fun hmem => by have ht := (mem_rowSet_cast rc q2).mp hmem; dsimp only [rowP] at ht; rw [h2] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨q1, hq1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨q2, hq2, rfl⟩ := Finset.mem_image.mp hz2
        have hqn : q1 ≠ q2 := fun h => hne (congrArg (Fin.castAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hXopp q1 (List.mem_toFinset.mp hq1) q2 (List.mem_toFinset.mp hq2) hqn
        exact ⟨rowSet rc, hRmem rc hrc,
          (fun hmem => by have ht := (mem_rowSet_cast rc q1).mp hmem; dsimp only [rowP] at ht; rw [h1] at ht; cases ht),
          (fun hmem => by have ht := (mem_rowSet_cast rc q2).mp hmem; dsimp only [rowP] at ht; rw [h2] at ht; cases ht)⟩)
      hZdeg1
    omega

  have hLevel2_0 : ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
      Separates E (allRows.filter fun I => Fin.castAdd 13 0 ∈ I) →
      9 ≤ E.size := by
    intro E hw hsep
    by_contra! hlt
    have hsz : E.size ≤ 8 := by omega
    obtain ⟨D, hDsz, hDwf, hDdisj, _, hDeval⟩ := strip_exists E hw
    let Rows := allRows.filter fun I => Fin.castAdd 13 0 ∈ I
    have hDsep : Separates D Rows := by
      intro I hI
      have h := hsep I hI
      exact ⟨by rw [hDeval]; exact h.1, fun w hw => by rw [hDeval]; exact h.2 w hw⟩
    obtain ⟨hYlen, hYin, hYout, hYsame, hYopp⟩ := hL2_geom
    let Ylist := (List.finRange 13).filter (fun l => !incB 0 l)
    let Z : Finset (Fin 26) := Ylist.toFinset.image (Fin.natAdd 13)
    have hZcard : Z.card = 9 := by
      have hnd : Ylist.Nodup := List.Nodup.filter _ (List.nodup_finRange 13)
      have hinj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := fun a b h => by
        have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
      rw [Finset.card_image_of_injective _ hinj, List.toFinset_card_of_nodup hnd, hYlen]
    have hRmem : ∀ rc ∈ rows0, rowSet rc ∈ Rows := by
      intro rc hrc
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, (mem_rowSet_cast rc 0).mpr (rows0_mem_0 rc hrc)⟩
    have hZdeg1 : ∀ z ∈ Z, (litSet D z).card ≤ 1 := by
      intro z hz
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
      have hlL : l ∈ Ylist := List.mem_toFinset.mp hl
      have hlni : ¬ inc 0 l := by
        intro h
        have ht : incB 0 l = true := (inc_iff _ _).mpr h
        have hf := (List.mem_filter.mp hlL).2
        rw [ht] at hf; cases hf
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices D hDwf {Fin.natAdd 13 l}
      have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.natAdd 13 l ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hIR : I ∈ Rows := Finset.mem_filter.mpr ⟨hf.1, hf.2.1⟩
        have hsub : ({Fin.natAdd 13 l} : Finset (Fin 26)) ⊆ I := Finset.singleton_subset_iff.mpr hf.2.2
        refine ⟨(heq I hsub).trans (hDsep I hIR).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hDsep I hIR).2 w hw)
      have h7 : 7 ≤ E'.size := hLevel3_0 l hlni E' hw' hsep'
      have htc : (litSet D (Fin.natAdd 13 l)).card =
          (Finset.univ.filter fun i : Fin D.size =>
            ∃ v ∈ ({Fin.natAdd 13 l} : Finset (Fin 26)), v ∈ D.leftVars i ∨ v ∈ D.rightVars i).card := by
        rw [(litSet_touch_card D hDdisj (Fin.natAdd 13 l)).1]
        apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left]
      rw [← htc] at hbd
      omega
    have hZle := card_le_size_of_deg_le_one D Rows Z hDsep
      (fun z hz => by
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hlt'⟩ := hYin l (List.mem_toFinset.mp hl)
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_nat rc l).mpr hlt'⟩)
      (fun z hz => by
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hlf⟩ := hYout l (List.mem_toFinset.mp hl)
        exact ⟨rowSet rc, hRmem rc hrc, (fun hmem => by have ht := (mem_rowSet_nat rc l).mp hmem; dsimp only [rowW] at ht; rw [hlf] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨l1, hl1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨l2, hl2, rfl⟩ := Finset.mem_image.mp hz2
        have hln : l1 ≠ l2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYsame l1 (List.mem_toFinset.mp hl1) l2 (List.mem_toFinset.mp hl2) hln
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_nat rc l1).mpr h1, (fun hmem => by have ht := (mem_rowSet_nat rc l2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨l1, hl1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨l2, hl2, rfl⟩ := Finset.mem_image.mp hz2
        have hln : l1 ≠ l2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYopp l1 (List.mem_toFinset.mp hl1) l2 (List.mem_toFinset.mp hl2) hln
        exact ⟨rowSet rc, hRmem rc hrc,
          (fun hmem => by have ht := (mem_rowSet_nat rc l1).mp hmem; dsimp only [rowW] at ht; rw [h1] at ht; cases ht),
          (fun hmem => by have ht := (mem_rowSet_nat rc l2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      hZdeg1
    omega

  have hShift_sep : ∀ (c : Fin 13) (E : PEqualNP.AndCount.AndCountCircuit 26)
      (Rows : Finset (Finset (Fin 26))),
      Separates E Rows →
      Separates (mapCirc (shiftEquiv c) E) (Rows.image fun I => I.map (shiftEquiv c).toEmbedding) := by
    intro c E Rows hsep J hJ
    obtain ⟨I, hIR, rfl⟩ := Finset.mem_image.mp hJ
    have hI := hsep I hIR
    refine ⟨(mapCirc_eval (shiftEquiv c) E I).trans hI.1, ?_⟩
    intro w hw
    let u := (shiftEquiv c).symm w
    have hu : u ∉ I := fun h => hw (by
      have hm : (shiftEquiv c) u ∈ I.map (shiftEquiv c).toEmbedding := Finset.mem_map.mpr ⟨u, h, rfl⟩
      simpa only [u, Equiv.apply_symm_apply] using hm)
    have hmap : insert w (I.map (shiftEquiv c).toEmbedding) = (insert u I).map (shiftEquiv c).toEmbedding := by
      have huw : (shiftEquiv c).toEmbedding u = w := (shiftEquiv c).apply_symm_apply w
      rw [Finset.map_insert, huw]
    rw [hmap, mapCirc_eval]
    exact hI.2 u hu
  have hLevel2 : ∀ (p0 : Fin 13) (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      Separates E (allRows.filter fun I => Fin.castAdd 13 p0 ∈ I) → 9 ≤ E.size := by
    intro p0 E hw hsep
    let E' := mapCirc (shiftEquiv (-p0)) E
    have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 0 ∈ I) := by
      intro J hJ
      have hJf := Finset.mem_filter.mp hJ
      let I := J.map (shiftEquiv p0).toEmbedding
      have hIR : I ∈ allRows.filter (fun K => Fin.castAdd 13 p0 ∈ K) := by
        refine Finset.mem_filter.mpr ⟨shift_allRows p0 J hJf.1, ?_⟩
        have hm : (shiftEquiv p0) (Fin.castAdd 13 0) ∈ I := Finset.mem_map.mpr ⟨Fin.castAdd 13 0, hJf.2, rfl⟩
        have h0p : (shiftEquiv p0) (Fin.castAdd 13 0) = Fin.castAdd 13 p0 := by
          change shiftFn p0 (Fin.castAdd 13 0) = Fin.castAdd 13 p0
          rw [shiftFn_cast, f13_zero_add]
        exact h0p ▸ hm
      have hJeq : I.map (shiftEquiv (-p0)).toEmbedding = J := by
        ext k; simp only [I, Finset.mem_map_equiv]
        have he : (shiftEquiv p0).symm ((shiftEquiv (-p0)).symm k) = k := by
          change shiftFn (-p0) (shiftFn (- -p0) k) = k
          rw [f13_neg_neg]
          exact (shiftEquiv p0).left_inv k
        rw [he]
      have h := hShift_sep (-p0) E (allRows.filter fun K => Fin.castAdd 13 p0 ∈ K) hsep J
        (Finset.mem_image.mpr ⟨I, hIR, hJeq⟩)
      exact h
    exact hLevel2_0 E' (mapCirc_wf _ E hw) hsep'
  have hLevel3 : ∀ (p0 l0 : Fin 13), ¬ inc p0 l0 →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 p0 ∈ I ∧ Fin.natAdd 13 l0 ∈ I) → 7 ≤ E.size := by
    intro p0 l0 hni E hw hsep
    let E' := mapCirc (shiftEquiv (-p0)) E
    have hni' : ¬ inc 0 (l0 - p0) := by
      intro h
      have h1 := (inc_shift 0 (l0 - p0) p0).mpr h
      rw [f13_zero_add, f13_sub_add] at h1; exact hni h1
    have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.natAdd 13 (l0 - p0) ∈ I) := by
      intro J hJ
      have hJf := Finset.mem_filter.mp hJ
      let I := J.map (shiftEquiv p0).toEmbedding
      have hIR : I ∈ allRows.filter (fun K => Fin.castAdd 13 p0 ∈ K ∧ Fin.natAdd 13 l0 ∈ K) := by
        refine Finset.mem_filter.mpr ⟨shift_allRows p0 J hJf.1, ?_, ?_⟩
        · have hm : (shiftEquiv p0) (Fin.castAdd 13 0) ∈ I := Finset.mem_map.mpr ⟨Fin.castAdd 13 0, hJf.2.1, rfl⟩
          have h0p : (shiftEquiv p0) (Fin.castAdd 13 0) = Fin.castAdd 13 p0 := by
            change shiftFn p0 (Fin.castAdd 13 0) = Fin.castAdd 13 p0; rw [shiftFn_cast, f13_zero_add]
          exact h0p ▸ hm
        · have hm : (shiftEquiv p0) (Fin.natAdd 13 (l0 - p0)) ∈ I :=
            Finset.mem_map.mpr ⟨Fin.natAdd 13 (l0 - p0), hJf.2.2, rfl⟩
          have hlp : (shiftEquiv p0) (Fin.natAdd 13 (l0 - p0)) = Fin.natAdd 13 l0 := by
            change shiftFn p0 (Fin.natAdd 13 (l0 - p0)) = Fin.natAdd 13 l0
            rw [shiftFn_nat, f13_sub_add]
          exact hlp ▸ hm
      have hJeq : I.map (shiftEquiv (-p0)).toEmbedding = J := by
        ext k; simp only [I, Finset.mem_map_equiv]
        have he : (shiftEquiv p0).symm ((shiftEquiv (-p0)).symm k) = k := by
          change shiftFn (-p0) (shiftFn (- -p0) k) = k; rw [f13_neg_neg]; exact (shiftEquiv p0).left_inv k
        rw [he]
      exact hShift_sep (-p0) E _ hsep J (Finset.mem_image.mpr ⟨I, hIR, hJeq⟩)
    exact hLevel3_0 (l0 - p0) hni' E' (mapCirc_wf _ E hw) hsep'
  have hLevel4 : ∀ (p1 p2 : Fin 13), p1 ≠ p2 →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 p1 ∈ I ∧ Fin.castAdd 13 p2 ∈ I) → 6 ≤ E.size := by
    intro p1 p2 hne E hw hsep
    let E' := mapCirc (shiftEquiv (-p1)) E
    have hne' : p2 - p1 ≠ 0 := fun h => hne ((f13_sub_zero p2 p1).mp h).symm
    have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 (p2 - p1) ∈ I) := by
      intro J hJ
      have hJf := Finset.mem_filter.mp hJ
      let I := J.map (shiftEquiv p1).toEmbedding
      have hIR : I ∈ allRows.filter (fun K => Fin.castAdd 13 p1 ∈ K ∧ Fin.castAdd 13 p2 ∈ K) := by
        refine Finset.mem_filter.mpr ⟨shift_allRows p1 J hJf.1, ?_, ?_⟩
        · have hm : (shiftEquiv p1) (Fin.castAdd 13 0) ∈ I := Finset.mem_map.mpr ⟨Fin.castAdd 13 0, hJf.2.1, rfl⟩
          have h0p : (shiftEquiv p1) (Fin.castAdd 13 0) = Fin.castAdd 13 p1 := by
            change shiftFn p1 (Fin.castAdd 13 0) = Fin.castAdd 13 p1; rw [shiftFn_cast, f13_zero_add]
          exact h0p ▸ hm
        · have hm : (shiftEquiv p1) (Fin.castAdd 13 (p2 - p1)) ∈ I :=
            Finset.mem_map.mpr ⟨Fin.castAdd 13 (p2 - p1), hJf.2.2, rfl⟩
          have hpp : (shiftEquiv p1) (Fin.castAdd 13 (p2 - p1)) = Fin.castAdd 13 p2 := by
            change shiftFn p1 (Fin.castAdd 13 (p2 - p1)) = Fin.castAdd 13 p2
            rw [shiftFn_cast, f13_sub_add]
          exact hpp ▸ hm
      have hJeq : I.map (shiftEquiv (-p1)).toEmbedding = J := by
        ext k; simp only [I, Finset.mem_map_equiv]
        have he : (shiftEquiv p1).symm ((shiftEquiv (-p1)).symm k) = k := by
          change shiftFn (-p1) (shiftFn (- -p1) k) = k; rw [f13_neg_neg]; exact (shiftEquiv p1).left_inv k
        rw [he]
      exact hShift_sep (-p1) E _ hsep J (Finset.mem_image.mpr ⟨I, hIR, hJeq⟩)
    exact hLevel4_0 (p2 - p1) hne' E' (mapCirc_wf _ E hw) hsep'

  have hMainBounds : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      (∀ i, Disjoint (E.leftVars i) (E.rightVars i)) → Separates E allRows →
      11 ≤ E.size ∧
      (∀ p : Fin 13, (Finset.univ.filter fun i : Fin E.size =>
          Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i).card + 9 ≤ E.size) ∧
      (∀ p l : Fin 13, ¬ inc p l → (Finset.univ.filter fun i : Fin E.size =>
          Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i ∨
          Fin.natAdd 13 l ∈ E.leftVars i ∨ Fin.natAdd 13 l ∈ E.rightVars i).card + 7 ≤ E.size) ∧
      (∀ p1 p2 : Fin 13, p1 ≠ p2 → (Finset.univ.filter fun i : Fin E.size =>
          Fin.castAdd 13 p1 ∈ E.leftVars i ∨ Fin.castAdd 13 p1 ∈ E.rightVars i ∨
          Fin.castAdd 13 p2 ∈ E.leftVars i ∨ Fin.castAdd 13 p2 ∈ E.rightVars i).card + 6 ≤ E.size) := by
    intro E hw hdisj hsep
    have hdegP : ∀ p : Fin 13, (Finset.univ.filter fun i : Fin E.size =>
        Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i).card + 9 ≤ E.size := by
      intro p
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices E hw {Fin.castAdd 13 p}
      have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 p ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hsub : ({Fin.castAdd 13 p} : Finset (Fin 26)) ⊆ I := Finset.singleton_subset_iff.mpr hf.2
        refine ⟨(heq I hsub).trans (hsep I hf.1).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hsep I hf.1).2 w hw)
      have h9 : 9 ≤ E'.size := hLevel2 p E' hw' hsep'
      have hfeq : (Finset.univ.filter fun i : Fin E.size =>
          ∃ v ∈ ({Fin.castAdd 13 p} : Finset (Fin 26)), v ∈ E.leftVars i ∨ v ∈ E.rightVars i) =
          (Finset.univ.filter fun i : Fin E.size =>
            Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left]
      rw [hfeq] at hbd
      omega
    have hpairPL : ∀ p l : Fin 13, ¬ inc p l → (Finset.univ.filter fun i : Fin E.size =>
        Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i ∨
        Fin.natAdd 13 l ∈ E.leftVars i ∨ Fin.natAdd 13 l ∈ E.rightVars i).card + 7 ≤ E.size := by
      intro p l hni
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices E hw {Fin.castAdd 13 p, Fin.natAdd 13 l}
      have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 p ∈ I ∧ Fin.natAdd 13 l ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hsub : ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26)) ⊆ I :=
          Finset.insert_subset hf.2.1 (Finset.singleton_subset_iff.mpr hf.2.2)
        refine ⟨(heq I hsub).trans (hsep I hf.1).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hsep I hf.1).2 w hw)
      have h7 : 7 ≤ E'.size := hLevel3 p l hni E' hw' hsep'
      have hfeq : (Finset.univ.filter fun i : Fin E.size =>
          ∃ v ∈ ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26)), v ∈ E.leftVars i ∨ v ∈ E.rightVars i) =
          (Finset.univ.filter fun i : Fin E.size =>
            Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i ∨
            Fin.natAdd 13 l ∈ E.leftVars i ∨ Fin.natAdd 13 l ∈ E.rightVars i) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]; tauto
      rw [hfeq] at hbd
      omega
    have hpairPP : ∀ p1 p2 : Fin 13, p1 ≠ p2 → (Finset.univ.filter fun i : Fin E.size =>
        Fin.castAdd 13 p1 ∈ E.leftVars i ∨ Fin.castAdd 13 p1 ∈ E.rightVars i ∨
        Fin.castAdd 13 p2 ∈ E.leftVars i ∨ Fin.castAdd 13 p2 ∈ E.rightVars i).card + 6 ≤ E.size := by
      intro p1 p2 hne
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices E hw {Fin.castAdd 13 p1, Fin.castAdd 13 p2}
      have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 p1 ∈ I ∧ Fin.castAdd 13 p2 ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hsub : ({Fin.castAdd 13 p1, Fin.castAdd 13 p2} : Finset (Fin 26)) ⊆ I :=
          Finset.insert_subset hf.2.1 (Finset.singleton_subset_iff.mpr hf.2.2)
        refine ⟨(heq I hsub).trans (hsep I hf.1).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hsep I hf.1).2 w hw)
      have h6 : 6 ≤ E'.size := hLevel4 p1 p2 hne E' hw' hsep'
      have hfeq : (Finset.univ.filter fun i : Fin E.size =>
          ∃ v ∈ ({Fin.castAdd 13 p1, Fin.castAdd 13 p2} : Finset (Fin 26)), v ∈ E.leftVars i ∨ v ∈ E.rightVars i) =
          (Finset.univ.filter fun i : Fin E.size =>
            Fin.castAdd 13 p1 ∈ E.leftVars i ∨ Fin.castAdd 13 p1 ∈ E.rightVars i ∨
            Fin.castAdd 13 p2 ∈ E.leftVars i ∨ Fin.castAdd 13 p2 ∈ E.rightVars i) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]; tauto
      rw [hfeq] at hbd
      omega
    have h11 : 11 ≤ E.size := by
      by_contra! hlt
      have hsz : E.size ≤ 10 := by omega
      let Z : Finset (Fin 26) := Finset.univ.image (Fin.castAdd 13)
      have hZcard : Z.card = 13 := by
        have hinj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := fun a b h => Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val h)
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      obtain ⟨hPin, hPout, _, hPsame, hPopp⟩ := hL1_geom
      have hZle := card_le_size_of_deg_le_one E allRows Z hsep
        (fun z hz => by
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨rc, _, hpt⟩ := hPin p
          exact ⟨rowSet rc, Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, (mem_rowSet_cast rc p).mpr hpt⟩)
        (fun z hz => by
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨rc, _, hpf⟩ := hPout p
          exact ⟨rowSet rc, Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, (fun hmem => by have ht := (mem_rowSet_cast rc p).mp hmem; dsimp only [rowP] at ht; rw [hpf] at ht; cases ht)⟩)
        (fun z1 hz1 z2 hz2 hne => by
          obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp hz1
          obtain ⟨p2, _, rfl⟩ := Finset.mem_image.mp hz2
          have hpn : p1 ≠ p2 := fun h => hne (congrArg (Fin.castAdd 13) h)
          obtain ⟨rc, _, h1, h2⟩ := hPsame p1 p2 hpn
          exact ⟨rowSet rc, Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩,
            (mem_rowSet_cast rc p1).mpr h1, (fun hmem => by have ht := (mem_rowSet_cast rc p2).mp hmem; dsimp only [rowP] at ht; rw [h2] at ht; cases ht)⟩)
        (fun z1 hz1 z2 hz2 hne => by
          obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp hz1
          obtain ⟨p2, _, rfl⟩ := Finset.mem_image.mp hz2
          have hpn : p1 ≠ p2 := fun h => hne (congrArg (Fin.castAdd 13) h)
          obtain ⟨rc, _, h1, h2⟩ := hPopp p1 p2 hpn
          exact ⟨rowSet rc, Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩,
            (fun hmem => by have ht := (mem_rowSet_cast rc p1).mp hmem; dsimp only [rowP] at ht; rw [h1] at ht; cases ht),
            (fun hmem => by have ht := (mem_rowSet_cast rc p2).mp hmem; dsimp only [rowP] at ht; rw [h2] at ht; cases ht)⟩)
        (fun z hz => by
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
          rw [(litSet_touch_card E hdisj (Fin.castAdd 13 p)).1]
          have h9 := hdegP p
          omega)
      omega
    exact ⟨h11, hdegP, hpairPL, hpairPP⟩

  have hSepPull (e : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26)
      (S R : Finset (Finset (Fin 26))) (hs : Separates E S)
      (hh : ∀ J ∈ R, J.map e.toEmbedding ∈ S) : Separates (mapCirc e.symm E) R := by
    have evalPull (V : Finset (Fin 26)) :
        (mapCirc e.symm E).eval V = E.eval (V.map e.toEmbedding) := by
      have hh' : (V.map e.toEmbedding).map e.symm.toEmbedding = V := by
        ext k; simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
      have he := mapCirc_eval e.symm E (V.map e.toEmbedding)
      rw [hh'] at he
      exact he
    intro J hJ
    have h := hs _ (hh _ hJ)
    refine ⟨(evalPull J).trans h.1, ?_⟩
    intro w hw
    rw [evalPull, Finset.map_insert]
    apply h.2
    simpa only [Finset.mem_map_equiv, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using hw

  let tripleDF (k : Fin 26) : Fin 26 :=
    if h : k.val < 13 then Fin.natAdd 13 (-⟨k.val, h⟩)
    else Fin.castAdd 13 (-⟨k.val-13, by omega⟩)
  have tripleDFP : ∀ q : Fin 13, tripleDF (Fin.castAdd 13 q) = Fin.natAdd 13 (-q) := by
    decide +kernel
  have tripleDFL : ∀ m : Fin 13, tripleDF (Fin.natAdd 13 m) = Fin.castAdd 13 (-m) := by
    decide +kernel
  have tripleDFInv : ∀ k : Fin 26, tripleDF (tripleDF k) = k := by decide +kernel
  let tripleDual : Fin 26 ≃ Fin 26 := ⟨tripleDF, tripleDF, tripleDFInv, tripleDFInv⟩
  have dual_allRows : ∀ J ∈ allRows, J.map tripleDual.toEmbedding ∈ allRows := by
    intro J hJ
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨t, ht⟩ := PEqualNP.Outside.L_meta_17461.pg3DualOrbit s
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_univ _, ?_⟩
    ext k; rw [Finset.mem_map_equiv]
    by_cases h : k.val < 13
    · let q : Fin 13 := ⟨k.val,h⟩
      have hk : k = Fin.castAdd 13 q := Fin.ext rfl
      rw [hk, show tripleDual.symm (Fin.castAdd 13 q) = _ from tripleDFP q,
        mem_rowSet_cast, mem_rowSet_nat]
      have eqv : rowP t q = rowW s (-q) := (ht q).1
      rw [eqv]
    · let m : Fin 13 := ⟨k.val-13,by omega⟩
      have hk : k = Fin.natAdd 13 m := Fin.ext (by dsimp [m]; omega)
      rw [hk, show tripleDual.symm (Fin.natAdd 13 m) = _ from tripleDFL m,
        mem_rowSet_nat, mem_rowSet_cast]
      have eqv : rowW t m = rowP s (-m) := (ht m).2
      rw [eqv]
  have dual_rows_eq : (allRows.image fun J => J.map tripleDual.toEmbedding) = allRows := by
    ext J; constructor
    · rintro h; obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp h
      exact dual_allRows K hK
    · intro hJ
      refine Finset.mem_image.mpr ⟨J.map tripleDual.toEmbedding, dual_allRows J hJ, ?_⟩
      ext k
      simp only [Finset.mem_map_equiv]
      change tripleDF (tripleDF k) ∈ J ↔ _
      rw [tripleDFInv]

  have hPairPtLB := hLevel4
  have hPairLnLB (l m : Fin 13) (hne : l ≠ m)
      (E : PEqualNP.AndCount.AndCountCircuit 26) (hw : E.WellFormed)
      (hs : Separates E (allRows.filter fun K => Fin.natAdd 13 l ∈ K ∧ Fin.natAdd 13 m ∈ K)) :
      6 ≤ E.size := by
    apply hLevel4 (-l) (-m) (fun h => hne ((f13_neg_inj _ _).1 h))
      (mapCirc tripleDual.symm E) (mapCirc_wf _ E hw)
    apply hSepPull tripleDual E _ _ hs
    intro K hK
    obtain ⟨hk,h1,h2⟩ := Finset.mem_filter.mp hK
    refine Finset.mem_filter.mpr ⟨dual_allRows K hk, ?_, ?_⟩
    · rw [Finset.mem_map_equiv]; change tripleDF (Fin.natAdd 13 l) ∈ K
      rw [tripleDFL]; exact h1
    · rw [Finset.mem_map_equiv]; change tripleDF (Fin.natAdd 13 m) ∈ K
      rw [tripleDFL]; exact h2

  have hTriplePPLB (p q l : Fin 13) (hne : q ≠ p) (hpl : ¬ inc p l) (hql : ¬ inc q l)
      (E : PEqualNP.AndCount.AndCountCircuit 26) (hw : E.WellFormed)
      (hs : Separates E (allRows.filter fun K =>
        Fin.castAdd 13 p ∈ K ∧ Fin.castAdd 13 q ∈ K ∧ Fin.natAdd 13 l ∈ K)) :
      5 ≤ E.size := by
    have h0l : ¬ inc 0 (l-p) := by simpa only [sub_self] using (inc_sub p l p).not.mpr hpl
    apply hLevel5_0 (q-p) (l-p) (fun h => hne ((f13_sub_zero _ _).1 h)) h0l
      ((inc_sub q l p).not.mpr hql) (mapCirc (shiftEquiv p).symm E) (mapCirc_wf _ E hw)
    apply hSepPull (shiftEquiv p) E _ _ hs
    intro K hK
    obtain ⟨hk,h1,h2,h3⟩ := Finset.mem_filter.mp hK
    have mem {v : Fin 26} (hv : v ∈ K) : (shiftEquiv p) v ∈ K.map (shiftEquiv p).toEmbedding :=
      Finset.mem_map.mpr ⟨v,hv,rfl⟩
    have sp (x : Fin 13) : (shiftEquiv p) (Fin.castAdd 13 x) = Fin.castAdd 13 (x+p) := shiftFn_cast p x
    have sl (x : Fin 13) : (shiftEquiv p) (Fin.natAdd 13 x) = Fin.natAdd 13 (x+p) := shiftFn_nat p x
    refine Finset.mem_filter.mpr ⟨shift_allRows p K hk, ?_, ?_, ?_⟩
    · simpa only [sp,zero_add] using mem h1
    · simpa only [sp,f13_sub_add] using mem h2
    · simpa only [sl,f13_sub_add] using mem h3

  have hTripleLB (p l : Fin 13) (hpl : ¬ inc p l) (v : Fin 26)
      (act : (∃ q, v = Fin.castAdd 13 q ∧ q ≠ p ∧ ¬ inc q l) ∨
        (∃ m, v = Fin.natAdd 13 m ∧ m ≠ l ∧ ¬ inc p m))
      (E : PEqualNP.AndCount.AndCountCircuit 26) (hw : E.WellFormed)
      (hs : Separates E (allRows.filter fun K =>
        Fin.castAdd 13 p ∈ K ∧ Fin.natAdd 13 l ∈ K ∧ v ∈ K)) : 5 ≤ E.size := by
    rcases act with ⟨q,rfl,hq,hql⟩ | ⟨m,rfl,hm,hpm⟩
    · apply hTriplePPLB p q l hq hpl hql E hw
      intro K hK
      obtain ⟨hk,h1,h2,h3⟩ := Finset.mem_filter.mp hK
      exact hs K (Finset.mem_filter.mpr ⟨hk,h1,h3,h2⟩)
    · apply hTriplePPLB (-l) (-m) (-p) (fun h => hm ((f13_neg_inj _ _).1 h))
        ((inc_neg p l).not.mpr hpl) ((inc_neg p m).not.mpr hpm)
        (mapCirc tripleDual.symm E) (mapCirc_wf _ E hw)
      apply hSepPull tripleDual E _ _ hs
      intro K hK
      obtain ⟨hk,h1,h2,h3⟩ := Finset.mem_filter.mp hK
      refine Finset.mem_filter.mpr ⟨dual_allRows K hk, ?_, ?_, ?_⟩
      · rw [Finset.mem_map_equiv]; change tripleDF (Fin.castAdd 13 p) ∈ K
        rw [tripleDFP]; exact h3
      · rw [Finset.mem_map_equiv]; change tripleDF (Fin.natAdd 13 l) ∈ K
        rw [tripleDFL]; exact h1
      · rw [Finset.mem_map_equiv]; change tripleDF (Fin.natAdd 13 m) ∈ K
        rw [tripleDFL]; exact h2

  dsimp only
  intro D hD_wf hD_disj hD_pos hD_neg
  have hSep_of_pos_neg : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26),
      (∀ p l : Fin 13, inc p l → E.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
      (∀ P : Finset (Fin 13),
        (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ inc q l) ∧ inc p l) →
        ((¬∃ l : Fin 13, ∀ p ∈ P, inc p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ inc q l) → inc p l) →
        E.eval (liftRow P) = false) →
      Separates E allRows := by
    intro E hEp hEn I hI
    obtain ⟨rc, _, rfl⟩ := Finset.mem_image.mp hI
    refine ⟨hEn (rowPSet rc) (row_max rc) (row_generic rc), ?_⟩
    intro w hw
    by_cases hlt : w.val < 13
    · let p : Fin 13 := ⟨w.val, hlt⟩
      have hw_eq : w = Fin.castAdd 13 p := Fin.ext rfl
      rw [hw_eq] at hw ⊢
      have hpn : p ∉ rowPSet rc := fun h => hw ((mem_rowSet_cast rc p).mpr (Finset.mem_filter.mp h).2)
      obtain ⟨l, hlW, hinc⟩ := row_max rc p hpn
      have hlI : Fin.natAdd 13 l ∈ rowSet rc := (mem_rowSet_nat rc l).mpr ((rowW_iff rc l).mpr hlW)
      have hsub : ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26)) ⊆ insert (Fin.castAdd 13 p) (rowSet rc) :=
        Finset.insert_subset (Finset.mem_insert_self _ _) (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem hlI))
      exact eval_mono E hsub (hEp p l hinc)
    · let l : Fin 13 := ⟨w.val - 13, by omega⟩
      have hw_eq : w = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      rw [hw_eq] at hw ⊢
      have hln : ¬ ∀ q ∈ rowPSet rc, ¬ inc q l := fun h =>
        hw ((mem_rowSet_nat rc l).mpr ((rowW_iff rc l).mpr h))
      push Not at hln
      obtain ⟨p, hp, hinc⟩ := hln
      have hpI : Fin.castAdd 13 p ∈ rowSet rc := (mem_rowSet_cast rc p).mpr (Finset.mem_filter.mp hp).2
      have hsub : ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26)) ⊆ insert (Fin.natAdd 13 l) (rowSet rc) :=
        Finset.insert_subset (Finset.mem_insert_of_mem hpI) (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      exact eval_mono E hsub (hEp p l hinc)
  have hD_sep : Separates D allRows := hSep_of_pos_neg D hD_pos hD_neg
  have hD_outVars : D.outVars = ∅ := by
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    obtain ⟨hPin, _, hLin, _, _⟩ := hL1_geom
    by_cases hlt : v.val < 13
    · let p : Fin 13 := ⟨v.val, hlt⟩
      have hv_eq : v = Fin.castAdd 13 p := Fin.ext rfl
      obtain ⟨rc, _, hpt⟩ := hPin p
      have hm : v ∈ rowSet rc := hv_eq ▸ (mem_rowSet_cast rc p).mpr hpt
      have ht : D.eval (rowSet rc) = true := decide_eq_true (Or.inl ⟨v, hv, hm⟩)
      have hf := (hD_sep (rowSet rc) (Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩)).1
      rw [hf] at ht; cases ht
    · let l : Fin 13 := ⟨v.val - 13, by omega⟩
      have hv_eq : v = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      obtain ⟨rc, _, hlt'⟩ := hLin l
      have hm : v ∈ rowSet rc := hv_eq ▸ (mem_rowSet_nat rc l).mpr hlt'
      have ht : D.eval (rowSet rc) = true := decide_eq_true (Or.inl ⟨v, hv, hm⟩)
      have hf := (hD_sep (rowSet rc) (Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩)).1
      rw [hf] at ht; cases ht
  obtain ⟨hD_ge11, hD_degP, hD_pairPL, hD_pairPP⟩ := hMainBounds D hD_wf hD_disj hD_sep

  let dualFn (k : Fin 26) : Fin 26 :=
    if h : k.val < 13 then Fin.natAdd 13 (-⟨k.val, h⟩)
    else Fin.castAdd 13 (-⟨k.val - 13, by omega⟩)
  have dualFn_cast : ∀ p : Fin 13, dualFn (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := by
    intro p
    have hlt : (Fin.castAdd 13 p).val < 13 := p.isLt
    simp only [dualFn, hlt, ↓reduceDIte]
    rfl
  have dualFn_nat : ∀ l : Fin 13, dualFn (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := by
    intro l
    have hlt : ¬ (Fin.natAdd 13 l).val < 13 := by simp only [Fin.val_natAdd, not_lt]; omega
    simp only [dualFn, hlt, ↓reduceDIte]
    have h1 : (⟨(Fin.natAdd 13 l).val - 13, by omega⟩ : Fin 13) = l :=
      Fin.ext (by simp only [Fin.val_natAdd, Nat.add_sub_cancel_left])
    rw [h1]
  let dualEquiv : Fin 26 ≃ Fin 26 :=
    { toFun := dualFn
      invFun := dualFn
      left_inv := by
        intro k
        by_cases h : k.val < 13
        · let p : Fin 13 := ⟨k.val, h⟩
          have hk : k = Fin.castAdd 13 p := Fin.ext rfl
          rw [hk, dualFn_cast, dualFn_nat, f13_neg_neg]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
          rw [hk, dualFn_nat, dualFn_cast, f13_neg_neg]
      right_inv := by
        intro k
        by_cases h : k.val < 13
        · let p : Fin 13 := ⟨k.val, h⟩
          have hk : k = Fin.castAdd 13 p := Fin.ext rfl
          rw [hk, dualFn_cast, dualFn_nat, f13_neg_neg]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
          rw [hk, dualFn_nat, dualFn_cast, f13_neg_neg] }
  let Ddual := mapCirc dualEquiv D
  have hDdual_wf : Ddual.WellFormed := mapCirc_wf dualEquiv D hD_wf
  have hDdual_disj : ∀ i, Disjoint (Ddual.leftVars i) (Ddual.rightVars i) := fun i =>
    Finset.disjoint_map dualEquiv.toEmbedding |>.mpr (hD_disj i)
  have hDdual_pos : ∀ p l : Fin 13, inc p l → Ddual.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true := by
    intro p l hinc
    have hmap : ({Fin.castAdd 13 (-l), Fin.natAdd 13 (-p)} : Finset (Fin 26)).map dualEquiv.toEmbedding =
        {Fin.castAdd 13 p, Fin.natAdd 13 l} := by
      ext k
      simp only [Finset.mem_map, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h; rcases h with ⟨u, hu, rfl⟩
        rcases hu with rfl | rfl
        · right; change dualFn (Fin.castAdd 13 (-l)) = _; rw [dualFn_cast, f13_neg_neg]
        · left; change dualFn (Fin.natAdd 13 (-p)) = _; rw [dualFn_nat, f13_neg_neg]
      · intro h; rcases h with rfl | rfl
        · refine ⟨Fin.natAdd 13 (-p), Or.inr rfl, ?_⟩
          change dualFn (Fin.natAdd 13 (-p)) = _; rw [dualFn_nat, f13_neg_neg]
        · refine ⟨Fin.castAdd 13 (-l), Or.inl rfl, ?_⟩
          change dualFn (Fin.castAdd 13 (-l)) = _; rw [dualFn_cast, f13_neg_neg]
    rw [← hmap, mapCirc_eval]
    exact hD_pos (-l) (-p) ((inc_neg p l).mpr hinc)
  have hDdual_neg : ∀ P : Finset (Fin 13),
      (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ inc q l) ∧ inc p l) →
      ((¬∃ l : Fin 13, ∀ p ∈ P, inc p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ inc q l) → inc p l) →
      Ddual.eval (liftRow P) = false := by
    intro P hmx hgen
    let P' : Finset (Fin 13) := Finset.univ.filter fun q : Fin 13 => ∀ p ∈ P, ¬ inc p (-q)
    have hW' : ∀ l : Fin 13, (∀ q ∈ P', ¬ inc q l) ↔ -l ∈ P := by
      intro l
      constructor
      · intro hall
        by_contra hn
        obtain ⟨w, hw, hinc⟩ := hmx (-l) hn
        have hwm : -w ∈ P' := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro p hp; rw [f13_neg_neg]; exact hw p hp
        exact hall (-w) hwm (by simpa only [f13_neg_neg] using (inc_neg (-l) w).mpr hinc)
      · intro hml q hq hinc
        have hq' := (Finset.mem_filter.mp hq).2 (-l) hml
        have h1 : inc (-l) (-q) := (inc_neg q l).mpr hinc
        exact hq' h1
    have hmx' : ∀ q ∉ P', ∃ l : Fin 13, (∀ r ∈ P', ¬ inc r l) ∧ inc q l := by
      intro q hqn
      have hex : ∃ p ∈ P, inc p (-q) := by
        by_contra h; push Not at h
        exact hqn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      obtain ⟨p, hp, hinc⟩ := hex
      refine ⟨-p, (hW' (-p)).mpr (by rw [f13_neg_neg]; exact hp), ?_⟩
      simpa only [f13_neg_neg] using (inc_neg p (-q)).mpr hinc
    have hgen' : (¬∃ l : Fin 13, ∀ q ∈ P', inc q l) ∧
        ¬∃ q : Fin 13, ∀ l : Fin 13, (∀ r ∈ P', ¬ inc r l) → inc q l := by
      constructor
      · intro hex; rcases hex with ⟨l, hl⟩
        apply hgen.2
        refine ⟨-l, fun w hw => ?_⟩
        have hwm : -w ∈ P' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => by rw [f13_neg_neg]; exact hw p hp⟩
        exact (inc_neg (-l) w).mp (by simpa only [f13_neg_neg] using hl (-w) hwm)
      · intro hex; rcases hex with ⟨q, hq⟩
        apply hgen.1
        refine ⟨-q, fun p hp => ?_⟩
        have hinc : inc q (-p) := hq (-p) ((hW' (-p)).mpr (by rw [f13_neg_neg]; exact hp))
        exact (inc_neg p (-q)).mp (by simpa only [f13_neg_neg] using hinc)
    have hmap : (liftRow P').map dualEquiv.toEmbedding = liftRow P := by
      ext k
      rw [Finset.mem_map_equiv]
      by_cases hlt : k.val < 13
      · let p : Fin 13 := ⟨k.val, hlt⟩
        have hk : k = Fin.castAdd 13 p := Fin.ext rfl
        rw [hk]
        have hsym : dualEquiv.symm (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := dualFn_cast p
        rw [hsym]
        simp only [liftRow, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨q, _, heq⟩
            have hv := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
          · rcases h2 with ⟨l, heq, hall⟩
            have hlp : l = -p := by
              have hv := congrArg Fin.val heq; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
            subst hlp
            have hpP : p ∈ P := by simpa only [f13_neg_neg] using (hW' (-p)).mp hall
            exact Or.inl ⟨p, hpP, rfl⟩
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨p', hp', heq⟩
            have hpp : p = p' := Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val heq)
            subst hpp
            exact Or.inr ⟨-p, rfl, (hW' (-p)).mpr (by simpa only [f13_neg_neg] using hp')⟩
          · rcases h2 with ⟨l, heq, _⟩
            have hv := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
      · let l : Fin 13 := ⟨k.val - 13, by omega⟩
        have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
        rw [hk]
        have hsym : dualEquiv.symm (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := dualFn_nat l
        rw [hsym]
        simp only [liftRow, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨q, hq, heq⟩
            have hql : -l = q := Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val heq)
            rw [← hql] at hq
            have hq' := (Finset.mem_filter.mp hq).2
            exact Or.inr ⟨l, rfl, fun p hp => by simpa only [f13_neg_neg] using hq' p hp⟩
          · rcases h2 with ⟨w, heq, _⟩
            have hv := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨p, _, heq⟩
            have hv := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
          · rcases h2 with ⟨l', heq, hall⟩
            have hll : l = l' := by
              have hv := congrArg Fin.val heq; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
            subst hll
            exact Or.inl ⟨-l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => by
              rw [f13_neg_neg]; exact hall p hp⟩, rfl⟩
    rw [← hmap, mapCirc_eval]
    exact hD_neg P' hmx' hgen'
  have hDdual_sep : Separates Ddual allRows := hSep_of_pos_neg Ddual hDdual_pos hDdual_neg
  obtain ⟨_, hDdual_degP, _, hDdual_pairPP⟩ := hMainBounds Ddual hDdual_wf hDdual_disj hDdual_sep
  have hD_degL : ∀ l : Fin 13, (Finset.univ.filter fun i : Fin D.size =>
      Fin.natAdd 13 l ∈ D.leftVars i ∨ Fin.natAdd 13 l ∈ D.rightVars i).card + 9 ≤ D.size := by
    intro l
    have h := hDdual_degP (-l)
    have heq : (Finset.univ.filter fun i : Fin Ddual.size =>
        Fin.castAdd 13 (-l) ∈ Ddual.leftVars i ∨ Fin.castAdd 13 (-l) ∈ Ddual.rightVars i) =
        (Finset.univ.filter fun i : Fin D.size =>
          Fin.natAdd 13 l ∈ D.leftVars i ∨ Fin.natAdd 13 l ∈ D.rightVars i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ddual, mapCirc, Finset.mem_map_equiv]
      have hsym : dualEquiv.symm (Fin.castAdd 13 (-l)) = Fin.natAdd 13 l := by
        change dualFn (Fin.castAdd 13 (-l)) = _; rw [dualFn_cast, f13_neg_neg]
      rw [hsym]
    simpa only [heq] using h
  have hD_pairLL : ∀ l1 l2 : Fin 13, l1 ≠ l2 → (Finset.univ.filter fun i : Fin D.size =>
      Fin.natAdd 13 l1 ∈ D.leftVars i ∨ Fin.natAdd 13 l1 ∈ D.rightVars i ∨
      Fin.natAdd 13 l2 ∈ D.leftVars i ∨ Fin.natAdd 13 l2 ∈ D.rightVars i).card + 6 ≤ D.size := by
    intro l1 l2 hne
    have h := hDdual_pairPP (-l1) (-l2) (fun h => hne ((f13_neg_inj l1 l2).mp h))
    have heq : (Finset.univ.filter fun i : Fin Ddual.size =>
        Fin.castAdd 13 (-l1) ∈ Ddual.leftVars i ∨ Fin.castAdd 13 (-l1) ∈ Ddual.rightVars i ∨
        Fin.castAdd 13 (-l2) ∈ Ddual.leftVars i ∨ Fin.castAdd 13 (-l2) ∈ Ddual.rightVars i) =
        (Finset.univ.filter fun i : Fin D.size =>
          Fin.natAdd 13 l1 ∈ D.leftVars i ∨ Fin.natAdd 13 l1 ∈ D.rightVars i ∨
          Fin.natAdd 13 l2 ∈ D.leftVars i ∨ Fin.natAdd 13 l2 ∈ D.rightVars i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ddual, mapCirc, Finset.mem_map_equiv]
      have h1 : dualEquiv.symm (Fin.castAdd 13 (-l1)) = Fin.natAdd 13 l1 := by
        change dualFn (Fin.castAdd 13 (-l1)) = _; rw [dualFn_cast, f13_neg_neg]
      have h2 : dualEquiv.symm (Fin.castAdd 13 (-l2)) = Fin.natAdd 13 l2 := by
        change dualFn (Fin.castAdd 13 (-l2)) = _; rw [dualFn_cast, f13_neg_neg]
      rw [h1, h2]
    simpa only [heq] using h
  have hD_degAll : ∀ v : Fin 26, (Finset.univ.filter fun i : Fin D.size =>
      v ∈ D.leftVars i ∨ v ∈ D.rightVars i).card + 9 ≤ D.size := by
    intro v
    by_cases hlt : v.val < 13
    · let p : Fin 13 := ⟨v.val, hlt⟩
      have hv : v = Fin.castAdd 13 p := Fin.ext rfl
      rw [hv]; exact hD_degP p
    · let l : Fin 13 := ⟨v.val - 13, by omega⟩
      have hv : v = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      rw [hv]; exact hD_degL l
  have hUnion_eq : ∀ (u v : Fin 26),
      (Finset.univ.filter fun i : Fin D.size => u ∈ D.leftVars i ∨ u ∈ D.rightVars i) ∪
      (Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i) =
      (Finset.univ.filter fun i : Fin D.size =>
        u ∈ D.leftVars i ∨ u ∈ D.rightVars i ∨ v ∈ D.leftVars i ∨ v ∈ D.rightVars i) := by
    intro u v; ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto

  let LB (T : Finset (Fin 26)) (k : ℕ) : Prop :=
    ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
      (∀ U, T ⊆ U → E.eval U = D.eval U) → k ≤ E.size
  have agreePair (x y : Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26)
      (he : ∀ U : Finset (Fin 26), {x,y} ⊆ U → E.eval U = D.eval U) :
      Separates E (allRows.filter fun K => x ∈ K ∧ y ∈ K) := by
    intro K hK
    obtain ⟨hm,hx,hy⟩ := Finset.mem_filter.mp hK
    have sub : ({x,y} : Finset (Fin 26)) ⊆ K := Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    exact ⟨(he _ sub).trans (hD_sep K hm).1, fun w hw =>
      (he _ (sub.trans (Finset.subset_insert _ _))).trans ((hD_sep K hm).2 w hw)⟩
  have sameLB (p q : Fin 13) (hne : p ≠ q) :
      LB {Fin.castAdd 13 p, Fin.castAdd 13 q} 6 ∧ LB {Fin.natAdd 13 p, Fin.natAdd 13 q} 6 := by
    exact ⟨fun E wf he => hPairPtLB p q hne E wf (agreePair _ _ _ he),
      fun E wf he => hPairLnLB p q hne E wf (agreePair _ _ _ he)⟩
  have crossLB (p l : Fin 13) (hn : ¬inc p l) : LB {Fin.castAdd 13 p,Fin.natAdd 13 l} 8 := by
    intro E hw hE
    let T : Finset (Fin 26) := {Fin.castAdd 13 p, Fin.natAdd 13 l}
    change ∀ U, T ⊆ U → E.eval U = D.eval U at hE
    have sepE := agreePair _ _ E hE
    have low := hLevel3 p l hn E hw sepE
    by_contra! small
    have esize : E.size = 7 := by omega
    obtain ⟨v, row, fixed, cols, activeV, edgesV⟩ :=
      pg3Relabel rowSet mem_rowSet_cast mem_rowSet_nat p l hn
    let R (r : Fin 48) := rowSet (row r)
    have inside (r : Fin 48) : T ⊆ R r :=
      Finset.insert_subset (fixed r).1 (Finset.singleton_subset_iff.mpr (fixed r).2)
    have member (r : Fin 48) : R r ∈ allRows := Finset.mem_image.mpr ⟨row r, Finset.mem_univ _, rfl⟩
    have ef : E.eval T = false := by
      apply Bool.eq_false_iff.mpr
      intro et
      have ht := eval_mono E (inside 0) et
      have hf := (sepE (R 0) (Finset.mem_filter.mpr ⟨member 0, fixed 0⟩)).1
      simp [hf] at ht
    obtain ⟨F, wfF, szF, evF⟩ := pg3Cofactor 26 E T hw ef
    obtain ⟨C, szC, wfC, disjC, singC, evC⟩ := strip_exists F wfF
    have hsz : C.size = 7 := by omega
    have sem (U : Finset (Fin 26)) : C.eval U = D.eval (T ∪ U) :=
      (evC U).trans ((evF U).trans (hE _ Finset.subset_union_left))
    have agreeC (U : Finset (Fin 26)) (hu : T ⊆ U) : C.eval U = D.eval U := by
      simpa only [Finset.union_eq_right.mpr hu] using sem U
    have sepC := agreePair _ _ C agreeC
    have capC (j : Fin 12) :
        (Finset.univ.filter fun i : Fin C.size => v j ∈ C.leftVars i ∨ v j ∈ C.rightVars i).card ≤ 2 := by
      obtain ⟨B, wfB, cost, evB⟩ := elim_vertices C wfC {v j}
      have five := hTripleLB p l hn (v j) (activeV j) B wfB (by
        intro K hK
        obtain ⟨hm,h1,h2,h3⟩ := Finset.mem_filter.mp hK
        have hk := sepC K (Finset.mem_filter.mpr ⟨hm,h1,h2⟩)
        have hsub : ({v j} : Finset (Fin 26)) ⊆ K := Finset.singleton_subset_iff.mpr h3
        exact ⟨(evB K hsub).trans hk.1, fun w hw =>
          (evB _ (hsub.trans (Finset.subset_insert w K))).trans (hk.2 w hw)⟩)
      simp only [Finset.mem_singleton,exists_eq_left] at cost
      omega
    have ng (r : Fin 48) : C.eval (R r) = false :=
      (agreeC _ (inside r)).trans (hD_sep _ (member r)).1
    have ins (r : Fin 48) (i : Fin 12) (hi : v i ∉ R r) :
        C.eval (insert (v i) (R r)) = true :=
      (agreeC _ ((inside r).trans (Finset.subset_insert _ _))).trans ((hD_sep _ (member r)).2 _ hi)
    have yes (i j : Fin 12) (hij : i < j) (he : rcData[j.val]!.1.testBit i.val = true) :
        C.eval {v i, v j} = true := by
      obtain ⟨q,m,hinc,h⟩ := edgesV i j hij he
      rw [sem]
      apply eval_mono D _ (hD_pos q m hinc)
      rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · rw [h1,h2]; exact Finset.subset_union_right
      · rw [h1,h2, Finset.pair_comm]; exact Finset.subset_union_right
    obtain ⟨O,hp,hc,ho,hr,he⟩ := pg3ModelOfCircuit C v R hsz singC disjC capC cols ng ins yes
    obtain ⟨s,t,hst,hreal,hedges⟩ := pg3RCModel O hp hc ho hr he
    have impossible := pg3SearchOfModel s t hst hreal hedges
    rw [pg3Exhaust] at impossible
    cases impossible
  refine ⟨?_, sameLB, crossLB⟩
  · refine ⟨hD_outVars, hD_ge11, hD_degAll, ?_, ?_⟩
    · intro p l hn
      rw [hUnion_eq]
      exact hD_pairPL p l hn
    · intro p q hn
      rw [hUnion_eq, hUnion_eq]
      exact ⟨hD_pairPP p q hn, hD_pairLL p q hn⟩

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461.Plane1898

open Finset

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem threeDonorsImpossible {ι : Type} [DecidableEq ι]
    (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (P L : Fin 13 → Finset ι) (p : Fin 13)
    (degp : (P p).card = 3) (pcap : ∀ q, (P q).card ≤ 3) (lcap : ∀ t, (L t).card ≤ 3)
    (rays : ((univ : Finset (Fin 13)).filter (I p)).card = 4)
    (four : ∀ t, ((univ : Finset (Fin 13)).filter (I · t)).card = 4)
    (three : ∀ q, q ≠ p →
      3 ≤ ((univ : Finset (Fin 13)).filter fun t => I q t ∧ ¬ I p t).card)
    (unique : ∀ {a b t u}, a ≠ b → I a t → I b t → I a u → I b u → t = u)
    (src targets : ι → Finset (Fin 13))
    (srcP : ∀ g q, q ∈ src g → g ∈ P q)
    (aligned : ∀ g q t, q ∈ src g → t ∈ targets g → I q t)
    (one : ∀ g, g ∉ P p → (targets g).card ≤ 1)
    (reach : ∀ q t, q ≠ p → I q t → ¬ I p t → ∃ g, q ∈ src g ∧ t ∈ targets g)
    (hit : Fin 13 → Fin 13 → ι → Prop)
    (cover : ∀ q t, I q t → ∃ g, hit q t g)
    (touchP : ∀ q t g, hit q t g → g ∈ P q)
    (touchL : ∀ q t g, hit q t g → g ∈ L t)
    (opposed : ∀ g ∈ P p, ∀ q ∈ src g, ∀ t, hit p t g → ¬ hit q t g) : False := by
  classical
  let single := (P p).filter fun g => (src g).card = 1
  let bad := single.biUnion src
  have bsize : bad.card ≤ 3 := by
    calc
      _ ≤ ∑ g ∈ single, (src g).card := card_biUnion_le
      _ = ∑ _g ∈ single, 1 := sum_congr rfl fun g hg => (mem_filter.mp hg).2
      _ = single.card := by simp
      _ ≤ (P p).card := card_le_card (filter_subset ..)
      _ = 3 := degp
  let near (q : Fin 13) := (univ : Finset (Fin 13)).filter fun t => I p t ∧ I q t
  have nearOne (q : Fin 13) (hq : q ≠ p) : (near q).card ≤ 1 := by
    apply card_le_one.mpr
    intro t ht u hu
    exact unique hq (mem_filter.mp ht).2.2 (mem_filter.mp ht).2.1
      (mem_filter.mp hu).2.2 (mem_filter.mp hu).2.1
  have blocked : ((bad.erase p).biUnion near).card ≤ 3 := by
    calc
      _ ≤ ∑ q ∈ bad.erase p, (near q).card := card_biUnion_le
      _ ≤ ∑ _q ∈ bad.erase p, 1 := sum_le_sum (fun q hq => nearOne q (ne_of_mem_erase hq))
      _ = (bad.erase p).card := by simp
      _ ≤ bad.card := card_erase_le
      _ ≤ 3 := bsize
  have pick : ¬ univ.filter (I p) ⊆ (bad.erase p).biUnion near :=
    fun h => by have := card_le_card h; omega
  obtain ⟨l, hl, hfree⟩ := Set.not_subset.mp pick
  have epl := (mem_filter.mp hl).2
  have good (q : Fin 13) (neq : q ≠ p) (hq : I q l) : q ∉ bad := by
    intro hqbad
    exact hfree (mem_biUnion.mpr ⟨q, mem_erase.mpr ⟨neq, hqbad⟩,
      mem_filter.mpr ⟨mem_univ _, epl, hq⟩⟩)
  have unit (q : Fin 13) (hq : q ∉ bad) (g : ι) (hg : q ∈ src g) :
      (targets g).card ≤ 1 := by
    by_cases hgp : g ∈ P p
    · have hns : (src g).card ≠ 1 := fun h =>
        hq (mem_biUnion.mpr ⟨g, mem_filter.mpr ⟨hgp,h⟩, hg⟩)
      have hp := card_pos.mpr ⟨q,hg⟩
      obtain ⟨w,hw,hwq⟩ := exists_mem_ne (by omega : 1 < (src g).card) q
      exact card_le_one.mpr fun t ht u hu =>
        unique hwq (aligned _ _ _ hw ht) (aligned _ _ _ hg ht)
          (aligned _ _ _ hw hu) (aligned _ _ _ hg hu)
    · exact one g hgp
  have productive (q : Fin 13) (neq : q ≠ p) (hq : I q l) (g : ι) (hg : g ∈ P q) :
      q ∈ src g ∧ ∃ t ∈ targets g, I q t ∧ ¬ I p t := by
    let T := (univ : Finset (Fin 13)).filter fun t => I q t ∧ ¬ I p t
    have size : 3 ≤ T.card := three q neq
    have get (t : ↥T) : ∃ k, q ∈ src k ∧ t.1 ∈ targets k :=
      reach q t.1 neq (mem_filter.mp t.2).2.1 (mem_filter.mp t.2).2.2
    choose k hk hv using get
    let f (t : ↥T) : ↥(P q) := ⟨k t, srcP _ _ (hk t)⟩
    have inj : Function.Injective f := by
      intro a b h
      have he : k a = k b := congrArg Subtype.val h
      apply Subtype.ext
      exact card_le_one.mp (unit q (good q neq hq) (k b) (hk b)) a.1 (he ▸ hv a) b.1 (hv b)
    have hcard : Fintype.card ↥(P q) ≤ Fintype.card ↥T := by
      simp only [Fintype.card_coe]
      exact (pcap q).trans size
    have surj := ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨inj, le_antisymm (Fintype.card_le_of_injective _ inj) hcard⟩).2
    obtain ⟨t, ht⟩ := surj ⟨g,hg⟩
    have he : k t = g := congrArg Subtype.val ht
    exact ⟨he ▸ hk t, t.1, he ▸ hv t, (mem_filter.mp t.2).2⟩
  let Q := (univ : Finset (Fin 13)).filter (I · l)
  choose f hf using fun q : ↥Q => cover q.1 l (mem_filter.mp q.2).2
  let j (q : ↥Q) : ↥(L l) := ⟨f q, touchL _ _ _ (hf q)⟩
  have inj : Function.Injective j := by
    intro x y hxy
    have he : f x = f y := congrArg Subtype.val hxy
    apply Subtype.ext
    by_contra hne
    have ey := (mem_filter.mp y.2).2
    have ex := (mem_filter.mp x.2).2
    have hx : hit x.1 l (f y) := he ▸ hf x
    by_cases xp : x.1 = p
    · have yp : y.1 ≠ p := fun h => hne (xp.trans h.symm)
      have pHit : hit p l (f y) := xp ▸ hx
      have prod := productive y.1 yp ey _ (touchP _ _ _ (hf y))
      exact opposed _ (touchP _ _ _ pHit) _ prod.1 _ pHit (hf y)
    by_cases yp : y.1 = p
    · have pHit : hit p l (f y) := yp ▸ hf y
      have prod := productive x.1 xp ex _ (touchP _ _ _ hx)
      exact opposed _ (touchP _ _ _ pHit) _ prod.1 _ pHit hx
    obtain ⟨hxs,t,ht,ext',hpt⟩ := productive x.1 xp ex _ (touchP _ _ _ hx)
    obtain ⟨hys,_⟩ := productive y.1 yp ey _ (touchP _ _ _ (hf y))
    have eq := unique hne ex ey ext' (aligned _ _ _ hys ht)
    exact hpt (eq ▸ epl)
  have hc := Fintype.card_le_of_injective j inj
  simp only [Fintype.card_coe] at hc
  change (univ.filter (I · l)).card ≤ _ at hc
  have := four l
  have := lcap l
  omega

end PEqualNP.Outside.L_meta_17461.Plane1898

namespace PEqualNP.Outside.L_meta_17461.Plane1898

open Finset PEqualNP.AndCount

abbrev donorInc (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
abbrev donorP (d : Bool) (x : Fin 13) : Fin 26 :=
  if d then Fin.natAdd 13 x else Fin.castAdd 13 x
abbrev donorL (d : Bool) (x : Fin 13) : Fin 26 := donorP (!d) x
abbrev donorI (d : Bool) (x y : Fin 13) : Prop :=
  if d then donorInc y x else donorInc x y
abbrev donorPos (D : AndCountCircuit 26) := ∀ p l : Fin 13, donorInc p l →
  D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true
abbrev donorNeg (D : AndCountCircuit 26) := ∀ P : Finset (Fin 13),
  (∀ p ∉ P, ∃ l, (∀ q ∈ P, ¬ donorInc q l) ∧ donorInc p l) →
  ((¬∃ l, ∀ p ∈ P, donorInc p l) ∧
   ¬∃ p, ∀ l, (∀ q ∈ P, ¬ donorInc q l) → donorInc p l) →
  D.eval (univ.filter fun k : Fin 26 => (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
    ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬donorInc q l) = false

private def donorMasks : List ℕ := [7405575,59244600,192832,33885824,2379913,18883684,
  12616082,9835012,724226,38807632,16892673,1595425,39977034,17597457,8462756,
  34636370,21102924,2405504,41960104,4999177,12062754,4466836,50726408,8925488,
  35718306,19939425,1210432,1871889,29622300,4286848,35685570,17376544,9634310]
private abbrev pointBit (m : ℕ) (p : Fin 13) := m.testBit p.val = true
private abbrev freeBit (m : ℕ) (l : Fin 13) := ∀ p, pointBit m p → ¬ donorInc p l
private abbrev donorOK (m : ℕ) :=
    (∀ p, ¬pointBit m p → ∃ l, freeBit m l ∧ donorInc p l) ∧
    ((¬∃ l, ∀ p, pointBit m p → donorInc p l) ∧ ¬∃ p, ∀ l, freeBit m l → donorInc p l) ∧
    (∀ k : Fin 26, m.testBit k.val = true ↔
      (∃ p, pointBit m p ∧ k = Fin.castAdd 13 p) ∨ ∃ l, k = Fin.natAdd 13 l ∧ freeBit m l) ∧
    (∀ v : Fin 26, m.testBit v.val = false →
      ∃ p l : Fin 13, donorInc p l ∧
        ((v = Fin.castAdd 13 p ∧ m.testBit (Fin.natAdd 13 l).val = true) ∨
         (v = Fin.natAdd 13 l ∧ m.testBit (Fin.castAdd 13 p).val = true)))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 2000 in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem donorRowsOK : ∀ m ∈ donorMasks, donorOK m := by
  have h : donorMasks.all (fun m => decide (donorOK m)) = true := by decide +kernel
  exact fun m hm => of_decide_eq_true (List.all_eq_true.mp h m hm)

private abbrev pd (m : ℕ) (d : Bool) (x : Fin 13) := m.testBit (donorP d x).val = true
private abbrev ld (m : ℕ) (d : Bool) (x : Fin 13) := m.testBit (donorL d x).val = true

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 2000 in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem donorMasksRealize : ∀ (d : Bool) (p : Fin 13),
    (∀ q, ∃ m ∈ donorMasks, pd m d p ∧ pd m d q) ∧
    (∀ t, ¬ donorI d p t → ∃ m ∈ donorMasks, pd m d p ∧ ld m d t) ∧
    (∀ t u, ¬ donorI d p t → ¬ donorI d p u → t ≠ u →
      (∃ m ∈ donorMasks, pd m d p ∧ ld m d t ∧ ¬ ld m d u) ∧
      ∃ m ∈ donorMasks, pd m d p ∧ ¬ ld m d t ∧ ¬ ld m d u) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem donorDualPos (D : AndCountCircuit 26) (pos : donorPos D)
    (d : Bool) (p l : Fin 13) (h : donorI d p l) :
    D.eval {donorP d p, donorL d l} = true := by
  cases d
  · exact pos _ _ h
  · exact congrArg D.eval (Finset.pair_comm (Fin.natAdd 13 p) (Fin.castAdd 13 l)) |>.trans (pos _ _ h)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem donorMono {n : ℕ} (D : AndCountCircuit n) {X Y : Finset (Fin n)}
    (hXY : X ⊆ Y) (hx : D.eval X = true) : D.eval Y = true := by
  have fuel : ∀ d (i : Fin D.size), D.gateValFuel X d i = true → D.gateValFuel Y d i = true := by
    intro d
    induction d with
    | zero => intro _ h; cases h
    | succ d ih =>
      intro i
      have side (A : Finset (Fin n)) (B : Finset (Fin D.size)) :
          AndCountCircuit.sideTrue X A B i (D.gateValFuel X d) = true →
          AndCountCircuit.sideTrue Y A B i (D.gateValFuel Y d) = true := by
        simp only [AndCountCircuit.sideTrue,decide_eq_true_eq]
        exact fun h => h.elim (fun ⟨a,ha,hx⟩ => Or.inl ⟨a,ha,hXY hx⟩)
          (fun ⟨j,hj,hlt,hv⟩ => Or.inr ⟨j,hj,hlt,ih j hv⟩)
      simp only [AndCountCircuit.gateValFuel,Bool.and_eq_true]
      exact fun h => ⟨side _ _ h.1,side _ _ h.2⟩
  simp only [AndCountCircuit.eval,decide_eq_true_eq] at hx ⊢
  exact hx.elim (fun ⟨v,hv,hx⟩ => Or.inl ⟨v,hv,hXY hx⟩)
    (fun ⟨g,hg,hx⟩ => Or.inr ⟨g,hg,fuel D.size g hx⟩)

private def maskRow (m : ℕ) : Finset (Fin 26) := univ.filter fun v => m.testBit v.val = true
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem atRow (m : ℕ) (v : Fin 26) : v ∈ maskRow m ↔ m.testBit v.val = true := by
  simp [maskRow]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem donorMaskSem (D : AndCountCircuit 26) (pos : donorPos D) (neg : donorNeg D)
    (m : ℕ) (hm : m ∈ donorMasks) :
    D.eval (maskRow m) = false ∧ ∀ v ∉ maskRow m, D.eval (insert v (maskRow m)) = true := by
  obtain ⟨closed,generic,bits,extend⟩ := donorRowsOK m hm
  let P := univ.filter (pointBit m)
  have hp (p : Fin 13) : p ∈ P ↔ pointBit m p := by simp [P]
  constructor
  · have closed' : ∀ p ∉ P, ∃ l, (∀ q ∈ P, ¬ donorInc q l) ∧ donorInc p l := by
      simpa only [hp,freeBit] using closed
    have generic' : (¬ ∃ l, ∀ p ∈ P, donorInc p l) ∧
        ¬ ∃ p, ∀ l, (∀ q ∈ P, ¬ donorInc q l) → donorInc p l := by
      simpa only [hp,freeBit] using generic
    convert neg P closed' generic' using 2
    ext k
    simpa only [atRow,mem_filter,mem_univ,true_and,hp,freeBit] using bits k
  · intro v hv
    have hv' := Bool.eq_false_iff.mpr (fun h => hv ((atRow ..).mpr h))
    obtain ⟨p,l,incident,h⟩ := extend v hv'
    apply donorMono D (hx := pos p l incident)
    apply insert_subset_iff.mpr
    rcases h with ⟨rfl,hl⟩ | ⟨rfl,hp'⟩
    · exact ⟨mem_insert_self ..,singleton_subset_iff.mpr (mem_insert_of_mem ((atRow ..).mpr hl))⟩
    · exact ⟨mem_insert_of_mem ((atRow ..).mpr hp'),singleton_subset_iff.mpr (mem_insert_self ..)⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem donorRows (D : AndCountCircuit 26) (pos : donorPos D) (neg : donorNeg D)
    (d : Bool) (p : Fin 13) :
    (∀ q, q ≠ p → D.eval {donorP d p,donorP d q} = false) ∧
    (∀ t, ¬ donorI d p t → D.eval {donorP d p,donorL d t} = false) ∧
    (∀ t u, ¬ donorI d p t → ¬ donorI d p u → t ≠ u →
      ∃ S : Finset (Fin 26), donorP d p ∈ S ∧ donorL d t ∈ S ∧ D.eval S = false ∧
        D.eval (insert (donorL d u) S) = true) ∧
    (∀ t u, ¬ donorI d p t → ¬ donorI d p u → t ≠ u →
      ∃ S : Finset (Fin 26), donorP d p ∈ S ∧ D.eval S = false ∧
        D.eval (insert (donorL d t) S) = true ∧ D.eval (insert (donorL d u) S) = true) := by
  obtain ⟨pp,pl,tw⟩ := donorMasksRealize d p
  have down (a b : Fin 26) {m : ℕ} (hm : m ∈ donorMasks)
      (ha : m.testBit a.val = true) (hb : m.testBit b.val = true) : D.eval {a,b} = false :=
    Bool.eq_false_iff.mpr fun ht => Bool.false_ne_true ((donorMaskSem D pos neg m hm).1.symm.trans
      (donorMono D (insert_subset_iff.mpr
        ⟨(atRow ..).mpr ha,singleton_subset_iff.mpr ((atRow ..).mpr hb)⟩) ht))
  refine ⟨?_,?_,?_,?_⟩
  · intro q _
    obtain ⟨m,hm,ha,hb⟩ := pp q
    exact down _ _ hm ha hb
  · intro t ht
    obtain ⟨m,hm,ha,hb⟩ := pl t ht
    exact down _ _ hm ha hb
  · intro t u ht hu htu
    obtain ⟨m,hm,hp,ht,hu⟩ := (tw t u ht hu htu).1
    obtain ⟨no,yes⟩ := donorMaskSem D pos neg m hm
    exact ⟨maskRow m,(atRow ..).mpr hp,(atRow ..).mpr ht,no,yes _ (fun h => hu ((atRow ..).mp h))⟩
  · intro t u ht hu htu
    obtain ⟨m,hm,hp,ht,hu⟩ := (tw t u ht hu htu).2
    obtain ⟨no,yes⟩ := donorMaskSem D pos neg m hm
    exact ⟨maskRow m,(atRow ..).mpr hp,no,yes _ (fun h => ht ((atRow ..).mp h)),
      yes _ (fun h => hu ((atRow ..).mp h))⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem donorCounts : ∀ (d : Bool) (p : Fin 13),
    ((univ : Finset (Fin 13)).filter (donorI d p)).card = 4 ∧
    (∀ t, ((univ : Finset (Fin 13)).filter (donorI d · t)).card = 4) ∧
    (∀ t, ∃ q, donorI d q t) ∧
    (∀ q, q ≠ p →
      3 ≤ ((univ : Finset (Fin 13)).filter fun t => donorI d q t ∧ ¬donorI d p t).card) ∧
    Fintype.card {t // ¬ donorI d p t} = 9 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem donorUnique (d : Bool) {a b t u : Fin 13} (hn : a ≠ b)
    (at' : donorI d a t) (bt : donorI d b t) (au : donorI d a u) (bu : donorI d b u) :
    t = u := by
  have h : ∀ (d : Bool) (a b : Fin 13), a ≠ b →
      ((univ : Finset (Fin 13)).filter fun t => donorI d a t ∧ donorI d b t).card ≤ 1 := by decide +kernel
  exact card_le_one.mp (h d a b hn) t (mem_filter.mpr ⟨mem_univ _,at',bt⟩)
    u (mem_filter.mpr ⟨mem_univ _,au,bu⟩)

end PEqualNP.Outside.L_meta_17461.Plane1898

namespace PEqualNP.Outside.L_meta_17461.Plane1898

open Finset

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem canonicalStars {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (p : Fin 13)
    (pt ln : Fin 13 → Fin 26) (U : Finset ι) (A : Fin 26 → ι → Bool → Prop)
    (H : Fin 26 → Finset ι)
    (hH : ∀ v g, g ∈ H v ↔ g ∉ U ∧ (A v g false ∨ A v g true))
    (n : Fintype.card ι = 12) (u : U.card = 3)
    (zcard : Fintype.card {t // ¬ I p t} = 9)
    (three : ∀ q, q ≠ p →
      3 ≤ ((univ : Finset (Fin 13)).filter fun t => I q t ∧ ¬ I p t).card)
    (lcap : ∀ t : {t // ¬ I p t}, (H (ln t)).card ≤ 1)
    (pcap : ∀ q, q ≠ p → (H (pt q)).card ≤ 3)
    (cross : ∀ (q : Fin 13) (t : {t // ¬ I p t}), q ≠ p → I q t →
      ∃ g ∉ U, ∃ b, A (ln t) g b ∧ ¬ A (ln t) g (!b) ∧
        A (pt q) g (!b) ∧ ¬ A (pt q) g b)
    (anchor : ∀ t : {t // ¬ I p t}, ∃ g ∈ H (ln t), ∃ b, A (ln t) g b ∧ ¬ A (ln t) g (!b))
    (distinct : ∀ (t w : {t // ¬ I p t}), t ≠ w → ∀ g b c,
      (∀ j ∈ H (ln t), j = g) → (∀ j ∈ H (ln w), j = g) →
      A (ln t) g b → ¬ A (ln t) g (!b) → A (ln w) g c → ¬ A (ln w) g (!c) → False) :
    ∃ (star : {t // ¬ I p t} → ι) (orient : {t // ¬ I p t} → Bool),
      Function.Injective star ∧
      (∀ g, g ∉ U ↔ ∃ t, star t = g) ∧
      (∀ t : {t // ¬ I p t}, A (ln t) (star t) (orient t) ∧ ¬ A (ln t) (star t) (!(orient t))) ∧
      ∀ (t : {t // ¬ I p t}) q, q ≠ p →
        (A (pt q) (star t) (!(orient t)) ↔ I q t) ∧ ¬ A (pt q) (star t) (orient t) := by
  classical
  let Z := {t // ¬ I p t}
  choose star memS orient ha hn using anchor
  have uniq (t : Z) (j : ι) (hj : j ∈ H (ln t)) : j = star t :=
    card_le_one.mp (lcap t) j hj (star t) (memS t)
  have inj : Function.Injective star := by
    intro t w e
    by_contra ne
    apply distinct t w ne (star w) (orient t) (orient w)
    · exact fun j h => (uniq t j h).trans e
    · exact uniq w
    · exact e ▸ ha t
    · exact e ▸ hn t
    · exact ha w
    · exact hn w
  have outside (t : Z) : star t ∉ U := ((hH ..).mp (memS t)).1
  let f (t : Z) : ↥Uᶜ := ⟨star t, mem_compl.mpr (outside t)⟩
  have fi : Function.Injective f := fun _ _ h => inj (congrArg Subtype.val h)
  have count := card_compl_add_card U
  rw [n,u] at count
  have equalCards : Fintype.card Z = Fintype.card ↥Uᶜ := by
    rw [Fintype.card_coe]
    change Fintype.card {t // ¬ I p t} = _
    omega
  have fs := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨fi,equalCards⟩).2
  refine ⟨star,orient,inj,?_,fun t => ⟨ha t,hn t⟩,?_⟩
  · intro g
    constructor
    · intro hg
      obtain ⟨t,ht⟩ := fs ⟨g,mem_compl.mpr hg⟩
      exact ⟨t,congrArg Subtype.val ht⟩
    · rintro ⟨t,rfl⟩
      exact outside t
  intro t q hq
  have pos (a : Z) (e : I q a) :
      A (pt q) (star a) (!(orient a)) ∧ ¬ A (pt q) (star a) (orient a) := by
    obtain ⟨g,hgu,b,l,_,r,z⟩ := cross q a hq e
    have hg := uniq a g ((hH ..).mpr ⟨hgu,by cases b <;> first | exact Or.inl l | exact Or.inr l⟩)
    subst g
    have eb : b = orient a := by
      by_contra hh
      have : b = !(orient a) := Bool.eq_not_of_ne hh
      exact hn a (this ▸ l)
    simpa only [eb] using And.intro r z
  have covers (a : Z) : I q a → star a ∈ H (pt q) := by
    intro e
    have hh := (pos a e).1
    exact (hH ..).mpr ⟨outside a, by cases he : orient a <;> rw [he] at hh <;>
      first | exact Or.inl hh | exact Or.inr hh⟩
  let T := (univ : Finset (Fin 13)).filter fun a => I q a ∧ ¬ I p a
  let f' (a : ↥T) : ↥(H (pt q)) :=
    ⟨star ⟨a.1,(mem_filter.mp a.2).2.2⟩, covers ⟨a.1,(mem_filter.mp a.2).2.2⟩ (mem_filter.mp a.2).2.1⟩
  have fi' : Function.Injective f' := by
    intro a b hh
    have hZ : (⟨a.1,(mem_filter.mp a.2).2.2⟩ : Z) =
        (⟨b.1,(mem_filter.mp b.2).2.2⟩ : Z) := inj (congrArg Subtype.val hh)
    exact Subtype.ext (congrArg (fun z : Z => z.1) hZ)
  have fs' := ((Fintype.bijective_iff_injective_and_card f').mpr
    ⟨fi',le_antisymm (Fintype.card_le_of_injective _ fi')
      (by simpa only [Fintype.card_coe] using (pcap q hq).trans (three q hq))⟩).2
  have only (h : star t ∈ H (pt q)) : I q t := by
    obtain ⟨a,hh⟩ := fs' ⟨star t,h⟩
    have e : (⟨a.1,(mem_filter.mp a.2).2.2⟩ : Z) = t := inj (congrArg Subtype.val hh)
    exact (congrArg Subtype.val e) ▸ (mem_filter.mp a.2).2.1
  have hit (b : Bool) (hb : A (pt q) (star t) b) : I q t :=
    only ((hH ..).mpr ⟨outside t, by cases b <;> first | exact Or.inl hb | exact Or.inr hb⟩)
  exact ⟨⟨hit _,fun e => (pos t e).1⟩,fun hb => (pos t (hit _ hb)).2 hb⟩

end PEqualNP.Outside.L_meta_17461.Plane1898

namespace PEqualNP.Outside.L_meta_17461.Plane1898.Cofactor

open Finset PEqualNP.AndCount

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem sideTrue_def : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool),
    PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
      decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := fun _ _ _ _ _ => rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem eval_def : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
    E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := fun _ _ => rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem sideTrue_congr : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool), (∀ j : Fin k, j < i → val j = val' j) →
    PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val' := by
  classical
  intro k U B F i val val' h
  rw [sideTrue_def, sideTrue_def, decide_eq_decide]
  constructor
  · intro h1
    rcases h1 with h1 | h2
    · exact Or.inl h1
    · rcases h2 with ⟨j, hj, hlt, hv⟩
      exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · intro h1
    rcases h1 with h1 | h2
    · exact Or.inl h1
    · rcases h2 with ⟨j, hj, hlt, hv⟩
      exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem fuel_indep : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
    (d d' : ℕ) (i : Fin E.size), i.val < d → i.val < d' →
    E.gateValFuel U d i = E.gateValFuel U d' i := by
  classical
  intro E U d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
            PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) =
           (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e') &&
            PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e'))
      rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
          sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem gateVal_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)) (i : Fin E.size),
    E.gateVal U i =
      (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateVal U) &&
       PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateVal U)) := by
  classical
  intro E U i
  have hi : i.val < E.size := i.2
  obtain ⟨e, he⟩ : ∃ e, E.size = e + 1 := ⟨E.size - 1, by omega⟩
  have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep E U e E.size j (by omega) j.2
  have h1 : E.gateVal U i = E.gateValFuel U (e + 1) i :=
    fuel_indep E U E.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
        PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) = _
  rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
      sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem gateValFuel_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
    U ⊆ V → ∀ (d : ℕ) (i : Fin E.size), E.gateValFuel U d i = true → E.gateValFuel V d i = true := by
  classical
  intro E U V hUV d
  induction d with
  | zero => intro i h; cases h
  | succ d ih =>
    intro i h
    change (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
            PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) = true at h
    change (PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.leftVars i) (E.leftGates i) i (E.gateValFuel V d) &&
            PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.rightVars i) (E.rightGates i) i (E.gateValFuel V d)) = true
    rw [Bool.and_eq_true] at h ⊢
    constructor
    · have hL := h.1
      rw [sideTrue_def] at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with h1 | h2
      · rcases h1 with ⟨v, hv, hu⟩
        exact Or.inl ⟨v, hv, hUV hu⟩
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, ih j hv⟩
    · have hR := h.2
      rw [sideTrue_def] at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with h1 | h2
      · rcases h1 with ⟨v, hv, hu⟩
        exact Or.inl ⟨v, hv, hUV hu⟩
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, ih j hv⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem gateVal_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
    U ⊆ V → ∀ i : Fin E.size, E.gateVal U i = true → E.gateVal V i = true := by
  classical
  intro E U V hUV i h
  exact gateValFuel_mono E hUV E.size i h
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem eval_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
    U ⊆ V → E.eval U = true → E.eval V = true := by
  classical
  intro E U V hUV h
  rw [eval_def] at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  rcases h with h1 | h2
  · rcases h1 with ⟨v, hv, hu⟩
    exact Or.inl ⟨v, hv, hUV hu⟩
  · rcases h2 with ⟨j, hj, hv⟩
    exact Or.inr ⟨j, hj, gateVal_mono E hUV j hv⟩

def signal {k : ℕ} (U A : Finset (Fin 26)) (P : Finset (Fin k)) (val : Fin k → Bool) : Prop :=
  (∃ v ∈ A, v ∈ U) ∨ ∃ j ∈ P, val j = true
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem gate_spec : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
    ∀ (U : Finset (Fin 26)) (i : Fin E.size),
      E.gateVal U i = true ↔
        signal U (E.leftVars i) (E.leftGates i) (E.gateVal U) ∧
        signal U (E.rightVars i) (E.rightGates i) (E.gateVal U) := by
  classical
  intro E hw U i
  rw [gateVal_eq, Bool.and_eq_true]
  rw [sideTrue_def, sideTrue_def]; simp only [signal, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h.1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, _, hv⟩; exact Or.inr ⟨j, hj, hv⟩
    · rcases h.2 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, _, hv⟩; exact Or.inr ⟨j, hj, hv⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h.1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hv⟩; exact Or.inr ⟨j, hj, (hw i).1 j hj, hv⟩
    · rcases h.2 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hv⟩; exact Or.inr ⟨j, hj, (hw i).2 j hj, hv⟩
def expandVars {m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin 26)) (P : Finset (Fin (m + 1))) : Finset (Fin 26) :=
  A ∪ if i ∈ P then B else ∅
noncomputable def expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun k => i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem signal_expand : ∀ {m : ℕ} (i : Fin (m + 1)) (U B A : Finset (Fin 26))
    (F P : Finset (Fin (m + 1))) (val : Fin (m + 1) → Bool) (val' : Fin m → Bool),
    (∀ j ∈ F, j < i) → (val i = true ↔ signal U B F val) →
    (∀ k ∈ expandRefs i F P, val' k = val (i.succAbove k)) →
    (signal U (expandVars i B A P) (expandRefs i F P) val' ↔ signal U A P val) := by
  classical
  intro m i U B A F P val val' before expand agree
  have memV : ∀ v : Fin 26, v ∈ expandVars i B A P ↔ v ∈ A ∨ i ∈ P ∧ v ∈ B := by
    intro v; by_cases h : i ∈ P <;> simp [expandVars, h]
  have memR : ∀ k : Fin m, k ∈ expandRefs i F P ↔ i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := by
    intro k; simp [expandRefs]
  constructor
  · intro h
    rcases h with h1 | h2
    · rcases h1 with ⟨v, hv, hu⟩
      rcases (memV v).mp hv with hvA | hB
      · exact Or.inl ⟨v, hvA, hu⟩
      · exact Or.inr ⟨i, hB.1, expand.mpr (Or.inl ⟨v, hB.2, hu⟩)⟩
    · rcases h2 with ⟨k, hk, ht⟩
      rw [agree k hk] at ht
      rcases (memR k).mp hk with hP | hF
      · exact Or.inr ⟨_, hP, ht⟩
      · exact Or.inr ⟨i, hF.1, expand.mpr (Or.inr ⟨_, hF.2, ht⟩)⟩
  · intro h
    rcases h with h1 | h2
    · rcases h1 with ⟨v, hv, hu⟩
      exact Or.inl ⟨v, (memV v).mpr (Or.inl hv), hu⟩
    · rcases h2 with ⟨j, hj, ht⟩
      by_cases hji : j = i
      · subst j
        rcases expand.mp ht with h3 | h4
        · rcases h3 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, (memV v).mpr (Or.inr ⟨hj, hv⟩), hu⟩
        · rcases h4 with ⟨l, hl, ht'⟩
          obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (ne_of_lt (before l hl))
          have hk := (memR k).mpr (Or.inr ⟨hj, hl⟩)
          exact Or.inr ⟨k, hk, (agree k hk).trans ht'⟩
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        have hk := (memR k).mpr (Or.inl hj)
        exact Or.inr ⟨k, hk, (agree k hk).trans ht⟩
def Expandable (E : PEqualNP.AndCount.AndCountCircuit 26) (Dom : Set (Finset (Fin 26))) (i : Fin E.size) : Prop :=
  ∃ B : Finset (Fin 26), ∃ F : Finset (Fin E.size), (∀ j ∈ F, j < i) ∧
    ∀ U ∈ Dom, E.gateVal U i = true ↔ signal U B F (E.gateVal U)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem remove_one : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (Dom : Set (Finset (Fin 26))) (i : Fin E.size),
    E.WellFormed → Expandable E Dom i →
    ∃ E' : PEqualNP.AndCount.AndCountCircuit 26, ∃ f : Fin E'.size → Fin E.size,
      E'.WellFormed ∧ E'.size + 1 = E.size ∧ StrictMono f ∧
      (∀ j, j ≠ i ↔ ∃ k, f k = j) ∧
      ∀ U ∈ Dom, E'.eval U = E.eval U ∧ ∀ j, E'.gateVal U j = E.gateVal U (f j) := by
  classical
  intro E Dom i hw hexp
  obtain ⟨B, F, before, same⟩ := hexp
  rcases E with ⟨s, lv, lg, rv, rg, ov, og⟩
  cases s with
  | zero => exact Fin.elim0 i
  | succ m =>
    let E0 : PEqualNP.AndCount.AndCountCircuit 26 := ⟨m + 1, lv, lg, rv, rg, ov, og⟩
    let E' : PEqualNP.AndCount.AndCountCircuit 26 :=
      ⟨m, fun j => expandVars i B (lv (i.succAbove j)) (lg (i.succAbove j)),
          fun j => expandRefs i F (lg (i.succAbove j)),
          fun j => expandVars i B (rv (i.succAbove j)) (rg (i.succAbove j)),
          fun j => expandRefs i F (rg (i.succAbove j)),
          expandVars i B ov og, expandRefs i F og⟩
    have lt_ref : ∀ (j k : Fin m) (P : Finset (Fin (m + 1))),
        (∀ l ∈ P, l < i.succAbove j) → k ∈ expandRefs i F P → k < j := by
      intro j k P old hk
      apply Fin.succAbove_lt_succAbove_iff.mp
      have hk' : i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := (Finset.mem_filter.mp hk).2
      rcases hk' with hp | hif
      · exact old _ hp
      · exact (before _ hif.2).trans (old i hif.1)
    have hw' : E'.WellFormed := fun j =>
      ⟨fun k hk => lt_ref j k _ (hw (i.succAbove j)).1 hk,
       fun k hk => lt_ref j k _ (hw (i.succAbove j)).2 hk⟩
    refine ⟨E', i.succAbove, hw', rfl, fun j k hjk => Fin.succAbove_lt_succAbove_iff.mpr hjk, ?_, ?_⟩
    · intro j
      refine ⟨Fin.exists_succAbove_eq, ?_⟩
      intro hex; rcases hex with ⟨k, rfl⟩; exact Fin.succAbove_ne i k
    · intro U hU
      have values : ∀ j : Fin m, E'.gateVal U j = E0.gateVal U (i.succAbove j) := by
        intro j
        induction j using (wellFounded_lt : WellFounded ((· < ·) : Fin m → Fin m → Prop)).induction with
        | h j ih =>
          rw [Bool.eq_iff_iff, gate_spec E' hw', gate_spec E0 hw]
          exact and_congr
            (signal_expand i U B _ F _ _ _ before (same U hU)
              (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).1 hk)))
            (signal_expand i U B _ F _ _ _ before (same U hU)
              (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).2 hk)))
      refine ⟨?_, values⟩
      rw [eval_def, eval_def]
      rw [decide_eq_decide]
      exact signal_expand i U B ov F og _ _ before (same U hU) (fun k _ => values k)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem remove_many : ∀ (Dom : Set (Finset (Fin 26))) (k : ℕ) (E : PEqualNP.AndCount.AndCountCircuit 26),
    E.WellFormed → ∀ (S : Finset (Fin E.size)), S.card = k → (∀ i ∈ S, Expandable E Dom i) →
    ∃ E' : PEqualNP.AndCount.AndCountCircuit 26, E'.WellFormed ∧ E'.size + S.card ≤ E.size ∧
      ∀ U ∈ Dom, E'.eval U = E.eval U := by
  classical
  intro Dom k
  induction k with
  | zero =>
    intro E hw S hS _
    exact ⟨E, hw, by simp [hS], fun _ _ => rfl⟩
  | succ k ih =>
    intro E hw S hS expands
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let i := S.max' hne
    have hi : i ∈ S := S.max'_mem hne
    obtain ⟨E', f, hw', hsize, hmono, hran, hsem⟩ := remove_one E Dom i hw (expands i hi)
    let S' : Finset (Fin E'.size) := Finset.univ.filter (fun j => f j ∈ S)
    have lift_mem : ∀ j : Fin E'.size, j ∈ S' ↔ f j ∈ S := fun j => by simp [S']
    have himg : S'.image f = S.erase i := by
      ext r
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · intro h; rcases h with ⟨j, hj, rfl⟩
        exact ⟨(hran _).mpr ⟨j, rfl⟩, (lift_mem j).mp hj⟩
      · intro h
        obtain ⟨j, rfl⟩ := (hran r).mp h.1
        exact ⟨j, (lift_mem j).mpr h.2, rfl⟩
    have hcard : S'.card = k := by
      have hc := Finset.card_image_of_injective S' hmono.injective
      rw [himg, Finset.card_erase_of_mem hi] at hc
      omega
    have hexp' : ∀ j ∈ S', Expandable E' Dom j := by
      intro j hj
      have hjS := (lift_mem j).mp hj
      obtain ⟨B, F, before, same⟩ := expands (f j) hjS
      let F' : Finset (Fin E'.size) := Finset.univ.filter (fun l => f l ∈ F)
      have hF' : ∀ l : Fin E'.size, l ∈ F' ↔ f l ∈ F := fun l => by simp [F']
      have hnotrem : i ∉ F := fun h =>
        (not_lt_of_ge (Finset.le_max' S (f j) hjS)) (before i h)
      refine ⟨B, F', ?_, ?_⟩
      · intro l hl
        exact hmono.lt_iff_lt.mp (before _ ((hF' l).mp hl))
      · intro U hU
        have values := (hsem U hU).2
        rw [values j, same U hU]
        constructor
        · intro h
          rcases h with h1 | h2
          · exact Or.inl h1
          · rcases h2 with ⟨l, hl, ht⟩
            have hli : l ≠ i := fun he => hnotrem (he ▸ hl)
            obtain ⟨q, rfl⟩ := (hran l).mp hli
            exact Or.inr ⟨q, (hF' q).mpr hl, (values q).trans ht⟩
        · intro h
          rcases h with h1 | h2
          · exact Or.inl h1
          · rcases h2 with ⟨l, hl, ht⟩
            exact Or.inr ⟨f l, (hF' l).mp hl, (values l).symm.trans ht⟩
    obtain ⟨E'', hw'', hbd, hout⟩ := ih E' hw' S' hcard hexp'
    exact ⟨E'', hw'', by omega, fun U hU => (hout U hU).trans (hsem U hU).1⟩

abbrev Circ := AndCountCircuit 26
abbrev Vertex := Fin 26

def vars (D : Circ) (i : Fin D.size) (b : Bool) :=
  if b then D.rightVars i else D.leftVars i

def refs (D : Circ) (i : Fin D.size) (b : Bool) :=
  if b then D.rightGates i else D.leftGates i

def side (D : Circ) (X : Finset Vertex) (i : Fin D.size) (b : Bool) : Prop :=
  signal X (vars D i b) (refs D i b) (D.gateVal X)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem sides (D : Circ) (hw : D.WellFormed) (X : Finset Vertex) (i : Fin D.size) :
    D.gateVal X i = true ↔ side D X i false ∧ side D X i true := gate_spec D hw X i

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem sides_orient (D : Circ) (hw : D.WellFormed) (X : Finset Vertex) (i : Fin D.size) (b : Bool) :
    D.gateVal X i = true ↔ side D X i b ∧ side D X i (!b) := by
  cases b
  · exact sides D hw X i
  · exact (sides D hw X i).trans and_comm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem side_mono (D : Circ) {X Y : Finset Vertex} (h : X ⊆ Y) (i : Fin D.size) (b : Bool) :
    side D X i b → side D Y i b := by
  rintro (⟨v,hv,hin⟩|⟨j,hj,ht⟩)
  · exact Or.inl ⟨v,hv,h hin⟩
  · exact Or.inr ⟨j,hj,gateVal_mono D h j ht⟩

noncomputable def active (D : Circ) (X : Finset Vertex) : Finset (Fin D.size) := by
  classical exact univ.filter fun i => side D X i false ∨ side D X i true

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mem_active {D : Circ} {X : Finset Vertex} {i : Fin D.size} :
    i ∈ active D X ↔ side D X i false ∨ side D X i true := by classical simp [active]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem residual (D : Circ) (hw : D.WellFormed) (X : Finset Vertex) :
    ∃ E : Circ, E.WellFormed ∧ E.size + (active D X).card ≤ D.size ∧
      ∀ Y, X ⊆ Y → E.eval Y = D.eval Y := by
  apply remove_many {Y | X ⊆ Y} _ D hw _ rfl
  intro i hi
  rcases mem_active.mp hi with left | right
  · refine ⟨D.rightVars i,D.rightGates i,(hw i).2,?_⟩
    intro Y hY
    exact (sides D hw Y i).trans ⟨And.right, fun h => ⟨side_mono D hY _ _ left,h⟩⟩
  · refine ⟨D.leftVars i,D.leftGates i,(hw i).1,?_⟩
    intro Y hY
    exact (sides D hw Y i).trans ⟨And.left, fun h => ⟨h,side_mono D hY _ _ right⟩⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem card_bound (D : Circ) (hw : D.WellFormed) (X : Finset Vertex) (k : ℕ)
    (lb : ∀ E : Circ, E.WellFormed → (∀ Y, X ⊆ Y → E.eval Y = D.eval Y) → k ≤ E.size) :
    k + (active D X).card ≤ D.size := by
  obtain ⟨E,he,hc,ha⟩ := residual D hw X
  have := lb E he ha
  omega

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mixed (D : Circ) (hw : D.WellFormed) (X Y : Finset Vertex)
    (hx : D.eval X = false) (hy : D.eval Y = false) (hxy : D.eval (X ∪ Y) = true) :
    ∃ i b, side D X i b ∧ ¬ side D Y i b ∧ side D Y i (!b) ∧ ¬ side D X i (!b) := by
  classical
  let T := univ.filter fun i : Fin D.size =>
    D.gateVal (X ∪ Y) i = true ∧ D.gateVal X i = false ∧ D.gateVal Y i = false
  have hne : T.Nonempty := by
    rw [eval_def, decide_eq_true_eq] at hxy
    rcases hxy with ⟨v,hv,hin⟩ | ⟨i,hi,hit⟩
    · rcases mem_union.mp hin with h | h
      · have : D.eval X = true := decide_eq_true (Or.inl ⟨v,hv,h⟩)
        simp_all
      · have : D.eval Y = true := decide_eq_true (Or.inl ⟨v,hv,h⟩)
        simp_all
    · refine ⟨i,mem_filter.mpr ⟨mem_univ _,hit,?_,?_⟩⟩
      · apply Bool.eq_false_iff.mpr; intro h
        have : D.eval X = true := decide_eq_true (Or.inr ⟨i,hi,h⟩)
        simp_all
      · apply Bool.eq_false_iff.mpr; intro h
        have : D.eval Y = true := decide_eq_true (Or.inr ⟨i,hi,h⟩)
        simp_all
  let i := T.min' hne
  have hm := (mem_filter.mp (T.min'_mem hne)).2
  change D.gateVal (X ∪ Y) i = true ∧ D.gateVal X i = false ∧ D.gateVal Y i = false at hm
  have splitSide (b : Bool) : side D X i b ∨ side D Y i b := by
    have hot := ((sides_orient D hw _ _ b).mp hm.1).1
    rcases hot with ⟨v,hv,hin⟩ | ⟨j,hj,hit⟩
    · rcases mem_union.mp hin with h | h
      · exact Or.inl (Or.inl ⟨v,hv,h⟩)
      · exact Or.inr (Or.inl ⟨v,hv,h⟩)
    · have lt : j < i := by cases b; exact (hw i).1 _ hj; exact (hw i).2 _ hj
      by_cases hX : D.gateVal X j = true
      · exact Or.inl (Or.inr ⟨j,hj,hX⟩)
      by_cases hY : D.gateVal Y j = true
      · exact Or.inr (Or.inr ⟨j,hj,hY⟩)
      have mem : j ∈ T := mem_filter.mpr ⟨mem_univ _,hit,Bool.eq_false_iff.mpr hX,Bool.eq_false_iff.mpr hY⟩
      exact (not_le_of_gt lt (T.min'_le _ mem)).elim
  have nX : ¬ (side D X i false ∧ side D X i true) := fun h => by
    have := (sides D hw X i).mpr h; simp_all
  have nY : ¬ (side D Y i false ∧ side D Y i true) := fun h => by
    have := (sides D hw Y i).mpr h; simp_all
  have h0 := splitSide false
  have h1 := splitSide true
  by_cases h : side D X i false
  · have nx : ¬ side D X i true := fun ht => nX ⟨h,ht⟩
    have yt := h1.resolve_left nx
    exact ⟨i,false,h,fun yf => nY ⟨yf,yt⟩,yt,nx⟩
  · have yf := h0.resolve_left h
    have ny : ¬ side D Y i true := fun ht => nY ⟨yf,ht⟩
    exact ⟨i,true,h1.resolve_right ny,ny,yf,h⟩

def G (D : Circ) (v : Vertex) : Finset (Fin D.size) :=
  univ.filter fun i => v ∈ D.leftVars i ∨ v ∈ D.rightVars i

def pair (a v : Vertex) : Finset Vertex := {a,v}
def A (D : Circ) (a v : Vertex) := side D (pair a v)
def LB (D : Circ) (X : Finset Vertex) (k : ℕ) :=
  ∀ E : Circ, E.WellFormed → (∀ Y, X ⊆ Y → E.eval Y = D.eval Y) → k ≤ E.size

def Hit (D : Circ) (pt ln : Fin 13 → Vertex) (q t : Fin 13) (g : Fin D.size) :=
  (pt q ∈ D.leftVars g ∧ ln t ∈ D.rightVars g) ∨
  (pt q ∈ D.rightVars g ∧ ln t ∈ D.leftVars g)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem side_raw {D : Circ} {X : Finset Vertex} {i : Fin D.size} {b : Bool} {v : Vertex}
    (h : v ∈ vars D i b) (hv : v ∈ X) : side D X i b := Or.inl ⟨v,h,hv⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem not_outside {D : Circ} {a : Vertex} {X Y : Finset Vertex} {i : Fin D.size} {b : Bool}
    (ax : a ∈ X) (ay : a ∈ Y) (hx : ¬side D X i (!b)) (hy : ¬side D Y i b) :
    i ∉ G D a := by
  intro h
  have h' := (mem_filter.mp h).2
  cases b <;> rcases h' with l|r
  · exact hy (side_raw l ay)
  · exact hx (side_raw r ax)
  · exact hx (side_raw l ax)
  · exact hy (side_raw r ay)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mixed_row (D : Circ) (hw : D.WellFormed) (a v : Vertex) (S : Finset Vertex)
    (ha : a ∈ S) (hp : D.eval (pair a v) = false)
    (hs : D.eval S = false) (hi : D.eval (insert v S) = true) :
    ∃ i ∉ G D a, ∃ b, A D a v i b ∧ ¬ A D a v i (!b) ∧ side D S i (!b) ∧ ¬side D S i b := by
  have he : pair a v ∪ S = insert v S := by ext x; simp [pair]; grind
  obtain ⟨i,b,h1,h2,h3,h4⟩ := mixed D hw (pair a v) S hp hs (he ▸ hi)
  exact ⟨i,not_outside (by simp [pair]) ha h4 h2,b,h1,h4,h3,h2⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem stars (D : Circ) (hw : D.WellFormed) (sz : D.size = 12)
    (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (pt ln : Fin 13 → Vertex) (p : Fin 13)
    (degp : (G D (pt p)).card = 3) (zcard : Fintype.card {t // ¬ I p t} = 9)
    (each : ∀ t, ¬ I p t → ∃ q, I q t)
    (three : ∀ q, q ≠ p → 3 ≤ (univ.filter fun t => I q t ∧ ¬ I p t).card)
    (dpq : ∀ q, q ≠ p → D.eval (pair (pt p) (pt q)) = false)
    (dpl : ∀ t, ¬ I p t → D.eval (pair (pt p) (ln t)) = false)
    (pos : ∀ q t, I q t → D.eval {pt q,ln t} = true)
    (rowDiff : ∀ t u, ¬ I p t → ¬ I p u → t ≠ u → ∃ S : Finset Vertex,
      pt p ∈ S ∧ ln t ∈ S ∧ D.eval S = false ∧ D.eval (insert (ln u) S) = true)
    (rowBoth : ∀ t u, ¬ I p t → ¬ I p u → t ≠ u → ∃ S : Finset Vertex,
      pt p ∈ S ∧ D.eval S = false ∧ D.eval (insert (ln t) S) = true ∧ D.eval (insert (ln u) S) = true)
    (lbp : ∀ q, q ≠ p → LB D (pair (pt p) (pt q)) 6)
    (lbl : ∀ t, ¬ I p t → LB D (pair (pt p) (ln t)) 8) :
    ∃ (star : {t // ¬ I p t} → Fin D.size) (orient : {t // ¬ I p t} → Bool),
      Function.Injective star ∧
      (∀ g, g ∉ G D (pt p) ↔ ∃ t, star t = g) ∧
      (∀ (t : {t // ¬ I p t}) g b, A D (pt p) (ln t) g b → g ∉ G D (pt p) → g = star t ∧ b = orient t) ∧
      (∀ t : {t // ¬ I p t}, A D (pt p) (ln t) (star t) (orient t)) ∧
      ∀ t q, q ≠ p →
        (A D (pt p) (pt q) (star t) (!(orient t)) ↔ I q t) ∧
          ¬ A D (pt p) (pt q) (star t) (orient t) := by
  classical
  let a := pt p
  let Z := {t // ¬ I p t}
  let H (v : Vertex) := active D (pair a v) \ G D a
  have hpMem (v : Vertex) : G D a ⊆ active D (pair a v) := by
    intro g hg
    apply mem_active.mpr
    have ha : a ∈ pair a v := by simp [pair]
    rcases (mem_filter.mp hg).2 with h|h
    · exact Or.inl (side_raw h ha)
    · exact Or.inr (side_raw h ha)
  have hH (v : Vertex) (g : Fin D.size) :
      g ∈ H v ↔ g ∉ G D a ∧ (A D a v g false ∨ A D a v g true) := by
    rw [show H v = _ from rfl, mem_sdiff,mem_active,and_comm]; rfl
  have cap (v : Vertex) (k : ℕ) (lb : LB D (pair a v) k) : (H v).card + k + 3 ≤ 12 := by
    have h0 := card_bound D hw (pair a v) k lb
    have h1 : (H v).card = (active D (pair a v)).card - (G D a).card := card_sdiff_of_subset (hpMem v)
    have h2 := card_le_card (hpMem v)
    change (G D a).card = 3 at degp
    omega
  have lcap (t : Z) : (H (ln t)).card ≤ 1 := by have := cap _ _ (lbl t t.2); omega
  have pcap (q) (hq : q ≠ p) : (H (pt q)).card ≤ 3 := by have := cap _ _ (lbp q hq); omega
  have memH {v g b} (hg : g ∉ G D a) (hb : A D a v g b) : g ∈ H v :=
    (hH ..).mpr ⟨hg,by cases b; exact Or.inl hb; exact Or.inr hb⟩
  have cross (q : Fin 13) (t : Z) (hq : q ≠ p) (hi : I q t) :
      ∃ g ∉ G D a, ∃ b, A D a (ln t) g b ∧ ¬ A D a (ln t) g (!b) ∧
        A D a (pt q) g (!b) ∧ ¬ A D a (pt q) g b := by
    have incl : {pt q,ln t} ⊆ pair a (ln t) ∪ pair a (pt q) := by
      intro x h; simp [pair] at h ⊢; tauto
    obtain ⟨g,b,hl,hqn,hq',hln⟩ := mixed D hw _ _ (dpl t t.2) (dpq q hq)
      (eval_mono D incl (pos q t hi))
    exact ⟨g,not_outside (by simp [a,pair]) (by simp [a,pair]) hln hqn,b,hl,hln,hq',hqn⟩
  have anchor (t : Z) : ∃ g ∈ H (ln t), ∃ b, A D a (ln t) g b ∧ ¬ A D a (ln t) g (!b) := by
    obtain ⟨q,hq⟩ := each t t.2
    obtain ⟨g,hg,b,l,n,_⟩ := cross q t (fun h => t.2 (h ▸ hq)) hq
    exact ⟨g,memH hg l,b,l,n⟩
  have distinct (t w : Z) (ne : t ≠ w) (g : Fin D.size) (b c : Bool)
      (ut : ∀ j ∈ H (ln t), j = g) (uw : ∀ j ∈ H (ln w), j = g)
      (ht : A D a (ln t) g b) (hnt : ¬ A D a (ln t) g (!b))
      (_hw : A D a (ln w) g c) (hnw : ¬ A D a (ln w) g (!c)) : False := by
    have resolve (z : Z) (d : Bool) (uni : ∀ j ∈ H (ln z), j = g)
        (no : ¬ A D a (ln z) g (!d)) (S : Finset Vertex) (ha : a ∈ S)
        (hs : D.eval S = false) (hm : D.eval (insert (ln z) S) = true) :
        side D S g (!d) ∧ ¬ side D S g d := by
      obtain ⟨i,hi,f,hf,_,hr,hn⟩ := mixed_row D hw a (ln z) S ha (dpl z z.2) hs hm
      have hi' := uni i (memH hi hf)
      subst i
      have : f = d := by by_contra hd; exact no (Bool.eq_not_of_ne hd ▸ hf)
      exact this ▸ ⟨hr,hn⟩
    have ne' : t.val ≠ w.val := fun h => ne (Subtype.ext h)
    by_cases eq : b = c
    · subst c
      obtain ⟨S,ha,ht',hs,hm⟩ := rowDiff t w t.2 w.2 ne'
      have hn := (resolve w b uw hnw S ha hs hm).2
      have inc : pair a (ln t) ⊆ S := by
        intro x hx; rcases mem_insert.mp hx with rfl|h; exact ha; exact mem_singleton.mp h ▸ ht'
      exact hn (side_mono D inc _ _ ht)
    · obtain ⟨S,ha,hs,hm,hm'⟩ := rowBoth t w t.2 w.2 ne'
      have yes := (resolve t b ut hnt S ha hs hm).1
      have no := (resolve w c uw hnw S ha hs hm').2
      exact no (Bool.eq_not_of_ne (Ne.symm eq) ▸ yes)
  obtain ⟨star,orient,inj,surj,ol,oq⟩ := canonicalStars I p pt ln (G D a) (A D a) H hH
    (by simpa using sz) degp zcard three lcap pcap cross anchor distinct
  refine ⟨star,orient,inj,surj,?_,fun t => (ol t).1,oq⟩
  intro t g b h hg
  have hm := memH hg h
  have hstar := memH ((surj (star t)).mpr ⟨t,rfl⟩) (ol t).1
  have eg := card_le_one.mp (lcap t) _ hm _ hstar
  subst g
  refine ⟨rfl,?_⟩
  by_contra neq
  exact (ol t).2 (Bool.eq_not_of_ne neq ▸ h)

def DonorData (D : Circ) (I : Fin 13 → Fin 13 → Prop) (pt ln : Fin 13 → Vertex) (p : Fin 13) : Prop :=
  ∃ src targets : Fin D.size → Finset (Fin 13),
    (∀ g q, q ∈ src g → g ∈ G D (pt q)) ∧
    (∀ g q t, q ∈ src g → t ∈ targets g → I q t) ∧
    (∀ g, g ∉ G D (pt p) → (targets g).card ≤ 1) ∧
    (∀ q t, q ≠ p → I q t → ¬ I p t → ∃ g, q ∈ src g ∧ t ∈ targets g) ∧
    (∀ g ∈ G D (pt p), ∀ q ∈ src g, ∀ t, Hit D pt ln p t g → ¬ Hit D pt ln q t g)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem fromStars (D : Circ) (hw : D.WellFormed) (I : Fin 13 → Fin 13 → Prop)
    (pt ln : Fin 13 → Vertex) (p : Fin 13)
    (star : {t // ¬ I p t} → Fin D.size) (orient : {t // ¬ I p t} → Bool)
    (inj : Function.Injective star)
    (outside : ∀ g, g ∉ G D (pt p) ↔ ∃ t, star t = g)
    (pts : ∀ t q, q ≠ p →
      (A D (pt p) (pt q) (star t) (!(orient t)) ↔ I q t) ∧ ¬ A D (pt p) (pt q) (star t) (orient t))
    (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) :
    DonorData D I pt ln p := by
  classical
  let a := pt p
  let U := G D a
  let opp (g : Fin D.size) : Bool := decide (a ∈ D.leftVars g)
  let src (g : Fin D.size) := univ.filter fun q =>
    q ≠ p ∧ (if g ∈ U then pt q ∈ vars D g (opp g) else g ∈ G D (pt q))
  let targets (g : Fin D.size) := univ.filter fun t : Fin 13 =>
    if g ∈ U then ∀ q ∈ src g, I q t else ∃ h : ¬ I p t, star ⟨t,h⟩ = g
  have hD (g : Fin D.size) := disjoint_left.mp (disj g)
  have inG {v : Vertex} {g : Fin D.size} {b : Bool} (h : v ∈ vars D g b) : g ∈ G D v :=
    mem_filter.mpr ⟨mem_univ _,by cases b; exact Or.inl h; exact Or.inr h⟩
  have rawOpp (g) (hg : g ∈ U) : a ∉ vars D g (opp g) ∧ a ∈ vars D g (!(opp g)) := by
    have := (mem_filter.mp hg).2
    by_cases hl : a ∈ D.leftVars g
    · simpa [opp,vars,hl] using hD g hl
    · simpa [opp,vars,hl] using this.resolve_left hl
  have srcP (g q) (h : q ∈ src g) : g ∈ G D (pt q) := by
    by_cases hg : g ∈ U
    · exact inG (by simpa [hg] using (mem_filter.mp h).2.2 : pt q ∈ vars D g (opp g))
    · simpa [hg] using (mem_filter.mp h).2.2
  have gatesSilent (i : Fin D.size) (hi : i ∉ U) (q) (hq : q ≠ p) :
      ¬ D.gateVal (pair a (pt q)) i = true := by
    obtain ⟨t,rfl⟩ := (outside i).mp hi
    exact fun h => (pts t q hq).2 (((sides_orient D hw _ _ _).mp h).1)

  have trace (q : Fin 13) (hq : q ≠ p) (i : Fin D.size) (hit : D.gateVal (pair a (pt q)) i = true) :
      ∃ j ∈ U, q ∈ src j ∧ ∀ r ∈ src j, D.gateVal (pair a (pt r)) i = true := by
    induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin D.size → Fin D.size → Prop)).induction with
    | h i ih =>
      have hi : i ∈ U := by by_contra hn; exact gatesSilent i hn q hq hit
      have ⟨absent,raw⟩ := rawOpp i hi
      have op (r) : A D a (pt r) i (opp i) → D.gateVal (pair a (pt r)) i = true := fun h =>
        (sides_orient D hw _ _ _).mpr ⟨h,side_raw raw (by simp [pair])⟩
      rcases ((sides_orient D hw _ _ (opp i)).mp hit).1 with ⟨v,hv,hin⟩|⟨k,hk,htrue⟩
      · rcases mem_insert.mp hin with e|e
        · exact (absent (e ▸ hv)).elim
        · have e' := mem_singleton.mp e
          have hq' : pt q ∈ vars D i (opp i) := e' ▸ hv
          refine ⟨i,hi,mem_filter.mpr ⟨mem_univ _,hq,by simpa [hi] using hq'⟩,?_⟩
          intro r hr
          exact op r (side_raw (by simpa [hi] using (mem_filter.mp hr).2.2 : pt r ∈ vars D i (opp i))
            (by simp [pair]))
      · have lt : k < i := by
          cases e : opp i <;> simp only [e,refs] at hk
          · exact (hw i).1 _ hk
          · exact (hw i).2 _ hk
        obtain ⟨j,hj,hqj,hall⟩ := ih _ lt htrue
        exact ⟨j,hj,hqj,fun r hr => op r (Or.inr ⟨k,hk,hall r hr⟩)⟩
  refine ⟨src,targets,srcP,?_,?_,?_,?_⟩
  · intro g q t hq ht
    have tt := (mem_filter.mp ht).2
    by_cases hg : g ∈ U
    · exact (ite_eq_left hg ▸ tt) q hq
    · obtain ⟨hn,rfl⟩ : ∃ h : ¬ I p t, star ⟨t,h⟩ = g := by simpa [hg] using tt
      let z : {t // ¬ I p t} := ⟨t,hn⟩
      have hs := pts z q (mem_filter.mp hq).2.1
      have sideHit : ∃ b, A D a (pt q) (star z) b := by
        rcases (mem_filter.mp (srcP _ _ hq)).2 with l|r
        · exact ⟨false,side_raw l (by simp [pair])⟩
        · exact ⟨true,side_raw r (by simp [pair])⟩
      obtain ⟨b,hb⟩ := sideHit
      have hn' : b ≠ orient z := fun e => hs.2 (e ▸ hb)
      exact hs.1.mp (Bool.eq_not_of_ne hn' ▸ hb)
  · intro g hg
    change g ∉ U at hg
    apply card_le_one.mpr
    intro t ht s hs
    obtain ⟨t',et⟩ : ∃ h : ¬ I p t, star ⟨t,h⟩ = g := by simpa [hg] using (mem_filter.mp ht).2
    obtain ⟨s',es⟩ : ∃ h : ¬ I p s, star ⟨s,h⟩ = g := by simpa [hg] using (mem_filter.mp hs).2
    exact congrArg Subtype.val (inj (et.trans es.symm))
  · intro q t hq hi ht
    let z : {t // ¬ I p t} := ⟨t,ht⟩
    let g := star z
    have out : g ∉ U := (outside g).mpr ⟨z,rfl⟩
    have sideHit := ((pts z q hq).1).mpr hi
    rcases sideHit with ⟨v,hv,hin⟩ | ⟨k,hk,htrue⟩
    · rcases mem_insert.mp hin with e|e
      · exact (out (inG (e ▸ hv))).elim
      · have e' := mem_singleton.mp e
        have hgq : g ∈ G D (pt q) := inG (e' ▸ hv)
        refine ⟨g,mem_filter.mpr ⟨mem_univ _,hq,by simpa [out] using hgq⟩,?_⟩
        exact mem_filter.mpr ⟨mem_univ _,by rw [ite_eq_right out]; exact ⟨ht,rfl⟩⟩
    · obtain ⟨j,hj,qj,all⟩ := trace q hq k htrue
      refine ⟨j,qj,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      rw [ite_eq_left hj]
      intro r hr
      exact ((pts z r (mem_filter.mp hr).2.1).1).mp (Or.inr ⟨k,hk,all r hr⟩)
  · intro g hg q hq t hp hqt
    change g ∈ U at hg
    have hraw : pt q ∈ vars D g (opp g) := by simpa [hg] using (mem_filter.mp hq).2.2
    have dis := hD g
    have hh := (mem_filter.mp hg).2
    change (pt p ∈ D.leftVars g ∧ ln t ∈ D.rightVars g) ∨
      (pt p ∈ D.rightVars g ∧ ln t ∈ D.leftVars g) at hp
    unfold Hit at hqt
    change pt q ∈ (if decide (pt p ∈ D.leftVars g) then D.rightVars g else D.leftVars g) at hraw
    by_cases l : pt p ∈ D.leftVars g <;> simp [l] at hraw <;> grind

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem threeDonorData (D : Circ) (hw : D.WellFormed) (sz : D.size = 12)
    (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (pt ln : Fin 13 → Vertex) (p : Fin 13)
    (degp : (G D (pt p)).card = 3) (zcard : Fintype.card {t // ¬ I p t} = 9)
    (each : ∀ t, ¬ I p t → ∃ q, I q t)
    (three : ∀ q, q ≠ p → 3 ≤ (univ.filter fun t => I q t ∧ ¬ I p t).card)
    (dpq : ∀ q, q ≠ p → D.eval (pair (pt p) (pt q)) = false)
    (dpl : ∀ t, ¬ I p t → D.eval (pair (pt p) (ln t)) = false)
    (pos : ∀ q t, I q t → D.eval {pt q,ln t} = true)
    (rowDiff : ∀ t u, ¬ I p t → ¬ I p u → t ≠ u → ∃ S : Finset Vertex,
      pt p ∈ S ∧ ln t ∈ S ∧ D.eval S = false ∧ D.eval (insert (ln u) S) = true)
    (rowBoth : ∀ t u, ¬ I p t → ¬ I p u → t ≠ u → ∃ S : Finset Vertex,
      pt p ∈ S ∧ D.eval S = false ∧ D.eval (insert (ln t) S) = true ∧ D.eval (insert (ln u) S) = true)
    (lbp : ∀ q, q ≠ p → LB D (pair (pt p) (pt q)) 6)
    (lbl : ∀ t, ¬ I p t → LB D (pair (pt p) (ln t)) 8)
    (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) : DonorData D I pt ln p := by
  obtain ⟨s,b,i,o,_,_,h⟩ := stars D hw sz I pt ln p degp zcard each three dpq dpl pos rowDiff rowBoth lbp lbl
  exact fromStars D hw I pt ln p s b i o h disj

end PEqualNP.Outside.L_meta_17461.Plane1898.Cofactor
namespace PEqualNP.Outside.L_meta_17461.Plane1898

open Finset PEqualNP.AndCount

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem donorCover (D : AndCountCircuit 26) (out : D.outVars = ∅)
    (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i))
    (d : Bool) (pos : donorPos D) (q t : Fin 13) (h : donorI d q t) :
    ∃ g, Cofactor.Hit D (donorP d) (donorL d) q t g := by
  let x := donorP d q
  let y := donorL d t
  have target := donorDualPos D pos d q t h
  change D.eval {x,y} = true at target
  simp [AndCountCircuit.eval, out] at target
  obtain ⟨i,_,hi⟩ := target
  suffices aux : ∀ (k : ℕ) (j : Fin D.size), D.gateValFuel {x,y} k j = true →
      ∃ g, Cofactor.Hit D (donorP d) (donorL d) q t g from aux D.size i hi
  intro k
  induction k with
  | zero => intro _ hv; cases hv
  | succ k ih =>
    intro j hj
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true, AndCountCircuit.sideTrue,
      decide_eq_true_eq, mem_insert, mem_singleton] at hj
    rcases hj.1 with ⟨a,ha,rfl | rfl⟩ | ⟨z,_,_,hz⟩
    · rcases hj.2 with ⟨b,hb,rfl | rfl⟩ | ⟨z,_,_,hz⟩
      · exact (disjoint_left.mp (disj j) ha hb).elim
      · exact ⟨j,Or.inl ⟨ha,hb⟩⟩
      · exact ih z hz
    · rcases hj.2 with ⟨b,hb,rfl | rfl⟩ | ⟨z,_,_,hz⟩
      · exact ⟨j,Or.inr ⟨hb,ha⟩⟩
      · exact (disjoint_left.mp (disj j) ha hb).elim
      · exact ih z hz
    · exact ih z hz

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem size12CapTwo (D : AndCountCircuit 26)
    (hw : D.WellFormed) (sz : D.size = 12) (out : D.outVars = ∅)
    (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i))
    (pos : donorPos D) (neg : donorNeg D)
    (cap : ∀ v, (Cofactor.G D v).card ≤ 3)
    (lbp : ∀ (d : Bool) (p q : Fin 13), q ≠ p →
      Cofactor.LB D {donorP d p,donorP d q} 6)
    (lbl : ∀ (d : Bool) (p t : Fin 13), ¬ donorI d p t →
      Cofactor.LB D {donorP d p,donorL d t} 8) :
    ∀ v, (Cofactor.G D v).card ≤ 2 := by
  have all (d : Bool) (p : Fin 13) : (Cofactor.G D (donorP d p)).card ≤ 2 := by
    by_contra! big
    have b := cap (donorP d p)
    have deg : (Cofactor.G D (donorP d p)).card = 3 := by omega
    obtain ⟨rays,four,each,three,zcard⟩ := donorCounts d p
    obtain ⟨dpq,dpl,rowDiff,rowBoth⟩ := donorRows D pos neg d p
    obtain ⟨src,targets,srcP,aligned,one,reach,opposed⟩ :=
      Cofactor.threeDonorData D hw sz (donorI d) (donorP d) (donorL d) p deg zcard
        (fun t _ => each t) three dpq dpl (donorDualPos D pos d) rowDiff rowBoth
        (lbp d p) (lbl d p) disj
    refine threeDonorsImpossible (donorI d) (fun q => Cofactor.G D (donorP d q))
      (fun t => Cofactor.G D (donorL d t)) p deg (fun _ => cap _) (fun _ => cap _)
      rays four three (fun {a b t u} => donorUnique d) src targets srcP aligned one reach
      (Cofactor.Hit D (donorP d) (donorL d)) (donorCover D out disj d pos) ?_ ?_ opposed
    · intro q t g hg
      exact mem_filter.mpr ⟨mem_univ _, hg.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
    · intro q t g hg
      exact mem_filter.mpr ⟨mem_univ _, hg.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)⟩
  intro v
  induction v using (Fin.addCases (m := 13) (n := 13)) with
  | left p => exact all false p
  | right l => exact all true l

end PEqualNP.Outside.L_meta_17461.Plane1898

namespace PEqualNP.Outside.L_meta_17461

namespace PGCapTwo
open Finset

abbrev Point := Fin 13

abbrev inc (dual : Bool) (p l : Point) : Prop :=
  let a := if dual then l else p
  let b := if dual then p else l
  a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9

def fiber {S : Type*} [DecidableEq S] (f : Point → S) (s : S) : Finset Point :=
  univ.filter fun p => f p = s

def weight (dual : Bool) (B : Finset Point) : ℕ :=
  if 6 ≤ B.card then 0 else if B.card = 5 then 1
  else if B.card = 4 ∨ (B.card = 3 ∧ ∃ l : Point, ∀ p ∈ B, inc dual p l) then 2 else B.card

end PGCapTwo

namespace PGCapTwo
open Finset

private theorem mixDegree : ∀ (d : Bool) (l : Point),
    (Finset.univ.filter fun p => inc d p l).card = 4 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
private theorem mixCodegree : ∀ (d : Bool) (l k : Point), l ≠ k →
    (Finset.univ.filter fun p => inc d p l ∧ inc d p k).card ≤ 1 := by decide +kernel

private theorem mixUnique {d : Bool} {l k : Point} {C : Finset Point} (hC : 2 ≤ C.card)
    (h : ∀ p ∈ C, inc d p l ∧ inc d p k) : l = k := by
  by_contra hne
  have hs : C ⊆ Finset.univ.filter (fun p => inc d p l ∧ inc d p k) :=
    fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h p hp⟩
  have := (Finset.card_le_card hs).trans (mixCodegree d l k hne)
  omega

theorem mixedBound (dual : Bool) (B M : Finset Point) (w : Point → Point)
    (hm : M ⊆ B) (hc : ∀ l : Point, (M.filter (fun p => w p = l)).card ≤ 2)
    (ha : ∀ p ∈ M, ∀ q ∈ B, q ≠ p → inc dual q (w p)) : M.card ≤ weight dual B := by
  classical
  have deg (C : Finset Point) (l : Point) (h : ∀ q ∈ C, inc dual q l) : C.card ≤ 4 := by
    have hs : C ⊆ Finset.univ.filter (fun p => inc dual p l) :=
      fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h p hp⟩
    exact (Finset.card_le_card hs).trans_eq (mixDegree dual l)
  have eqOfFour (hB : 4 ≤ B.card) (p : Point) (hp : p ∈ M) (r : Point) (hr : r ∈ M) :
      w p = w r := by
    by_cases hpr : r = p
    · rw [hpr]
    have hrc : r ∈ B.erase p := Finset.mem_erase.mpr ⟨hpr, hm hr⟩
    apply mixUnique (C := (B.erase p).erase r)
    · rw [Finset.card_erase_of_mem hrc, Finset.card_erase_of_mem (hm hp)]
      omega
    · intro q hq
      obtain ⟨hqr, hq'⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqp, hqB⟩ := Finset.mem_erase.mp hq'
      exact ⟨ha p hp q hqB hqp, ha r hr q hqB hqr⟩
  have boundOfConstant (l : Point) (h : ∀ p ∈ M, w p = l) : M.card ≤ 2 := by
    exact (Finset.card_le_card (t := M.filter (fun p => w p = l))
      (fun p hp => Finset.mem_filter.mpr ⟨hp, h p hp⟩)).trans (hc l)
  unfold weight
  split
  · rename_i hB
    by_contra h
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
    have hdeg := deg (B.erase p) (w p) fun q hq =>
      ha p hp q (Finset.mem_erase.mp hq).2 (Finset.mem_erase.mp hq).1
    rw [Finset.card_erase_of_mem (hm hp)] at hdeg
    omega
  split
  · rename_i hB
    by_contra h
    obtain ⟨p, hp, r, hr, hpr⟩ := Finset.one_lt_card.mp (by omega : 1 < M.card)
    have he := eqOfFour (by omega) p hp r hr
    have hdeg : B.card ≤ 4 := deg B (w p) fun q hq => by
      by_cases hqp : q = p
      · rw [hqp, he]
        exact ha r hr p (hm hp) hpr
      · exact ha p hp q hq hqp
    omega
  split
  · rename_i hB
    rcases hB with h4 | ⟨h3, l, hl⟩
    · by_cases h : 0 < M.card
      · obtain ⟨p, hp⟩ := Finset.card_pos.mp h
        exact boundOfConstant (w p) (fun q hq => eqOfFour (by omega) q hq p hp)
      · omega
    · apply boundOfConstant l
      intro p hp
      apply mixUnique (C := B.erase p)
      · rw [Finset.card_erase_of_mem (hm hp), h3]
      · intro q hq
        obtain ⟨hqp, hqB⟩ := Finset.mem_erase.mp hq
        exact ⟨ha p hp q hqB hqp, hl q hqB⟩
  · exact Finset.card_le_card hm

end PGCapTwo

namespace PGCapTwo
open Finset

private theorem privateChoice {S : Type*} [DecidableEq S] (A : Point → Finset S)
    (cap : ∀ p, (A p).card ≤ 2)
    (sep : ∀ p q r, q ≠ p → r ≠ p → ¬ A p ⊆ A q ∪ A r) :
    ∀ p, ∃ s ∈ A p, ∀ q, s ∈ A q → q = p := by
  classical
  intro p
  by_contra! hn
  obtain ⟨z,hz⟩ : ∃ z : Point, z ≠ p := by
    by_cases h : p = 0
    · exact ⟨1,by simp [h]⟩
    · exact ⟨0,Ne.symm h⟩
  have hc := cap p
  interval_cases k : (A p).card
  · apply sep p z z hz hz
    simp [card_eq_zero.mp k]
  · obtain ⟨s,hs⟩ := card_eq_one.mp k
    obtain ⟨q,hq,hne⟩ := hn s (by simp [hs])
    exact sep p q q hne hne (by simp [hs,hq])
  · obtain ⟨s,t,_,hs⟩ := card_eq_two.mp k
    obtain ⟨q,hq,hne⟩ := hn s (by simp [hs])
    obtain ⟨r,hr,hrne⟩ := hn t (by simp [hs])
    exact sep p q r hne hrne (by
      rw [hs]
      exact insert_subset_iff.mpr ⟨mem_union_left _ hq, singleton_subset_iff.mpr (mem_union_right _ hr)⟩)

private theorem oneColor {S : Type*} [DecidableEq S] (dual : Bool) (A B : Point → Finset S)
    (capA : ∀ p, (A p).card ≤ 2) (capB : ∀ l, (B l).card ≤ 2)
    (same : ∀ p q r, q ≠ p → r ≠ p → ¬ A p ⊆ A q ∪ A r)
    (mixed : ∀ p q l, q ≠ p → A p ⊆ A q ∪ B l → inc dual q l)
    (opp : S → S)
    (cover : ∀ p l, inc dual p l → ∃ t ∈ B l, opp t ∈ A p)
    (geoBound' : ∀ f : Point → S,
      (∀ l, ((univ.filter (fun p => inc dual p l)).image f).card ≤ 2) →
      (∑ s ∈ univ.image f, weight dual (fiber f s)) ≤
        ((univ.image f).filter (fun s => 1 < (fiber f s).card)).card + 1)
    (mixedBound' : ∀ (U M : Finset Point) (w : Point → Point), M ⊆ U →
      (∀ l, (M.filter (fun p => w p = l)).card ≤ 2) →
      (∀ p ∈ M, ∀ q ∈ U, q ≠ p → inc dual q (w p)) → M.card ≤ weight dual U) :
    ∃ T ⊆ univ.biUnion A, 25 + (T ∩ univ.biUnion B).card ≤ 2 * T.card := by
  classical
  choose d hd hdunique using privateChoice A capA same
  have dinj : Function.Injective d := by
    intro p q eq
    exact hdunique q p (eq ▸ hd p)

  have pair (p : Point) : ∃ t ∈ A p, A p ⊆ {d p, t} := by
    by_cases h : ((A p).erase (d p)).Nonempty
    · obtain ⟨t,ht⟩ := h
      have hk := card_erase_add_one (hd p)
      have hc := capA p
      have he : ((A p).erase (d p)).card ≤ 1 := by omega
      refine ⟨t,mem_of_mem_erase ht,?_⟩
      intro k h
      by_cases h' : k = d p
      · simp [h']
      · simp [card_le_one.mp he k (mem_erase.mpr ⟨h',h⟩) t ht]
    · refine ⟨d p,hd p,?_⟩
      intro k hk
      by_cases he : k = d p
      · simp [he]
      · exact (h ⟨k,mem_erase.mpr ⟨he,hk⟩⟩).elim
  choose f hf hpair using pair
  have label (s : S) (p q : Point) (hp : s ∈ A p) (hq : s ∈ A q) : f p = f q := by
    by_cases e : p = q
    · simp [e]
    have ep : s ≠ d p := fun h => e (hdunique p q (h ▸ hq)).symm
    have eq : s ≠ d q := fun h => e (hdunique q p (h ▸ hp))
    have h1 := hpair p hp
    have h2 := hpair q hq
    simp only [mem_insert, mem_singleton] at h1 h2
    exact ((h1.resolve_left ep).symm).trans (h2.resolve_left eq)
  have rep (s : S) : ∃ u : S, ∀ p, s ∈ A p → f p = u := by
    by_cases h : ∃ p, s ∈ A p
    · obtain ⟨q,hq⟩ := h
      exact ⟨f q,fun p hp => label s p q hp hq⟩
    · exact ⟨f 0,fun p hp => (h ⟨p,hp⟩).elim⟩
  choose c hc using rep

  have nr (l : Point) : ((univ.filter (fun p => inc dual p l)).image f).card ≤ 2 := by
    refine (card_le_card (t := (B l).image (fun t => c (opp t))) ?_).trans
      (card_image_le.trans (capB l))
    intro u hu
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hu
    obtain ⟨t,ht,htp⟩ := cover p l (mem_filter.mp hp).2
    exact mem_image.mpr ⟨t,ht,(hc _ p htp).symm⟩
  let K := univ.image f
  let C := K.filter fun s => 1 < (fiber f s).card
  let D := univ.image d
  have hsubC : C ⊆ K := filter_subset _ _
  have hdis : Disjoint D C := by
    apply disjoint_left.mpr
    intro s hs hcs
    obtain ⟨p,_,rfl⟩ := mem_image.mp hs
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (mem_filter.mp hcs).2
    have ha' : f a = d p := (mem_filter.mp ha).2
    have hb' : f b = d p := (mem_filter.mp hb).2
    exact hab ((hdunique p a (ha' ▸ hf a)).trans (hdunique p b (hb' ▸ hf b)).symm)
  have hD : D.card = 13 := by
    simp [D,card_image_of_injective _ dinj,Point]
  let Y := univ.biUnion B
  let M := univ.filter fun p => d p ∈ Y
  have witness (p : Point) : ∃ l : Point, p ∈ M → d p ∈ B l := by
    by_cases h : p ∈ M
    · obtain ⟨l,_,hl⟩ := mem_biUnion.mp (mem_filter.mp h).2
      exact ⟨l,fun _ => hl⟩
    · exact ⟨0,fun hm => (h hm).elim⟩
  choose w hw using witness
  have hmf (s : S) : (M.filter fun p => f p = s).card ≤ weight dual (fiber f s) := by
    apply mixedBound' (fiber f s) _ w
    · intro p hp
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
    · intro l
      refine (card_le_card_of_injOn (t := B l) d ?_ dinj.injOn).trans (capB l)
      intro p hp
      obtain ⟨hps,hl⟩ := (mem_filter.mp hp)
      exact hl ▸ hw p (mem_filter.mp hps).1
    · intro p hp q hq hne
      obtain ⟨hmp,hfp⟩ := mem_filter.mp hp
      have hfq : f q = s := (mem_filter.mp hq).2
      apply mixed p q _ hne
      apply (hpair p).trans
      refine insert_subset_iff.mpr ⟨mem_union_right _ (hw _ hmp),
        singleton_subset_iff.mpr (mem_union_left _ ?_)⟩
      simpa only [hfp,hfq] using hf q
  have hM : M.card ≤ C.card + 1 := by
    calc
      M.card = ∑ s ∈ K, (M.filter (fun p => f p = s)).card :=
        card_eq_sum_card_fiberwise (fun p _ => mem_image_of_mem f (mem_univ p))
      _ ≤ ∑ s ∈ K, weight dual (fiber f s) := sum_le_sum (fun s _ => hmf s)
      _ ≤ C.card + 1 := geoBound' f nr
  have deq : D ∩ Y = M.image d := by
    ext s
    simp only [D,M,mem_inter,mem_image, mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨⟨p,rfl⟩,hp⟩
      exact ⟨p,hp,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p,rfl⟩,hp⟩
  have incl : (D ∪ C) ∩ Y ⊆ (D ∩ Y) ∪ C := by
    intro s hs
    obtain ⟨h,hy⟩ := mem_inter.mp hs
    exact (mem_union.mp h).elim (fun hd' => mem_union_left _ (mem_inter.mpr ⟨hd',hy⟩))
      (mem_union_right _)

  refine ⟨D ∪ C, ?_, ?_⟩
  · intro s hs
    rcases mem_union.mp hs with hd' | hcs
    · obtain ⟨p,_,rfl⟩ := mem_image.mp hd'
      exact mem_biUnion.mpr ⟨p,mem_univ _,hd _⟩
    · obtain ⟨p,_,rfl⟩ := mem_image.mp (hsubC hcs)
      exact mem_biUnion.mpr ⟨p,mem_univ _,hf _⟩
  · have bound := (card_le_card incl).trans (card_union_le _ _)
    rw [deq,card_image_of_injective _ dinj] at bound
    change 25 + ((D ∪ C) ∩ Y).card ≤ 2 * (D ∪ C).card
    rw [card_union_of_disjoint hdis,hD]
    omega

end PGCapTwo
namespace PGCapTwo
open Finset

def geoSet (m : Nat) : Finset Point :=
  univ.filter (fun p => m.testBit p.val)

@[simp] theorem geoSet_mem (m : Nat) (p : Point) :
    p ∈ geoSet m ↔ m.testBit p.val = true := by
  simp [geoSet]

private def geoLines (dual : Bool) : List Nat :=
  if dual then [5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664]
  else [523, 1046, 2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357]

def geoLine (dual : Bool) (l : Point) : Nat :=
  (geoLines dual)[l.val]'(by cases dual <;> exact l.isLt)

theorem geoLine_spec (dual : Bool) (p l : Point) :
    (geoLine dual l).testBit p.val = true ↔ inc dual p l := by
  revert dual p l
  decide +kernel

private theorem geoLines_eq (dual : Bool) :
    geoLines dual = List.ofFn (geoLine dual) := by
  cases dual <;> decide

private def geoCountAux (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => geoCountAux m n + (m.testBit n).toNat

def geoCount (m : Nat) : Nat := geoCountAux m 13

private theorem geoCountAux_spec (m n : Nat) :
    geoCountAux m n = ((range n).filter fun i => m.testBit i).card := by
  induction n with
  | zero => simp [geoCountAux]
  | succ n ih =>
    rw [geoCountAux, ih, range_add_one]
    cases hb : m.testBit n <;> simp [filter_insert, hb]

theorem geoCount_spec {m : Nat} (_hm : m < 8192) : geoCount m = (geoSet m).card := by
  rw [geoCount, geoCountAux_spec]
  symm
  refine card_bij' (fun p _ => p.val) (fun i hi => ⟨i, (mem_range.mp (mem_filter.mp hi).1)⟩)
    (fun p hp => mem_filter.mpr ⟨mem_range.mpr p.isLt, (geoSet_mem _ _).mp hp⟩)
    (fun i hi => (geoSet_mem _ _).mpr (mem_filter.mp hi).2) (fun _ _ => rfl) (fun _ _ => rfl)

theorem geoHit_spec (dual : Bool) {m : Nat} (hm : m < 8192) (l : Point) :
    (m &&& geoLine dual l != 0) = true ↔ ((geoSet m).filter (fun p => inc dual p l)).Nonempty := by
  rw [bne_iff_ne]
  constructor
  · intro hn
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hn
    rw [Nat.testBit_and, Bool.and_eq_true] at hi
    have hil : i < 13 := by
      by_contra! hc
      have hb : m < 2 ^ i :=
        lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0 < 2) hc)
      rw [Nat.testBit_lt_two_pow hb] at hi
      simp at hi
    exact ⟨⟨i, hil⟩, mem_filter.mpr ⟨(geoSet_mem _ _).mpr hi.1, (geoLine_spec dual _ _).mp hi.2⟩⟩
  · rintro ⟨p, hp⟩ hz
    obtain ⟨hp, hl⟩ := mem_filter.mp hp
    have he : (m &&& geoLine dual l).testBit p.val = true := by
      simp only [Nat.testBit_and, Bool.and_eq_true]
      exact ⟨(geoSet_mem _ _).mp hp, (geoLine_spec dual _ _).mpr hl⟩
    simp [hz] at he

private theorem geoSubsetLine (dual : Bool) {m : Nat} (hm : m < 8192) (l : Point) :
    (m &&& geoLine dual l = m) ↔ ∀ p ∈ geoSet m, inc dual p l := by
  rw [Nat.eq_iff_testBit_eq]
  simp only [Nat.testBit_and, geoSet_mem, ← geoLine_spec]
  constructor
  · intro h p hp
    simpa [hp] using h p.val
  · intro h i
    cases hb : m.testBit i with
    | false => simp
    | true =>
      have hil : i < 13 := by
        by_contra! hc
        have hb' : m < 2 ^ i :=
          lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0 < 2) hc)
        simp [Nat.testBit_lt_two_pow hb'] at hb
      simpa using h ⟨i, hil⟩ hb

def geoWeight (dual : Bool) (m : Nat) : Nat :=
  let c := geoCount m
  if 6 ≤ c then 0 else if c = 5 then 1
  else if c = 4 ∨ (c = 3 ∧ (geoLines dual).any (fun b => (m &&& b) == m)) then 2 else c

theorem geoWeight_spec (dual : Bool) {m : Nat} (hm : m < 8192) :
    geoWeight dual m = weight dual (geoSet m) := by
  have h : ((geoLines dual).any (fun b => (m &&& b) == m)) = true ↔
      ∃ l, ∀ p ∈ geoSet m, inc dual p l := by
    simp only [geoLines_eq, List.any_eq_true, List.mem_ofFn, beq_iff_eq]
    constructor
    · rintro ⟨b, ⟨l, rfl⟩, hl⟩
      exact ⟨l, (geoSubsetLine dual hm l).mp hl⟩
    · rintro ⟨l, hl⟩
      exact ⟨geoLine dual l, ⟨l, rfl⟩, (geoSubsetLine dual hm l).mpr hl⟩
  unfold geoWeight weight
  dsimp only
  simp only [geoCount_spec hm, h]

end PGCapTwo

namespace PGCapTwo

def geoNext (b : Nat) : List Nat → List (List Nat)
  | [] => [[b]]
  | a :: as => ((a ||| b) :: as) :: (geoNext b as).map (a :: ·)

def geoValid (dual : Bool) (ms : List Nat) : Bool :=
  if ms.length ≤ 2 then true else
    (List.finRange 13).all fun l =>
      decide ((ms.filter (fun m => (m &&& geoLine dual l) != 0)).length ≤ 2)

theorem geoValid_eq (dual : Bool) (ms : List Nat) :
    geoValid dual ms = true ↔
      ∀ l : Point, (ms.filter (fun m => (m &&& geoLine dual l) != 0)).length ≤ 2 := by
  unfold geoValid
  split
  next h =>
    exact ⟨fun _ l => (List.length_filter_le _ _).trans h, fun _ => rfl⟩
  next =>
    simp only [List.all_eq_true, decide_eq_true_eq, List.mem_finRange, true_implies]

def geoSearch (dual : Bool) (ms : List Nat) : List Nat → Bool
  | [] => decide ((ms.map (geoWeight dual)).sum ≤ (ms.filter (fun m => 1 < geoCount m)).length + 1)
  | i :: is => (geoNext (2 ^ i) ms).all fun ms' => !geoValid dual ms' || geoSearch dual ms' is

end PGCapTwo

namespace PGCapTwo
open Finset

private def prefixMask {S : Type*} [DecidableEq S] (f : Point → S) (s : S) :
    List Point → Nat
  | [] => 0
  | p :: ps =>
    if f p = s then prefixMask f s ps ||| 2^p.val else prefixMask f s ps

private theorem prefixMask_lt {S : Type*} [DecidableEq S] (f : Point → S) (s : S)
    (ps : List Point) : prefixMask f s ps < 8192 := by
  induction ps with
  | nil => simp [prefixMask]
  | cons p ps ih =>
    dsimp [prefixMask]
    split
    · apply Nat.or_lt_two_pow (n := 13) ih
      exact Nat.pow_lt_pow_right (by decide) p.isLt
    · exact ih

private theorem prefixMask_mem {S : Type*} [DecidableEq S] (f : Point → S) (s : S)
    (ps : List Point) (q : Point) :
    q ∈ geoSet (prefixMask f s ps) ↔ q ∈ ps ∧ f q = s := by
  simp only [geoSet, mem_filter, mem_univ, true_and]
  induction ps with
  | nil => simp [prefixMask]
  | cons p ps ih =>
    by_cases h : f p = s
    · simp only [prefixMask, h, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true,
        Nat.testBit_two_pow, decide_eq_true_eq, Fin.val_inj, ih, List.mem_cons]
      grind
    · simp only [prefixMask, h, ↓reduceIte, ih, List.mem_cons]
      grind

private theorem prefixMask_zero {S : Type*} [DecidableEq S] (f : Point → S) (s : S)
    (ps : List Point) (h : ∀ p ∈ ps, f p ≠ s) : prefixMask f s ps = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [prefixMask, h p (by simp), ↓reduceIte]
    exact ih (fun q hq => h q (by simp [hq]))

private def geoPush {S : Type*} [DecidableEq S] (s : S) (keys : List S) : List S :=
  if s ∈ keys then keys else keys ++ [s]

private theorem geoPush_mem {S : Type*} [DecidableEq S] (s t : S) (keys : List S) :
    t ∈ geoPush s keys ↔ t = s ∨ t ∈ keys := by
  simp only [geoPush]
  split <;> simp_all
  grind

private theorem geoPush_nodup {S : Type*} [DecidableEq S] (s : S) (keys : List S)
    (hk : keys.Nodup) : (geoPush s keys).Nodup := by
  simp only [geoPush]
  split
  · exact hk
  · simp [List.nodup_append, hk]
    grind

private theorem prefixMask_next {S : Type*} [DecidableEq S] (f : Point → S) (p : Point)
    (ps : List Point) (keys : List S) (hk : keys.Nodup)
    (hz : f p ∉ keys → prefixMask f (f p) ps = 0) :
    ((geoPush (f p) keys).map fun s => prefixMask f s (p :: ps)) ∈
      geoNext (2^p.val) (keys.map fun s => prefixMask f s ps) := by
  induction keys with
  | nil =>
    simp [geoPush, prefixMask, geoNext, hz (by simp)]
  | cons k ks ih =>
    obtain ⟨hnot, hnod⟩ := List.nodup_cons.mp hk
    by_cases heq : f p = k
    · have htail : (ks.map fun s => prefixMask f s (p::ps)) =
          (ks.map fun s => prefixMask f s ps) := by
        apply List.map_congr_left
        intro s hs
        have hne : f p ≠ s := by grind
        simp [prefixMask, hne]
      have hpush : geoPush (f p) (k::ks) = k::ks := by simp [geoPush, heq]
      rw [hpush, List.map_cons, List.map_cons, htail, geoNext]
      apply List.mem_cons.mpr
      left
      simp [prefixMask, heq]
    · have hrec := ih hnod (fun hn => hz (by simp [heq, hn]))
      have hpush : geoPush (f p) (k::ks) = k :: geoPush (f p) ks := by
        by_cases hm : f p ∈ ks <;> simp [geoPush, heq, hm]
      rw [hpush, List.map_cons, List.map_cons, geoNext]
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      exact ⟨_, hrec, by simp [prefixMask, heq]⟩

private theorem prefixMask_valid {S : Type*} [DecidableEq S] (dual : Bool) (f : Point → S)
    (nr : ∀ l : Point, ((univ.filter (fun p => inc dual p l)).image f).card ≤ 2)
    (ps : List Point) (keys : List S) (hk : keys.Nodup) :
    geoValid dual (keys.map fun s => prefixMask f s ps) = true := by
  apply (geoValid_eq _ _).mpr
  intro l
  rw [List.filter_map, List.length_map]
  let pred := fun s => (prefixMask f s ps &&& geoLine dual l) != 0
  change (keys.filter pred).length ≤ 2
  rw [← List.toFinset_card_of_nodup (hk.filter pred)]
  apply le_trans (Finset.card_le_card ?_) (nr l)
  intro s hs
  have hh := (List.mem_filter.mp (List.mem_toFinset.mp hs)).2
  obtain ⟨q, hq⟩ := (geoHit_spec dual (prefixMask_lt f s ps) l).mp hh
  obtain ⟨hmem, hinc⟩ := Finset.mem_filter.mp hq
  exact mem_image.mpr ⟨q, by simp [hinc], ((prefixMask_mem f s ps q).mp hmem).2⟩

private theorem prefixMask_finish {S : Type*} [DecidableEq S] (dual : Bool) (f : Point → S)
    (ps : List Point) (keys : List S) (hk : keys.Nodup)
    (hc : ∀ s, s ∈ keys ↔ ∃ p ∈ ps, f p = s) (hall : ∀ p, p ∈ ps)
    (hcheck : geoSearch dual (keys.map fun s => prefixMask f s ps) [] = true) :
    (∑ s ∈ univ.image f, weight dual (fiber f s)) ≤
      ((univ.image f).filter (fun s => 1 < (fiber f s).card)).card + 1 := by
  have hset (s : S) : geoSet (prefixMask f s ps) = fiber f s := by
    ext p
    simp only [prefixMask_mem, hall, fiber, mem_filter, mem_univ, true_and]
  have heq : keys.toFinset = univ.image f := by
    ext s
    simp [hc, hall]
  have hw (s : S) : geoWeight dual (prefixMask f s ps) = weight dual (fiber f s) := by
    rw [geoWeight_spec _ (prefixMask_lt ..), hset]
  have hn (s : S) : geoCount (prefixMask f s ps) = (fiber f s).card := by
    rw [geoCount_spec (prefixMask_lt ..), hset]
  simp only [geoSearch, decide_eq_true_eq, List.map_map, Function.comp_def, hw,
    List.filter_map, List.length_map, hn] at hcheck
  rw [← heq, List.sum_toFinset _ hk, List.filter_toFinset, List.toFinset_card_of_nodup (hk.filter _)]
  exact hcheck

private theorem geoReplay {S : Type*} [DecidableEq S] (dual : Bool) (f : Point → S)
    (nr : ∀ l : Point, ((univ.filter (fun p => inc dual p l)).image f).card ≤ 2)
    (todo ps : List Point) (keys : List S) (hk : keys.Nodup)
    (hc : ∀ s, s ∈ keys ↔ ∃ p ∈ ps, f p = s) (hall : ∀ q, q ∈ ps ∨ q ∈ todo)
    (hcheck : geoSearch dual (keys.map fun s => prefixMask f s ps) (todo.map Fin.val) = true) :
    (∑ s ∈ univ.image f, weight dual (fiber f s)) ≤
      ((univ.image f).filter (fun s => 1 < (fiber f s).card)).card + 1 := by
  induction todo generalizing ps keys with
  | nil =>
    exact prefixMask_finish _ _ ps keys hk hc (by simpa using hall) hcheck
  | cons p todo ih =>
    have hz (hn : f p ∉ keys) : prefixMask f (f p) ps = 0 := by
      apply prefixMask_zero
      intro q hq he
      exact hn ((hc _).mpr ⟨q, hq, he⟩)
    let ks := geoPush (f p) keys
    have hkn : ks.Nodup := geoPush_nodup _ _ hk
    apply ih (p::ps) ks hkn
    · intro s
      simp only [ks, geoPush_mem, hc, List.mem_cons]
      grind
    · intro q
      specialize hall q
      simp only [List.mem_cons] at *
      tauto
    · simp only [List.map_cons, geoSearch, List.all_eq_true] at hcheck
      have hc' := hcheck _ (prefixMask_next f p ps keys hk hz)
      simpa [prefixMask_valid dual f nr (p::ps) ks hkn, ks] using hc'

end PGCapTwo

namespace PGCapTwo
open Finset

private theorem geoCheckedTriangle : ∀ d : Bool,
    geoSearch d [1,2,4] [3,4,5,6,7,8,9,10,11,12] = true := by decide +kernel

private theorem geoNormalized {S : Type*} [DecidableEq S] (d : Bool) (f : Point → S)
    (nr : ∀ l : Point, ((univ.filter (fun p => inc d p l)).image f).card ≤ 2)
    (h01 : f 0 ≠ f 1) (h02 : f 0 ≠ f 2) (h12 : f 1 ≠ f 2) :
    (∑ s ∈ univ.image f, weight d (fiber f s)) ≤
      ((univ.image f).filter (fun s => 1 < (fiber f s).card)).card + 1 := by
  let todo : List Point := [3,4,5,6,7,8,9,10,11,12]
  apply geoReplay d f nr todo [2,1,0] [f 0,f 1,f 2]
  · simp [h01,h02,h12]
  · intro s
    simp
    grind
  · decide
  · have eq : ([f 0,f 1,f 2].map fun s => prefixMask f s [2,1,0]) = [1,2,4] := by
      simp [prefixMask,h01,h02,h12,Ne.symm h01,Ne.symm h02,Ne.symm h12]
    rw [eq]
    exact geoCheckedTriangle d

private theorem geoNormalize_bound {S : Type*} [DecidableEq S] (d : Bool) (f : Point → S)
    (nr : ∀ l : Point, ((univ.filter (fun p => inc d p l)).image f).card ≤ 2)
    (h : 2 < (univ.image f).card)
    (transitive : ∀ a b c : Point, a ≠ b → (¬∃ l, inc d a l ∧ inc d b l ∧ inc d c l) →
      ∃ π : Point ≃ Point, ∃ σ : Point ≃ Point,
      (∀ p l, inc d (π p) (σ l) ↔ inc d p l) ∧ π 0 = a ∧ π 1 = b ∧ π 2 = c) :
    (∑ s ∈ univ.image f, weight d (fiber f s)) ≤
      ((univ.image f).filter (fun s => 1 < (fiber f s).card)).card + 1 := by
  obtain ⟨ka,hka,kb,hkb,kc,hkc,hab,hac,hbc⟩ := two_lt_card.mp h
  obtain ⟨a,_,rfl⟩ := mem_image.mp hka
  obtain ⟨b,_,rfl⟩ := mem_image.mp hkb
  obtain ⟨c,_,rfl⟩ := mem_image.mp hkc
  have nc : ¬∃ l, inc d a l ∧ inc d b l ∧ inc d c l := by
    rintro ⟨l,ha,hb,hc⟩
    have mem (p : Point) (hp : inc d p l) :
        f p ∈ (univ.filter (fun q => inc d q l)).image f :=
      mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hp⟩)
    have hh := two_lt_card.mpr ⟨f a,mem _ ha,f b,mem _ hb,f c,mem _ hc,hab,hac,hbc⟩
    have := nr l
    omega
  obtain ⟨π,σ,pres,pa,pb,pc⟩ := transitive a b c (fun he => hab (congrArg f he)) nc
  let g : Point → S := fun p => f (π p)
  have ng (l : Point) : ((univ.filter (fun p => inc d p l)).image g).card ≤ 2 := by
    refine (card_le_card ?_).trans (nr (σ l))
    intro s hs
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hs
    apply mem_image.mpr
    exact ⟨π p, mem_filter.mpr ⟨mem_univ _,(pres p l).mpr (mem_filter.mp hp).2⟩, rfl⟩
  have small := geoNormalized d g ng (by simpa [g,pa,pb] using hab)
    (by simpa [g,pa,pc] using hac) (by simpa [g,pb,pc] using hbc)
  have himg : univ.image g = univ.image f := by
    ext s
    simp only [mem_image,mem_univ,true_and]
    exact ⟨fun ⟨p,hp⟩ => ⟨π p,hp⟩,fun ⟨p,hp⟩ => ⟨π.symm p,by simpa [g] using hp⟩⟩
  have hcard (s : S) : (fiber g s).card = (fiber f s).card := by
    have e : (fiber g s).map π.toEmbedding = fiber f s := by
      ext p
      simp [mem_map_equiv,fiber,g]
    rw [← e,card_map]
  have hweight (s : S) : weight d (fiber g s) = weight d (fiber f s) := by
    have hc : (∃ l, ∀ q ∈ fiber g s, inc d q l) ↔ (∃ l, ∀ q ∈ fiber f s, inc d q l) := by
      constructor
      · rintro ⟨l,hl⟩
        refine ⟨σ l, fun q hq => ?_⟩
        have hh := (pres (π.symm q) l).mpr (hl (π.symm q) (by simpa [fiber,g] using hq))
        simpa using hh
      · rintro ⟨l,hl⟩
        refine ⟨σ.symm l, fun q hq => ?_⟩
        have hh := hl (π q) (by simpa [fiber,g] using hq)
        exact (pres q (σ.symm l)).mp (by simpa using hh)
    simp only [weight,hcard,hc]
  simpa only [himg,hcard,hweight] using small

end PGCapTwo
namespace PGCapTwo
open Finset

private theorem geoSmall {S : Type*} [DecidableEq S] (dual : Bool) (f : Point → S)
    (h : (univ.image f).card ≤ 2) :
    (∑ s ∈ univ.image f, weight dual (fiber f s)) ≤
      ((univ.image f).filter (fun s => 1 < (fiber f s).card)).card + 1 := by
  have ht : 13 = ∑ s ∈ univ.image f, (fiber f s).card := by
    simpa [fiber] using card_eq_sum_card_image f univ
  have hz (B : Finset Point) (hb : 6 ≤ B.card) : weight dual B = 0 := by
    simp [weight, hb]
  have hw (B : Finset Point) : weight dual B ≤ 3 := by
    unfold weight
    split_ifs <;> omega
  have hone (B : Finset Point) (hb : ¬ 1 < B.card) : weight dual B ≤ 1 := by
    unfold weight
    split_ifs <;> omega
  by_cases h2 : (univ.image f).card = 2
  · obtain ⟨a, b, hn, he⟩ := card_eq_two.mp h2
    rw [he] at ht ⊢
    simp only [sum_insert (mem_singleton.not.mpr hn), sum_singleton] at ht ⊢
    have hbig : 6 ≤ (fiber f a).card ∨ 6 ≤ (fiber f b).card := by omega
    have ha := hw (fiber f a)
    have hb := hw (fiber f b)
    have hsa := hone (fiber f a)
    have hsb := hone (fiber f b)
    rcases hbig with hga | hgb
    · rw [hz _ hga, zero_add]
      have haa : 1 < (fiber f a).card := by omega
      by_cases hbb : 1 < (fiber f b).card <;>
        simp [filter_insert, filter_singleton, haa, hbb, hn] <;> omega
    · rw [hz _ hgb, add_zero]
      have hbb : 1 < (fiber f b).card := by omega
      by_cases haa : 1 < (fiber f a).card <;>
        simp [filter_insert, filter_singleton, haa, hbb, hn] <;> omega
  · have hp : 0 < (univ.image f).card :=
      card_pos.mpr ⟨f 0, mem_image_of_mem _ (mem_univ _)⟩
    obtain ⟨a, he⟩ := card_eq_one.mp (show (univ.image f).card = 1 by omega)
    rw [he] at ht ⊢
    simp only [sum_singleton] at ht ⊢
    rw [hz _ (by omega)]
    exact Nat.zero_le _

end PGCapTwo
namespace PGCapTwo

private def symRows (dual pair : Bool) : List Nat :=
  match dual, pair with
  | false, false => [0xcba9876543210cba9876543210, 0xcba9876543210cba9876543210, 0x6a937b24851c96ac37b548120, 0xc7a89b63451208ab9c76451230, 0xc8a7b963052148ba7c96315240, 0xc9ab786503124cab7896134250, 0xc30978154b26ac39a84157b260, 0xcba3851709264cb6481a395270, 0x8a9b1354627c9bac146572380, 0xc94b5718a3260c5718a4b63290, 0xc90b85274361ac91b8537462a0, 0xcb0357684912ac13687945a2b0, 0xba586794123c1b6897a5423c0]
  | false, true => [0xcba9876543210cba9876543210, 0xcba9876543210cba9876543210, 0xcba9876543210cba9876543210, 0xcba9876543210cba9876543210, 0x45a9678bc231056a978bc23410, 0x4ba68391c72507b694ca283510, 0xabc8976142350bc89a72453610, 0x41a89265c37b04ab95268c3710, 0xcb496281a3750c7592b4a63810, 0xcba9876543210cba9876543210, 0xa5c6829b437106829b5c743a10, 0xa1c96385472b0a2c9648573b10, 0xc1468795a23b024798a56b3c10]
  | true, false => [0xcba9876543210cba9876543210, 0xcba9876543210cba9876543210, 0x8ab9c76451230c7a89b6345120, 0xa8c9b72541630a7c98b6241530, 0x6b798ac2435015ab6879c13240, 0xcb80a742635199b8ca74163250, 0xc5718a4b63290c94b5718a3260, 0xc6a924b571830c3a961824b570, 0x6281a7c543b90a6c517b943280, 0x4ba17862c359048a1b756c3290, 0xc2a9784563b01bc196784532a0, 0x42708a65c3b198164c7a5932b0, 0x4589a76bc32011458976ab32c0]
  | true, true => [0xcba9876543210cba9876543210, 0xcba9876543210cba9876543210, 0xcba9876543210cba9876543210, 0xbca08756234198b9ac74562310, 0xc7a96b85204133b796a852c410, 0xcba9876543210cba9876543210, 0x86a3c5b749210c5a7392b48610, 0x6829b5c743a10a5c6829b43710, 0x7ba35c68294104ba72935c6810, 0xbc23678549a10abc2367548910, 0x7b298c5640a137b268c9534a10, 0xcba9876543210cba9876543210, 0x58a9b67c4021325798a6b34c10]

private def symMap (d k : Bool) (t : Point) (line : Bool) (p : Point) : Point :=
  let row := (symRows d k).getD t.val 0
  Fin.ofNat 13 ((row >>> (4 * (p.val + if line then 13 else 0))) % 16)

private theorem symInv : ∀ d k t s p, symMap d k t s (symMap d k t s p) = p := by
  decide +kernel

private def symPerm (d k : Bool) (t : Point) (s : Bool) : Point ≃ Point :=
  ⟨symMap d k t s, symMap d k t s, symInv d k t s, symInv d k t s⟩

set_option maxHeartbeats 2000000 in
private theorem symPres : ∀ d k t p l,
    inc d (symPerm d k t false p) (symPerm d k t true l) ↔ inc d p l := by
  decide +kernel

private theorem symFirst : ∀ d t, t ≠ 0 →
    symPerm d false t false 0 = 0 ∧ symPerm d false t false 1 = t := by decide +kernel

private theorem symSecond : ∀ d t, (¬∃ l, inc d 0 l ∧ inc d 1 l ∧ inc d t l) →
    symPerm d true t false 0 = 0 ∧ symPerm d true t false 1 = 1 ∧
    symPerm d true t false 2 = t := by decide +kernel

private theorem symShift (d : Bool) (a p l : Point) :
    inc d (p+a) (l+a) ↔ inc d p l := by
  cases d <;> simp [inc, add_right_comm _ a]

theorem canonicalTriple (dual : Bool) (a b c : Point) (hab : a ≠ b)
    (hnc : ¬∃ l, inc dual a l ∧ inc dual b l ∧ inc dual c l) :
    ∃ π : Point ≃ Point, ∃ σ : Point ≃ Point,
      (∀ p l, inc dual (π p) (σ l) ↔ inc dual p l) ∧ π 0 = a ∧ π 1 = b ∧ π 2 = c := by
  let t := b - a
  have ht : t ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨h0, h1⟩ := symFirst dual t ht
  let e (s : Bool) := (symPerm dual false t s).trans (Equiv.addRight a)
  have hE (p l : Point) : inc dual (e false p) (e true l) ↔ inc dual p l :=
    (symShift dual a _ _).trans (symPres dual false t p l)
  have e0 : e false 0 = a := by change symPerm dual false t false 0 + a = a; rw [h0, zero_add]
  have e1 : e false 1 = b := by
    change symPerm dual false t false 1 + a = b
    rw [h1]; exact sub_add_cancel ..
  let u := (e false).symm c
  have eu : e false u = c := Equiv.apply_symm_apply ..
  have hu : ¬∃ l, inc dual 0 l ∧ inc dual 1 l ∧ inc dual u l := by
    rintro ⟨l,hp,hq,hr⟩
    exact hnc ⟨e true l, e0 ▸ (hE 0 l).mpr hp, e1 ▸ (hE 1 l).mpr hq,
      eu ▸ (hE u l).mpr hr⟩
  obtain ⟨u0,u1,u2⟩ := symSecond dual u hu
  refine ⟨(symPerm dual true u false).trans (e false),
    (symPerm dual true u true).trans (e true),
    fun p l => (hE _ _).trans (symPres dual true u p l), ?_, ?_, ?_⟩
  · exact (congrArg (e false) u0).trans e0
  · exact (congrArg (e false) u1).trans e1
  · exact (congrArg (e false) u2).trans eu

end PGCapTwo

namespace PGCapTwo
open Finset

theorem geoBound {S : Type*} [DecidableEq S] (dual : Bool) (f : Point → S)
    (nr : ∀ l : Point, ((univ.filter (fun p => inc dual p l)).image f).card ≤ 2) :
    (∑ s ∈ univ.image f, weight dual (fiber f s)) ≤
      ((univ.image f).filter (fun s => 1 < (fiber f s).card)).card + 1 := by
  by_cases h : (univ.image f).card ≤ 2
  · exact geoSmall dual f h
  · exact geoNormalize_bound dual f nr (by omega) (canonicalTriple dual)

end PGCapTwo

namespace PGCapTwo
open Finset

abbrev edge (a b : Fin 26) : Prop :=
  (a.val < 13 ∧ 13 ≤ b.val ∧
    (a.val + 26 - b.val) % 13 ∈ ([0,1,3,9] : List ℕ)) ∨
  (b.val < 13 ∧ 13 ≤ a.val ∧
    (b.val + 26 - a.val) % 13 ∈ ([0,1,3,9] : List ℕ))

theorem impossible {k : ℕ} (size : k ≤ 12) (occ : Fin 26 → Finset (Fin k × Bool))
    (cap : ∀ v, (occ v).card ≤ 2)
    (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → edge a b)
    (coverage : ∀ x y, edge x y → ∃ j, ((j,false) ∈ occ x ∧ (j,true) ∈ occ y) ∨
      ((j,true) ∈ occ x ∧ (j,false) ∈ occ y)) : False := by
  let vertex (d : Bool) (p : Point) : Fin 26 := if d then Fin.natAdd 13 p else Fin.castAdd 13 p
  have inj : ∀ d, Function.Injective (vertex d) := by decide
  have disj : ∀ d p l, vertex (!d) l ≠ vertex d p := by decide
  have independent : ∀ d p q, ¬ edge (vertex d p) (vertex d q) := by decide
  have codes : ∀ d p l, edge (vertex d p) (vertex (!d) l) ↔ inc d p l := by decide
  let A (d : Bool) (p : Point) := occ (vertex d p)
  let flip (s : Fin k × Bool) : Fin k × Bool := (s.1,!s.2)
  have bound (d : Bool) : ∃ T ⊆ univ.biUnion (A d),
      25 + (T ∩ univ.biUnion (A (!d))).card ≤ 2 * T.card := by
    apply oneColor d _ _ (fun p => cap _) (fun l => cap _) ?_ ?_ flip ?_ (geoBound d) (mixedBound d)
    · exact fun p q r hq hr h => independent d q r
        (sep _ _ _ (fun e => hq (inj d e)) (fun e => hr (inj d e)) h)
    · exact fun p q l hq h => (codes d q l).mp
        (sep _ _ _ (fun e => hq (inj d e)) (disj d p l) h)
    · intro p l h
      obtain ⟨j,hj⟩ := coverage _ _ ((codes d p l).mpr h)
      rcases hj with h | h
      · exact ⟨(j,true),h.2,h.1⟩
      · exact ⟨(j,false),h.2,h.1⟩
  obtain ⟨T,ht,bt⟩ := bound false
  obtain ⟨U,hu,bu⟩ := bound true

  have htu := card_le_card (inter_subset_inter_left (s := T) hu)
  have hut := card_le_card (inter_subset_inter_left (s := U) ht)
  rw [inter_comm U T] at hut
  have hi := card_union_add_card_inter T U
  have h24 := card_le_univ (T ∪ U)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h24
  change 25 + (T ∩ univ.biUnion (A true)).card ≤ 2 * T.card at bt
  change 25 + (U ∩ univ.biUnion (A false)).card ≤ 2 * U.card at bu
  omega

end PGCapTwo

namespace PGCapTwo
open Finset PEqualNP.AndCount
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem circuit
    (hGeom :
      let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let oriented := fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧
        (a.val + 26 - b.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let free := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ q ∈ P, ¬ I q l
      let U := fun (P : Finset (Fin 13)) => Finset.univ.filter fun k : Fin 26 =>
        (∃ p ∈ P, k = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ free P l
      ∀ v a b : Fin 26, a ≠ v → b ≠ v → ¬ (oriented a b ∨ oriented b a) →
        ∃ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l, free P l ∧ I p l) ∧
          ((¬∃ l, ∀ p ∈ P, I p l) ∧ ¬∃ p, ∀ l, free P l → I p l) ∧
          a ∈ U P ∧ b ∈ U P ∧ v ∉ U P) :
      let E (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let G (D : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin D.size) :=
        Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.size ≤ 12 → D.outVars = ∅ →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l : Fin 13, E p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
        (∀ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ E q l) ∧ E p l) →
          ((¬∃ l : Fin 13, ∀ p ∈ P, E p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ E q l) → E p l) →
          D.eval (Finset.univ.filter fun k : Fin 26 =>
            (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ E q l) = false) →
        (∀ v : Fin 26, (G D v).card ≤ 2) → False := by
    let V := Fin 26
    let rawVars {n : ℕ} (D : AndCountCircuit n) (s : Fin D.size × Bool) : Finset (Fin n) :=
      if s.2 then D.rightVars s.1 else D.leftVars s.1

    let rawOcc {n : ℕ} (D : AndCountCircuit n) (v : Fin n) : Finset (Fin D.size × Bool) :=
      univ.filter fun s => v ∈ rawVars D s

    have mem_rawOcc {n : ℕ} (D : AndCountCircuit n) (v : Fin n) (s : Fin D.size × Bool) :
        s ∈ rawOcc D v ↔ v ∈ rawVars D s := by simp [rawOcc]

    have rawEvalEq {n : ℕ} (D : AndCountCircuit n) (U : Finset (Fin n)) :
        D.eval U = decide ((∃ v ∈ D.outVars, v ∈ U) ∨ ∃ j ∈ D.outGates, D.gateVal U j = true) := rfl
    have rawSideEq {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
        (val : Fin k → Bool) :
        AndCountCircuit.sideTrue U B F i val =
          decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := rfl
    have rawNextEq {n : ℕ} (D : AndCountCircuit n) (U : Finset (Fin n)) (d : ℕ) (i : Fin D.size) :
        D.gateValFuel U (d + 1) i =
          (AndCountCircuit.sideTrue U (D.leftVars i) (D.leftGates i) i (D.gateValFuel U d) &&
           AndCountCircuit.sideTrue U (D.rightVars i) (D.rightGates i) i (D.gateValFuel U d)) := rfl

    have rawPair {n : ℕ} (D : AndCountCircuit n) (out : D.outVars = ∅)
        (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i))
        {x y : Fin n} (positive : D.eval {x, y} = true) :
        ∃ i, ((i, false) ∈ rawOcc D x ∧ (i, true) ∈ rawOcc D y) ∨
          ((i, true) ∈ rawOcc D x ∧ (i, false) ∈ rawOcc D y) := by
      simp [rawEvalEq, out] at positive
      obtain ⟨i, _, hi⟩ := positive
      suffices aux : ∀ (d : ℕ) (j : Fin D.size), D.gateValFuel {x,y} d j = true →
          ∃ k, (x ∈ D.leftVars k ∧ y ∈ D.rightVars k) ∨
            (x ∈ D.rightVars k ∧ y ∈ D.leftVars k) by
        simpa only [mem_rawOcc, rawVars, Bool.false_eq_true, ite_false, ite_true] using aux D.size i hi
      intro d
      induction d with
      | zero => intro _ h; exact (Bool.false_ne_true h).elim
      | succ d ih =>
        intro j h
        simp only [rawNextEq, Bool.and_eq_true, rawSideEq,
          decide_eq_true_eq, mem_insert, mem_singleton] at h
        rcases h.1 with ⟨a, ha, rfl | rfl⟩ | ⟨k, _, _, hk⟩
        · rcases h.2 with ⟨b, hb, rfl | rfl⟩ | ⟨k, _, _, hk⟩
          · exact (Finset.disjoint_left.mp (disj j) ha hb).elim
          · exact ⟨j, Or.inl ⟨ha, hb⟩⟩
          · exact ih k hk
        · rcases h.2 with ⟨b, hb, rfl | rfl⟩ | ⟨k, _, _, hk⟩
          · exact ⟨j, Or.inr ⟨hb, ha⟩⟩
          · exact (Finset.disjoint_left.mp (disj j) ha hb).elim
          · exact ih k hk
        · exact ih k hk

    have rawDominates {n : ℕ} (D : AndCountCircuit n) (out : D.outVars = ∅)
        {U Z : Finset (Fin n)}
        (cover : ∀ s : Fin D.size × Bool, (∃ v ∈ U, v ∈ rawVars D s) → ∃ v ∈ Z, v ∈ rawVars D s)
        (accepted : D.eval U = true) : D.eval Z = true := by
      simp [rawEvalEq, out] at accepted ⊢
      obtain ⟨g, hg, h⟩ := accepted
      refine ⟨g, hg, ?_⟩
      suffices mono : ∀ (d : ℕ) (j : Fin D.size), D.gateValFuel U d j = true → D.gateValFuel Z d j = true
        from mono D.size g h
      intro d
      induction d with
      | zero => exact fun _ h => h
      | succ d ih =>
        intro j
        have side (b : Bool) (F : Finset (Fin D.size)) :
            AndCountCircuit.sideTrue U (rawVars D (j,b)) F j (D.gateValFuel U d) = true →
            AndCountCircuit.sideTrue Z (rawVars D (j,b)) F j (D.gateValFuel Z d) = true := by
          simp only [rawSideEq, decide_eq_true_eq]
          rintro (⟨v, hv, hu⟩ | ⟨k, hk, hkj, ht⟩)
          · obtain ⟨w, hw, hz⟩ := cover (j,b) ⟨v, hu, hv⟩
            exact Or.inl ⟨w, hz, hw⟩
          · exact Or.inr ⟨k, hk, hkj, ih k ht⟩
        simp only [rawNextEq, Bool.and_eq_true]
        exact fun h => ⟨side false _ h.1, side true _ h.2⟩

    have rawExcluded {n : ℕ} (D : AndCountCircuit n) (out : D.outVars = ∅)
        {v w : Fin n} {Z : Finset (Fin n)} (accept : D.eval {v,w} = true)
        (hw : w ∈ Z) (reject : D.eval Z = false) :
        ∃ s ∈ rawOcc D v, ∀ a ∈ Z, s ∉ rawOcc D a := by
      by_contra! h
      have covered (s : Fin D.size × Bool) (hs : ∃ z ∈ ({v,w} : Finset _), z ∈ rawVars D s) :
          ∃ z ∈ Z, z ∈ rawVars D s := by
        obtain ⟨z, hz, hzs⟩ := hs
        rcases mem_insert.mp hz with rfl | hz
        · obtain ⟨a, ha, has⟩ := h s ((mem_rawOcc D _ _).mpr hzs)
          exact ⟨a, ha, (mem_rawOcc D _ _).mp has⟩
        · obtain rfl := mem_singleton.mp hz
          exact ⟨z, hw, hzs⟩
      have contra := rawDominates D out covered accept
      simp [reject] at contra

    have rawOcc_card_le {n : ℕ} (D : AndCountCircuit n)
        (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) (v : Fin n) :
        (rawOcc D v).card ≤ (univ.filter fun i => v ∈ D.leftVars i ∨ v ∈ D.rightVars i).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · rintro ⟨i,b⟩ hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        cases b
        · exact Or.inl ((mem_rawOcc D _ _).mp hi)
        · exact Or.inr ((mem_rawOcc D _ _).mp hi)
      · rintro ⟨i,a⟩ ha ⟨j,b⟩ hb (rfl : i = j)
        have hA := (mem_rawOcc D _ _).mp ha
        have hB := (mem_rawOcc D _ _).mp hb
        cases a <;> cases b
        · rfl
        · exact (Finset.disjoint_left.mp (disj i) hA hB).elim
        · exact (Finset.disjoint_left.mp (disj i) hB hA).elim
        · rfl

    let incidence (a b : V) : Prop :=
      (a.val < 13 ∧ 13 ≤ b.val ∧
        (a.val + 26 - b.val) % 13 ∈ ([0,1,3,9] : List ℕ)) ∨
      (b.val < 13 ∧ 13 ≤ a.val ∧
        (b.val + 26 - a.val) % 13 ∈ ([0,1,3,9] : List ℕ))

    have incidence_symm {x y : V} (h : incidence x y) : incidence y x := h.symm

    let planeInc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

    let row (P : Finset (Fin 13)) : Finset V := Finset.univ.filter fun k : V =>
      (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ planeInc q l

    let Closed (P : Finset (Fin 13)) : Prop :=
      ∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ planeInc q l) ∧ planeInc p l

    let Generic (P : Finset (Fin 13)) : Prop :=
      (¬ ∃ l : Fin 13, ∀ p ∈ P, planeInc p l) ∧
        ¬ ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ planeInc q l) → planeInc p l

    have codes : ∀ (p l : Fin 13),
        incidence (Fin.castAdd 13 p) (Fin.natAdd 13 l) ↔ planeInc p l := by decide

    have no_points : ∀ (p q : Fin 13), ¬ incidence (Fin.castAdd 13 p) (Fin.castAdd 13 q) :=
      by decide

    have no_lines : ∀ (l k : Fin 13), ¬ incidence (Fin.natAdd 13 l) (Fin.natAdd 13 k) :=
      by decide

    have vertex_positive (D : AndCountCircuit 26)
        (pos : ∀ p l : Fin 13, planeInc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) :
        ∀ a b : V, incidence a b → D.eval {a,b} = true := by
      intro a b
      induction a using (Fin.addCases (m := 13) (n := 13)) <;> induction b using (Fin.addCases (m := 13) (n := 13))
      case left.left p q => exact fun h => (no_points p q h).elim
      case left.right p l => exact fun h => pos p l ((codes p l).mp h)
      case right.left l p =>
        intro h
        simpa only [Finset.pair_comm] using pos p l ((codes p l).mp (incidence_symm h))
      case right.right l k => exact fun h => (no_lines l k h).elim

    have missingNeighbor (P : Finset (Fin 13)) (hc : Closed P) :
        ∀ v : V, v ∉ row P → ∃ w ∈ row P, incidence v w := by
      intro v
      induction v using (Fin.addCases (m := 13) (n := 13))
      case left p =>
        intro hv
        have hp : p ∉ P := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, h, rfl⟩⟩)
        obtain ⟨l, free, incident⟩ := hc p hp
        exact ⟨Fin.natAdd 13 l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨l, rfl, free⟩⟩,
          (codes p l).mpr incident⟩
      case right l =>
        intro hv
        by_contra! h
        apply hv
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨l, rfl, ?_⟩⟩
        intro p hp incident
        exact h (Fin.castAdd 13 p) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, hp, rfl⟩⟩)
          (incidence_symm ((codes p l).mpr incident))

    have rawSeparation (D : AndCountCircuit 26) (out : D.outVars = ∅)
        (pos : ∀ p l : Fin 13, planeInc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true)
        (neg : ∀ P, Closed P → Generic P → D.eval (row P) = false)
        (extension : ∀ v a b : V, a ≠ v → b ≠ v → ¬ incidence a b →
          ∃ P, Closed P ∧ Generic P ∧ a ∈ row P ∧ b ∈ row P ∧ v ∉ row P) :
        ∀ v a b : V, a ≠ v → b ≠ v → rawOcc D v ⊆ rawOcc D a ∪ rawOcc D b → incidence a b := by
      intro v a b hav hbv hsub
      by_contra nonedge
      obtain ⟨P, hc, hg, ha, hb, hv⟩ := extension v a b hav hbv nonedge
      obtain ⟨w, hw, edge⟩ := missingNeighbor P hc v hv
      obtain ⟨s, hs, hn⟩ := rawExcluded D out (vertex_positive D pos v w edge) hw (neg P hc hg)
      exact (Finset.mem_union.mp (hsub hs)).elim (hn a ha) (hn b hb)

    have rawCoverage (D : AndCountCircuit 26) (out : D.outVars = ∅)
        (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i))
        (pos : ∀ p l : Fin 13, planeInc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true)
        (x y : V) (edge : incidence x y) :
        ∃ j : Fin D.size, ((j,false) ∈ rawOcc D x ∧ (j,true) ∈ rawOcc D y) ∨
          ((j,true) ∈ rawOcc D x ∧ (j,false) ∈ rawOcc D y) :=
      rawPair D out disj (vertex_positive D pos x y edge)
    dsimp only
    intro D size out disj pos neg cap
    exact impossible size (rawOcc D) (fun v => (rawOcc_card_le D disj v).trans (cap v))
      (rawSeparation D out pos neg hGeom) (rawCoverage D out disj pos)
end PGCapTwo

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461
open Finset PEqualNP.AndCount

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
private theorem pg3Reduction
    (hGeom :
      let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let oriented := fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧
        (a.val + 26 - b.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let free := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ q ∈ P, ¬ I q l
      let U := fun (P : Finset (Fin 13)) => Finset.univ.filter fun k : Fin 26 =>
        (∃ p ∈ P, k = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ free P l
      ∀ v a b : Fin 26, a ≠ v → b ≠ v → ¬ (oriented a b ∨ oriented b a) →
        ∃ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l, free P l ∧ I p l) ∧
          ((¬∃ l, ∀ p ∈ P, I p l) ∧ ¬∃ p, ∀ l, free P l → I p l) ∧
          a ∈ U P ∧ b ∈ U P ∧ v ∉ U P)
    (hLadder :
      let I (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let pt := (Fin.castAdd 13 : Fin 13 → Fin 26)
      let ln := (Fin.natAdd 13 : Fin 13 → Fin 26)
      let free (P : Finset (Fin 13)) (l : Fin 13) := ∀ p ∈ P, ¬ I p l
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26, D.WellFormed →
        (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l, I p l → D.eval {pt p, ln l} = true) →
        (∀ P, (∀ p ∉ P, ∃ l, free P l ∧ I p l) →
          ((¬ ∃ l, ∀ p ∈ P, I p l) ∧ ¬ ∃ p, ∀ l, free P l → I p l) →
          D.eval (Finset.univ.filter fun k => (∃ p ∈ P, k = pt p) ∨ ∃ l, k = ln l ∧ free P l) = false) →
        let G (v : Fin 26) := Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
        D.outVars = ∅ ∧ 11 ≤ D.size ∧ (∀ v, (G v).card + 9 ≤ D.size) ∧
          (∀ p l, ¬ I p l → (G (pt p) ∪ G (ln l)).card + 7 ≤ D.size) ∧
          (∀ p q, p ≠ q → (G (pt p) ∪ G (pt q)).card + 6 ≤ D.size ∧
            (G (ln p) ∪ G (ln q)).card + 6 ≤ D.size))
    (hSize12 :
      let E (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let G (D : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin D.size) :=
        Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.WellFormed → D.size = 12 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l : Fin 13, E p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
        (∀ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ E q l) ∧ E p l) →
          ((¬∃ l : Fin 13, ∀ p ∈ P, E p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ E q l) → E p l) →
          D.eval (Finset.univ.filter fun k : Fin 26 =>
            (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ E q l) = false) →
        (∀ v : Fin 26, (G D v).card ≤ 3) →
        (∀ p l : Fin 13, ¬ E p l → (G D (Fin.castAdd 13 p) ∪ G D (Fin.natAdd 13 l)).card ≤ 5) →
        (∀ p1 p2 : Fin 13, p1 ≠ p2 → (G D (Fin.castAdd 13 p1) ∪ G D (Fin.castAdd 13 p2)).card ≤ 6) →
        (∀ l1 l2 : Fin 13, l1 ≠ l2 → (G D (Fin.natAdd 13 l1) ∪ G D (Fin.natAdd 13 l2)).card ≤ 6) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  have hSize11 :
      let E (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let G (D : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin D.size) :=
        Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.WellFormed → D.size = 11 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l : Fin 13, E p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
        (∀ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ E q l) ∧ E p l) →
          ((¬∃ l : Fin 13, ∀ p ∈ P, E p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ E q l) → E p l) →
          D.eval (Finset.univ.filter fun k : Fin 26 =>
            (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ E q l) = false) →
        (∀ v : Fin 26, (G D v).card ≤ 2) →
        (∀ p l : Fin 13, ¬ E p l → (G D (Fin.castAdd 13 p) ∪ G D (Fin.natAdd 13 l)).card ≤ 4) →
        (∀ p1 p2 : Fin 13, p1 ≠ p2 → (G D (Fin.castAdd 13 p1) ∪ G D (Fin.castAdd 13 p2)).card ≤ 5) →
        (∀ l1 l2 : Fin 13, l1 ≠ l2 → (G D (Fin.natAdd 13 l1) ∪ G D (Fin.natAdd 13 l2)).card ≤ 5) →
        False := by
    dsimp only
    intro D _ hs out _ disj pos neg cap _ _ _
    exact PGCapTwo.circuit hGeom D (by omega) out disj pos neg cap
  classical
  intro C hm hPos hNeg
  have op_and_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have op_or_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
  have sideTrue_def : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool),
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := fun _ _ _ _ _ => rfl
  have eval_def : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := fun _ _ => rfl

  have sideTrue_congr : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k)
      (val val' : Fin k → Bool), (∀ j : Fin k, j < i → val j = val' j) →
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val' := by
    intro k U B F i val val' h
    rw [sideTrue_def, sideTrue_def, decide_eq_decide]
    constructor
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩
  have fuel_indep : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (d d' : ℕ) (i : Fin E.size), i.val < d → i.val < d' →
      E.gateValFuel U d i = E.gateValFuel U d' i := by
    intro E U d
    induction d with
    | zero =>
      intro d' i h
      exact absurd h (Nat.not_lt_zero _)
    | succ e ih =>
      intro d' i h h'
      cases d' with
      | zero => exact absurd h' (Nat.not_lt_zero _)
      | succ e' =>
        have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateValFuel U e' j := by
          intro j hj
          have hji : j.val < i.val := hj
          exact ih e' j (by omega) (by omega)
        show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) =
             (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e') &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e'))
        rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
            sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateVal_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)) (i : Fin E.size),
      E.gateVal U i =
        (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateVal U) &&
         PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateVal U)) := by
    intro E U i
    have hi : i.val < E.size := i.2
    obtain ⟨e, he⟩ : ∃ e, E.size = e + 1 := ⟨E.size - 1, by omega⟩
    have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateVal U j := by
      intro j hj
      have hji : j.val < i.val := hj
      exact fuel_indep E U e E.size j (by omega) j.2
    have h1 : E.gateVal U i = E.gateValFuel U (e + 1) i :=
      fuel_indep E U E.size (e + 1) i i.2 (by omega)
    rw [h1]
    show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
          PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) = _
    rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
        sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateValFuel_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → ∀ (d : ℕ) (i : Fin E.size), E.gateValFuel U d i = true → E.gateValFuel V d i = true := by
    intro E U V hUV d
    induction d with
    | zero => intro i h; cases h
    | succ d ih =>
      intro i h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) = true at h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.leftVars i) (E.leftGates i) i (E.gateValFuel V d) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.rightVars i) (E.rightGates i) i (E.gateValFuel V d)) = true
      rw [Bool.and_eq_true] at h ⊢
      constructor
      · have hL := h.1
        rw [sideTrue_def] at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with h1 | h2
        · rcases h1 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, hv, hUV hu⟩
        · rcases h2 with ⟨j, hj, hlt, hv⟩
          exact Or.inr ⟨j, hj, hlt, ih j hv⟩
      · have hR := h.2
        rw [sideTrue_def] at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with h1 | h2
        · rcases h1 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, hv, hUV hu⟩
        · rcases h2 with ⟨j, hj, hlt, hv⟩
          exact Or.inr ⟨j, hj, hlt, ih j hv⟩
  have gateVal_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → ∀ i : Fin E.size, E.gateVal U i = true → E.gateVal V i = true := by
    intro E U V hUV i h
    exact gateValFuel_mono E hUV E.size i h
  have eval_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → E.eval U = true → E.eval V = true := by
    intro E U V hUV h
    rw [eval_def] at h ⊢
    rw [decide_eq_true_eq] at h ⊢
    rcases h with h1 | h2
    · rcases h1 with ⟨v, hv, hu⟩
      exact Or.inl ⟨v, hv, hUV hu⟩
    · rcases h2 with ⟨j, hj, hv⟩
      exact Or.inr ⟨j, hj, gateVal_mono E hUV j hv⟩

  let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
  have wiresFrom_append : ∀ (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
    intro gs1 gs2 w; simp [wiresFrom, List.foldl_append]
  have wiresFrom_ext : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
      refine ⟨v :: t, ?_, by simp [hl]⟩
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
      rw [hstep, ht]
      simp
  have length_wiresFrom : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
    rw [ht, List.length_append, hl]
  have getD_wiresFrom_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
    intro gs w i h
    obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
    rw [ht, List.getD_append _ _ _ _ h]
  have getD_wiresFrom_take : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k i : ℕ),
      k ≤ gs.length →
      (wiresFrom (gs.take k) w).getD i false =
        if i < w.length + k then (wiresFrom gs w).getD i false else false := by
    intro gs w k i hk
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left hk]
    split_ifs with hi
    · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
      conv_rhs => rw [hsplit, wiresFrom_append]
      exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
    · rw [List.getD_eq_default]
      omega
  have getD_wiresFrom_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ)
      (hk : k < gs.length),
      (wiresFrom gs w).getD (w.length + k) false =
        (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
          if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
    intro gs w k hk
    have hsplit : gs = gs.take k ++ gs[k]'hk :: gs.drop (k + 1) := by
      have h1 := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
    have heq : wiresFrom gs w =
        wiresFrom (gs.drop (k + 1))
          (wiresFrom (gs.take k) w ++
            [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
      conv_lhs => rw [hsplit, wiresFrom_append]
      rfl
    have hsnoc : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := fun l b => by simp
    rw [heq, getD_wiresFrom_lt]
    · conv_lhs => rw [← hlen, hsnoc]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
    · rw [List.length_append, hlen]; simp
  let T_and : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j : Fin C.gates.length => (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  let A_and : Finset ℕ := T_and.image Fin.val
  have hA_card : A_and.card = {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
    have h1 : A_and.card = T_and.card := Finset.card_image_of_injective T_and Fin.val_injective
    have h2 : (T_and : Set (Fin C.gates.length)) =
        {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
      ext j; simp [T_and]
    rw [h1, ← h2, Set.ncard_coe_finset]
  let k0 : ℕ := A_and.card
  let ord : Fin k0 ↪o ℕ := A_and.orderEmbOfFin rfl
  have memOrd : ∀ i : Fin k0, ord i ∈ A_and := fun i => A_and.orderEmbOfFin_mem rfl i
  have allAnd : ∀ (j : ℕ) (hj : j < C.gates.length), C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∃ i : Fin k0, ord i = j := by
    intro j hj ha
    have hT : (⟨j, hj⟩ : Fin C.gates.length) ∈ T_and := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    have hA : j ∈ A_and := Finset.mem_image.mpr ⟨⟨j, hj⟩, hT, rfl⟩
    change j ∈ Set.range (A_and.orderEmbOfFin rfl)
    rwa [Finset.range_orderEmbOfFin]
  have okOrd : ∀ i : Fin k0, ∃ h : ord i < C.gates.length, C.gates[ord i].op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    intro i
    obtain ⟨j, hjT, hjv⟩ := Finset.mem_image.mp (memOrd i)
    have hop := (Finset.mem_filter.mp hjT).2
    refine ⟨hjv ▸ j.isLt, ?_⟩
    simpa [← hjv] using hop
  let collVal (U : Finset (Fin 26)) (v : Fin k0 → Bool) (s : Finset (Fin 26) × Finset (Fin k0)) : Bool :=
    decide ((∃ x ∈ s.1, x ∈ U) ∨ ∃ i ∈ s.2, v i = true)
  let collCollect (L : List ℕ) (s : ℕ → Finset (Fin 26) × Finset (Fin k0)) : Finset (Fin 26) × Finset (Fin k0) :=
    (L.toFinset.biUnion (fun j => (s j).1), L.toFinset.biUnion (fun j => (s j).2))
  have collCollect_true : ∀ (U : Finset (Fin 26)) (v : Fin k0 → Bool) (L : List ℕ)
      (s : ℕ → Finset (Fin 26) × Finset (Fin k0)),
      collVal U v (collCollect L s) = true ↔ ∃ j ∈ L, collVal U v (s j) = true := by
    intro U v L s
    simp only [collVal, collCollect, decide_eq_true_eq, Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨x, ⟨j, hjL, hxs⟩, hxU⟩
        exact ⟨j, hjL, Or.inl ⟨x, hxs, hxU⟩⟩
      · rcases h2 with ⟨i, ⟨j, hjL, his⟩, hvi⟩
        exact ⟨j, hjL, Or.inr ⟨i, his, hvi⟩⟩
    · intro h
      rcases h with ⟨j, hjL, hjv⟩
      rcases hjv with h1 | h2
      · rcases h1 with ⟨x, hxs, hxU⟩
        exact Or.inl ⟨x, ⟨j, hjL, hxs⟩, hxU⟩
      · rcases h2 with ⟨i, his, hvi⟩
        exact Or.inr ⟨i, ⟨j, hjL, his⟩, hvi⟩
  let collOrig (U : Finset (Fin 26)) (w : ℕ) : Bool :=
    (wiresFrom C.gates (List.ofFn (fun i : Fin 26 => decide (i ∈ U)))).getD w false
  have coll_gate : ∀ (U : Finset (Fin 26)) (j : ℕ) (h : j < C.gates.length),
      collOrig U (26 + j) = (C.gates[j]'h).op.eval ((C.gates[j]'h).inputs.map
        (fun i => if i < 26 + j then collOrig U i else false)) := by
    intro U j h
    simpa only [collOrig, List.length_ofFn] using
      getD_wiresFrom_gate C.gates (List.ofFn (fun i : Fin 26 => decide (i ∈ U))) j h
  let collV (U : Finset (Fin 26)) (j : Fin k0) : Bool := collOrig U (26 + ord j)
  have coll_prior : ∀ (w : ℕ),
      (∀ i < w, ∃ s : Finset (Fin 26) × Finset (Fin k0), (∀ j ∈ s.2, 26 + ord j ≤ i) ∧
        ∀ U : Finset (Fin 26), collVal U (collV U) s = collOrig U i) →
      ∃ f : ℕ → Finset (Fin 26) × Finset (Fin k0), (∀ i j, j ∈ (f i).2 → 26 + ord j < w) ∧
        ∀ i (U : Finset (Fin 26)), collVal U (collV U) (f i) = if i < w then collOrig U i else false := by
    intro w ih
    let f (i : ℕ) : Finset (Fin 26) × Finset (Fin k0) := if hi : i < w then (ih i hi).choose else (∅, ∅)
    refine ⟨f, ?_, ?_⟩
    · intro i j hj
      by_cases hi : i < w
      · simp only [f, dite_eq_left hi] at hj
        exact Nat.lt_of_le_of_lt ((ih i hi).choose_spec.1 _ hj) hi
      · simp [f, hi] at hj
    · intro i U
      by_cases hi : i < w
      · simpa only [f, dite_eq_left hi, ite_eq_left hi] using (ih i hi).choose_spec.2 U
      · simp [f, hi, collVal]
  have coll_wires : ∀ w : ℕ, ∃ s : Finset (Fin 26) × Finset (Fin k0),
      (∀ j ∈ s.2, 26 + ord j ≤ w) ∧ ∀ U : Finset (Fin 26), collVal U (collV U) s = collOrig U w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hinput : w < 26
      · let p : Fin 26 := ⟨w, hinput⟩
        refine ⟨({p}, ∅), by simp, ?_⟩
        intro U
        unfold collOrig
        rw [getD_wiresFrom_lt _ _ _ (by simpa using hinput)]
        rw [List.getD_eq_getElem _ _ (by simpa using hinput), List.getElem_ofFn]
        simp [collVal, p]
      let j := w - 26
      have hw : 26 + j = w := by dsimp [j]; omega
      by_cases hj : j < C.gates.length
      · obtain h | h := (hm C.gates[j] (List.getElem_mem hj)).1
        · obtain ⟨z, hz⟩ := allAnd j hj h
          exact ⟨(∅, {z}), by simp [hz, hw], fun U => by simp [collVal, collV, hz, hw]⟩
        · obtain ⟨f, hf, he⟩ := coll_prior w ih
          refine ⟨collCollect C.gates[j].inputs f, ?_, ?_⟩
          · intro z hz
            obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
            exact Nat.le_of_lt (hf i z hi)
          · intro U
            rw [← hw, coll_gate U j hj, show C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or from h]
            apply Bool.eq_iff_iff.mpr
            rw [collCollect_true]
            rw [op_or_eval]
            simp only [List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
            simp_rw [he, hw]
      · refine ⟨(∅, ∅), by simp, ?_⟩
        intro U
        unfold collOrig
        rw [List.getD_eq_default _ _ (by simp only [length_wiresFrom, List.length_ofFn]; omega)]
        simp [collVal]
  have coll_sides : ∀ i : Fin k0, ∃ l r : Finset (Fin 26) × Finset (Fin k0),
      (∀ z ∈ l.2, z < i) ∧ (∀ z ∈ r.2, z < i) ∧
      ∀ U : Finset (Fin 26), U.Nonempty →
        (collVal U (collV U) l && collVal U (collV U) r) = collV U i := by
    intro i
    obtain ⟨h, hop⟩ := okOrd i
    let g := C.gates[ord i]
    have hlen := (hm g (List.getElem_mem h)).2
    obtain ⟨f, hf, he⟩ := coll_prior (26 + ord i) (fun w _ => coll_wires w)
    have ltj : ∀ (a : ℕ) (z : Fin k0), z ∈ (f a).2 → z < i := fun a z hz =>
      ord.lt_iff_lt.mp (Nat.lt_of_add_lt_add_left (hf _ _ hz))
    have gate : ∀ U : Finset (Fin 26),
        collV U i = (g.inputs.map fun j => collVal U (collV U) (f j)).all id := by
      intro U
      dsimp only [collV]
      rw [coll_gate U (ord i) h, hop]
      rw [op_and_eval]; dsimp only [g]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (he a U).symm
    cases hL : g.inputs with
    | nil =>
      refine ⟨(Finset.univ, ∅), (Finset.univ, ∅), by simp, by simp, ?_⟩
      intro U hu
      rw [gate, hL]
      simpa [collVal] using (show ∃ x, x ∈ U from hu)
    | cons a L =>
      cases L with
      | nil =>
        refine ⟨f a, f a, ltj a, ltj a, ?_⟩
        intro U _
        simp [gate, hL]
      | cons b L =>
        have hem : L = [] := by rw [hL] at hlen; simpa using hlen
        subst L
        refine ⟨f a, f b, ltj a, ltj b, ?_⟩
        intro U _
        simp [gate, hL]
  choose lSide rSide hlSide hrSide hvSide using coll_sides
  obtain ⟨oSide, _, hoSide⟩ := coll_wires C.output
  let D0 : PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨k0, fun i => (lSide i).1, fun i => (lSide i).2,
         fun i => (rSide i).1, fun i => (rSide i).2, oSide.1, oSide.2⟩
  have hD0_size : D0.size = {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
    hA_card
  have hD0_wf : D0.WellFormed := fun i => ⟨hlSide i, hrSide i⟩
  have hD0_eval : ∀ U : Finset (Fin 26), U.Nonempty →
      D0.eval U = PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => Decidable.decide (k ∈ U)) := by
    intro U hU
    have fuel : ∀ (d : ℕ) (i : Fin k0), i.val < d → D0.gateValFuel U d i = collV U i := by
      intro d
      induction d with
      | zero => intro i h; omega
      | succ d ih =>
        intro i hd
        have eqSide : ∀ (s : Finset (Fin 26) × Finset (Fin k0)), (∀ z ∈ s.2, z < i) →
            PEqualNP.AndCount.AndCountCircuit.sideTrue U s.1 s.2 i (D0.gateValFuel U d) = collVal U (collV U) s := by
          intro s hs
          rw [sideTrue_def]; dsimp only [collVal]
          congr 1
          apply propext
          apply or_congr_right
          constructor
          · intro h1
            rcases h1 with ⟨j, hj, hji, hval⟩
            exact ⟨j, hj, (ih j (by have := hji; change j.val < i.val at this; omega)).symm.trans hval⟩
          · intro h1
            rcases h1 with ⟨j, hj, hval⟩
            have hji := hs j hj
            exact ⟨j, hj, hji, (ih j (by change j.val < i.val at hji; omega)).trans hval⟩
        change (PEqualNP.AndCount.AndCountCircuit.sideTrue U (lSide i).1 (lSide i).2 i (D0.gateValFuel U d) &&
                PEqualNP.AndCount.AndCountCircuit.sideTrue U (rSide i).1 (rSide i).2 i (D0.gateValFuel U d)) = _
        rw [eqSide _ (hlSide i), eqSide _ (hrSide i), hvSide i U hU]
    have hgate : ∀ i : Fin k0, D0.gateVal U i = collV U i := fun i => fuel k0 i i.isLt
    have hev : D0.eval U = collOrig U C.output := by
      have h1 : D0.eval U = collVal U (collV U) oSide := by
        rw [eval_def]; simp only [hgate, collVal, D0]
      rw [h1, hoSide U]
    rw [hev]
    show (wiresFrom C.gates (List.ofFn fun i : Fin 26 => decide (i ∈ U))).getD C.output false =
         (C.wires (List.ofFn fun k : Fin 26 => Decidable.decide (k ∈ U))).getD C.output false
    rfl

  let stripCircuit (E : PEqualNP.AndCount.AndCountCircuit 26) : PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨E.size,
     fun i => Finset.univ.filter (fun v =>
       (v ∈ E.leftVars i ∨ ∃ j ∈ E.leftGates i, j < i ∧ E.gateVal {v} j = true) ∧ E.gateVal {v} i = false),
     E.leftGates,
     fun i => Finset.univ.filter (fun v =>
       (v ∈ E.rightVars i ∨ ∃ j ∈ E.rightGates i, j < i ∧ E.gateVal {v} j = true) ∧ E.gateVal {v} i = false),
     E.rightGates,
     Finset.univ.filter (fun v => v ∈ E.outVars ∨ ∃ j ∈ E.outGates, E.gateVal {v} j = true),
     E.outGates⟩
  have strip_wf : ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed → (stripCircuit E).WellFormed :=
    fun _ hw => hw
  have strip_disj : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (i : Fin (stripCircuit E).size),
      Disjoint ((stripCircuit E).leftVars i) ((stripCircuit E).rightVars i) := by
    intro E i
    rw [Finset.disjoint_left]
    intro v hL hR
    have hL' := (Finset.mem_filter.mp hL).2
    have hR' := (Finset.mem_filter.mp hR).2
    have hvL : PEqualNP.AndCount.AndCountCircuit.sideTrue {v} (E.leftVars i) (E.leftGates i) i (E.gateVal {v}) = true := by
      rw [sideTrue_def]
      rw [decide_eq_true_eq]
      rcases hL'.1 with h1 | h2
      · exact Or.inl ⟨v, h1, Finset.mem_singleton_self v⟩
      · exact Or.inr h2
    have hvR : PEqualNP.AndCount.AndCountCircuit.sideTrue {v} (E.rightVars i) (E.rightGates i) i (E.gateVal {v}) = true := by
      rw [sideTrue_def]
      rw [decide_eq_true_eq]
      rcases hR'.1 with h1 | h2
      · exact Or.inl ⟨v, h1, Finset.mem_singleton_self v⟩
      · exact Or.inr h2
    have htrue : E.gateVal {v} i = true := by
      rw [gateVal_eq E {v} i, hvL, hvR]; rfl
    rw [hL'.2] at htrue
    cases htrue
  have strip_gateVal_le : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (k : ℕ) (i : Fin E.size), i.val < k → (stripCircuit E).gateVal U i = true → E.gateVal U i = true := by
    intro E U k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hval
      rw [gateVal_eq (stripCircuit E) U i, Bool.and_eq_true] at hval
      rw [gateVal_eq E U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        rw [sideTrue_def] at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with h1 | h2
        · rcases h1 with ⟨v, hv, hvU⟩
          have hv' := (Finset.mem_filter.mp hv).2.1
          rcases hv' with hvB | hjs
          · exact Or.inl ⟨v, hvB, hvU⟩
          · rcases hjs with ⟨j, hjF, hji, hvs⟩
            exact Or.inr ⟨j, hjF, hji, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
        · rcases h2 with ⟨j, hjF, hji, hjv⟩
          exact Or.inr ⟨j, hjF, hji, ih j (by have := hji; change j.val < i.val at this; omega) hjv⟩
      · have hR := hval.2
        rw [sideTrue_def] at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with h1 | h2
        · rcases h1 with ⟨v, hv, hvU⟩
          have hv' := (Finset.mem_filter.mp hv).2.1
          rcases hv' with hvB | hjs
          · exact Or.inl ⟨v, hvB, hvU⟩
          · rcases hjs with ⟨j, hjF, hji, hvs⟩
            exact Or.inr ⟨j, hjF, hji, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
        · rcases h2 with ⟨j, hjF, hji, hjv⟩
          exact Or.inr ⟨j, hjF, hji, ih j (by have := hji; change j.val < i.val at this; omega) hjv⟩
  have strip_gateVal_ge : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (k : ℕ) (i : Fin E.size), i.val < k → E.gateVal U i = true →
      (∃ v ∈ U, E.gateVal {v} i = true) ∨ (stripCircuit E).gateVal U i = true := by
    intro E U k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hval
      by_cases hsing : ∃ v ∈ U, E.gateVal {v} i = true
      · exact Or.inl hsing
      · right
        have hno : ∀ v ∈ U, E.gateVal {v} i = false := fun v hvU =>
          Bool.eq_false_iff.mpr (fun hv => hsing ⟨v, hvU, hv⟩)
        rw [gateVal_eq E U i, Bool.and_eq_true] at hval
        rw [gateVal_eq (stripCircuit E) U i, Bool.and_eq_true]
        constructor
        · have hL := hval.1
          rw [sideTrue_def] at hL ⊢
          rw [decide_eq_true_eq] at hL ⊢
          rcases hL with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvB, hno v hvU⟩, hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hjv⟩
            rcases ih j (by have := hji; change j.val < i.val at this; omega) hjv with h3 | hj'
            · rcases h3 with ⟨v, hvU, hvs⟩
              exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hj'⟩
        · have hR := hval.2
          rw [sideTrue_def] at hR ⊢
          rw [decide_eq_true_eq] at hR ⊢
          rcases hR with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvB, hno v hvU⟩, hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hjv⟩
            rcases ih j (by have := hji; change j.val < i.val at this; omega) hjv with h3 | hj'
            · rcases h3 with ⟨v, hvU, hvs⟩
              exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hj'⟩
  have strip_eval_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      (stripCircuit E).eval U = E.eval U := by
    intro E U
    rw [eval_def, eval_def]
    refine decide_eq_decide.mpr ?_
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        rcases (Finset.mem_filter.mp hvO).2 with hvC | hjs
        · exact Or.inl ⟨v, hvC, hvU⟩
        · rcases hjs with ⟨j, hjO, hvs⟩
          exact Or.inr ⟨j, hjO, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        exact Or.inr ⟨j, hjO, strip_gateVal_le E U E.size j j.isLt hjv⟩
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvO⟩, hvU⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        rcases strip_gateVal_ge E U E.size j j.isLt hjv with h3 | hj'
        · rcases h3 with ⟨v, hvU, hvs⟩
          exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjO, hvs⟩⟩, hvU⟩
        · exact Or.inr ⟨j, hjO, hj'⟩
  have strip_gateVal_singleton : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (i : Fin (stripCircuit E).size) (v : Fin 26), (stripCircuit E).gateVal {v} i = false := by
    intro E i v
    induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin E.size → Fin E.size → Prop)).induction with
    | h i ih =>
      rw [Bool.eq_false_iff]
      intro htrue
      rw [gateVal_eq (stripCircuit E) {v} i, Bool.and_eq_true] at htrue
      have getL : v ∈ (stripCircuit E).leftVars i := by
        have hL := htrue.1
        rw [sideTrue_def] at hL
        rw [decide_eq_true_eq] at hL
        rcases hL with h1 | h2
        · rcases h1 with ⟨u, hu, huv⟩
          rw [Finset.mem_singleton.mp huv] at hu
          exact hu
        · rcases h2 with ⟨j, _, hji, hjv⟩
          rw [ih j hji] at hjv; cases hjv
      have getR : v ∈ (stripCircuit E).rightVars i := by
        have hR := htrue.2
        rw [sideTrue_def] at hR
        rw [decide_eq_true_eq] at hR
        rcases hR with h1 | h2
        · rcases h1 with ⟨u, hu, huv⟩
          rw [Finset.mem_singleton.mp huv] at hu
          exact hu
        · rcases h2 with ⟨j, _, hji, hjv⟩
          rw [ih j hji] at hjv; cases hjv
      exact Finset.disjoint_left.mp (strip_disj E i) getL getR
  have strip_exists : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      ∃ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.size = E.size ∧ D.WellFormed ∧
        (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) ∧
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) ∧
        (∀ U, D.eval U = E.eval U) :=
    fun E hw => ⟨stripCircuit E, rfl, strip_wf E hw, strip_disj E, strip_gateVal_singleton E, strip_eval_eq E⟩

  let inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let liftRow (P : Finset (Fin 13)) : Finset (Fin 26) :=
    Finset.univ.filter fun k : Fin 26 =>
      (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
      ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ inc q l

  obtain ⟨D, hD_sz0, hD_wf, hD_disj, hD_sing, hD_ev0⟩ := strip_exists D0 hD0_wf
  have hD_pos : ∀ p l : Fin 13, inc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true := by
    intro p l hinc
    rw [hD_ev0, hD0_eval _ (Finset.insert_nonempty _ _)]
    have hp := hPos p l hinc
    refine Eq.trans ?_ hp
    congr 1; funext k
    exact decide_eq_decide.mpr (by simp only [Finset.mem_insert, Finset.mem_singleton])
  have hD_neg : ∀ P : Finset (Fin 13),
      (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ inc q l) ∧ inc p l) →
      ((¬∃ l : Fin 13, ∀ p ∈ P, inc p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ inc q l) → inc p l) →
      D.eval (liftRow P) = false := by
    intro P hmx hgen
    have hne : (liftRow P).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      have hP0 : P = ∅ := by
        ext p; simp only [Finset.notMem_empty, iff_false]
        intro hp
        have hm : Fin.castAdd 13 p ∈ liftRow P :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, hp, rfl⟩⟩
        rw [hem] at hm; exact Finset.notMem_empty _ hm
      exact hgen.1 ⟨0, fun p hp => by rw [hP0] at hp; exact (Finset.notMem_empty _ hp).elim⟩
    rw [hD_ev0, hD0_eval _ hne]
    have hn := hNeg P hmx hgen
    refine Eq.trans ?_ hn
    congr 1; funext k
    exact decide_eq_decide.mpr (by simp only [liftRow, inc, Finset.mem_filter, Finset.mem_univ, true_and])
  obtain ⟨hD_outVars, hD_ge11, hD_degAll, hD_pairPL, hD_pairSame⟩ :=
    hLadder D hD_wf hD_disj hD_pos hD_neg
  have hD_eq_ncard : D.size = {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
    hD_sz0.trans hD0_size
  rw [← hD_eq_ncard]
  by_contra! hlt13
  have casesSize : D.size = 11 ∨ D.size = 12 := by omega
  rcases casesSize with h11 | h12
  · exact hSize11 D hD_wf h11 hD_outVars hD_sing hD_disj hD_pos hD_neg
      (fun v => by have := hD_degAll v; dsimp only at this ⊢; omega)
      (fun p l h => by have := hD_pairPL p l h; dsimp only at this ⊢; omega)
      (fun p q h => by have := (hD_pairSame p q h).1; dsimp only at this ⊢; omega)
      (fun p q h => by have := (hD_pairSame p q h).2; dsimp only at this ⊢; omega)
  · exact hSize12 D hD_wf h12 hD_outVars hD_sing hD_disj hD_pos hD_neg
      (fun v => by have := hD_degAll v; dsimp only at this ⊢; omega)
      (fun p l h => by have := hD_pairPL p l h; dsimp only at this ⊢; omega)
      (fun p q h => by have := (hD_pairSame p q h).1; dsimp only at this ⊢; omega)
      (fun p q h => by have := (hD_pairSame p q h).2; dsimp only at this ⊢; omega)

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem and13 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  apply pg3Reduction pg3Geom
  · dsimp only
    intro D hw hd hp hn
    exact (pg3StrongBounds D hw hd hp hn).1
  · dsimp only
    intro D hw hs ho hsing hd hp hn cap _ _ _
    obtain ⟨_, both, cross⟩ := pg3StrongBounds D hw hd hp hn
    apply PGCapTwo.circuit pg3Geom D hs.le ho hd hp hn
    apply Plane1898.size12CapTwo D hw hs ho hd hp hn cap
    · intro d p q hne
      cases d
      · exact (both p q hne.symm).1
      · exact (both p q hne.symm).2
    · intro d p l hne
      cases d
      · exact cross p l hne
      · change Plane1898.Cofactor.LB D {Fin.natAdd 13 p, Fin.castAdd 13 l} 8
        rw [Finset.pair_comm]
        exact cross l p hne

end PEqualNP.Outside.L_meta_17461

namespace PEqualNP.Outside.L_meta_17461_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Classical

abbrev I (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

theorem meet : ∀ l m : Fin 13, ∃ r : Fin 13, I r l ∧ I r m := by decide
theorem join : ∀ p q : Fin 13, ∃ m : Fin 13, I p m ∧ I q m := by decide
theorem line_card : ∀ l : Fin 13, (Finset.univ.filter fun p : Fin 13 => I p l).card = 4 := by decide
theorem pencil_card : ∀ p : Fin 13, (Finset.univ.filter fun l : Fin 13 => I p l).card = 4 := by decide

theorem two_out {α : Type} [DecidableEq α] (S T : Finset α) (hS : S.card = 4) (hT : T ⊆ S)
    (h : 2 < T.card) (r1 r2 : α) (h1 : r1 ∈ S) (h2 : r2 ∈ S) (n1 : r1 ∉ T) (n2 : r2 ∉ T) :
    r1 = r2 := by
  by_contra hne
  have hsub : T ⊆ (S.erase r1).erase r2 := by
    intro p hp
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hT hp⟩⟩
    · rintro rfl; exact n2 hp
    · rintro rfl; exact n1 hp
  have hc := Finset.card_le_card hsub
  have e2 : r2 ∈ S.erase r1 := Finset.mem_erase.2 ⟨fun e => hne e.symm, h2⟩
  rw [Finset.card_erase_of_mem e2, Finset.card_erase_of_mem h1, hS] at hc
  omega

theorem arc_pts (x4 : Finset (Fin 13))
    (h3 : ¬∃ q : Fin 13, ∀ m : Fin 13, (∀ p ∈ x4, ¬I p m) → I q m) (l : Fin 13) :
    (x4.filter fun p => I p l).card ≤ 2 := by
  by_contra hc
  have hc' : 2 < (x4.filter fun p => I p l).card := by omega
  apply h3
  by_cases hex : ∃ r, I r l ∧ r ∉ x4
  · obtain ⟨r, hrl, hr⟩ := hex
    refine ⟨r, fun m hm => ?_⟩
    obtain ⟨r', h1, h2⟩ := meet l m
    have hr' : r' ∉ x4 := fun hin => hm r' hin h2
    have e : r' = r := two_out (Finset.univ.filter fun p : Fin 13 => I p l) (x4.filter fun p => I p l)
      (line_card l) (fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2⟩) hc' r' r
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hrl⟩)
      (fun h => hr' (Finset.mem_filter.1 h).1) (fun h => hr (Finset.mem_filter.1 h).1)
    rw [← e]; exact h2
  · refine ⟨l, fun m hm => ?_⟩
    obtain ⟨r', h1, h2⟩ := meet l m
    have hin : r' ∈ x4 := by
      by_contra hn
      exact hex ⟨r', h1, hn⟩
    exact absurd h2 (hm r' hin)

theorem arc_lines (x4 : Finset (Fin 13)) (h2 : ¬∃ n : Fin 13, ∀ p ∈ x4, I p n) (p : Fin 13) :
    ((Finset.univ.filter fun l : Fin 13 => ∀ q ∈ x4, ¬I q l).filter fun l => I p l).card ≤ 2 := by
  by_contra hc
  have hc' : 2 < ((Finset.univ.filter fun l : Fin 13 => ∀ q ∈ x4, ¬I q l).filter fun l => I p l).card := by
    omega
  have hQ : ∀ m : Fin 13, m ∈ ((Finset.univ.filter fun l : Fin 13 => ∀ q ∈ x4, ¬I q l).filter fun l => I p l) →
      ∀ q ∈ x4, ¬I q m := by
    intro m hm
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hm).1).2
  apply h2
  by_cases hex : ∃ n, I p n ∧ ¬(∀ q ∈ x4, ¬I q n)
  · obtain ⟨n, hpn, hn⟩ := hex
    refine ⟨n, fun r hr => ?_⟩
    obtain ⟨m, hrm, hpm⟩ := join r p
    have hm : ¬(∀ q ∈ x4, ¬I q m) := fun h => h r hr hrm
    have e : m = n := two_out (Finset.univ.filter fun l : Fin 13 => I p l)
      ((Finset.univ.filter fun l : Fin 13 => ∀ q ∈ x4, ¬I q l).filter fun l => I p l)
      (pencil_card p) (fun l hl => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hl).2⟩) hc' m n
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpm⟩) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpn⟩)
      (fun h => hm (hQ m h)) (fun h => hn (hQ n h))
    rw [← e]; exact hrm
  · refine ⟨0, fun r hr => ?_⟩
    obtain ⟨m, hrm, hpm⟩ := join r p
    have : ∀ q ∈ x4, ¬I q m := by
      by_contra hn
      exact hex ⟨m, hpm, hn⟩
    exact absurd hrm (this r hr)

theorem wires_spec (gs : List Gate) (x : List Bool) (val : ℕ → Bool)
    (h : ∀ k (hk : k < gs.length), (gs[k]).op.eval
      ((gs[k]).inputs.map fun w => (x ++ (List.range k).map val).getD w false) = val k) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      = x ++ (List.range gs.length).map val := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    have ih' := ih (fun k hk => by
      have h' := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at h')
    have hg := h gs.length (by simp)
    rw [List.getElem_append_right (le_refl _)] at hg
    simp only [Nat.sub_self, List.getElem_cons_zero] at hg
    rw [List.foldl_append, ih']
    simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons, List.length_nil]
    rw [hg, List.range_succ, List.map_append]
    simp

def BaseF (n : ℕ) (X Y : Fin n → Finset (Fin 13)) : Set (Set (Fin n)) :=
  {∅, Set.univ} ∪ Set.range fun v : Fin (13 + 13) =>
    {i : Fin n | Fin.addCases (fun p : Fin 13 => decide (p ∈ X i)) (fun l : Fin 13 => decide (l ∈ Y i)) v = true}

def Bk (n : ℕ) (X Y : Fin n → Finset (Fin 13)) (s : List (Set (Fin n))) (k : ℕ) : Set (Set (Fin n)) :=
  BaseF n X Y ∪ {t | t ∈ s.take k}

def row (n : ℕ) (X Y : Fin n → Finset (Fin 13)) (i : Fin n) : Fin (13 + 13) → Bool :=
  Fin.addCases (fun p : Fin 13 => decide (p ∈ X i)) (fun l : Fin 13 => decide (l ∈ Y i))

noncomputable def vals (n : ℕ) (s : List (Set (Fin n))) (i : Fin n) (j : ℕ) : Bool := decide (i ∈ s.getD j ∅)

theorem rep (n : ℕ) (X Y : Fin n → Finset (Fin 13)) (s : List (Set (Fin n))) (k : ℕ) (hk : k ≤ s.length)
    (a : Set (Fin n)) (ha : a ∈ Bk n X Y s k) (h0 : a ≠ ∅) (h1 : a ≠ Set.univ) :
    ∃ w : ℕ, ∀ i : Fin n,
      (List.ofFn (row n X Y i) ++ (List.range k).map (vals n s i)).getD w false = decide (i ∈ a) := by
  rcases ha with ha | ha
  · rcases ha with ha | ha
    · rcases ha with ha | ha
      · exact absurd ha h0
      · exact absurd ha h1
    · obtain ⟨v, rfl⟩ := ha
      refine ⟨v.val, fun i => ?_⟩
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp [row]
  · obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 ha
    have hjk : j < k := by omega
    have hjs : j < s.length := by omega
    refine ⟨26 + j, fun i => ?_⟩
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp [vals, hjk, hjs]

theorem gate_ex (n : ℕ) (X Y : Fin n → Finset (Fin 13)) (s : List (Set (Fin n)))
    (hval : ∀ k : Fin s.length, s.getD k ∅ ∉ Bk n X Y s k ∧ ∃ a ∈ Bk n X Y s k, ∃ b ∈ Bk n X Y s k,
      s.getD k ∅ = a ∪ b ∨ s.getD k ∅ = a ∩ b) (k : Fin s.length) :
    ∃ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧
      (g.op = GateOp.and → ¬∃ a ∈ Bk n X Y s k, ∃ b ∈ Bk n X Y s k, s.getD k ∅ = a ∪ b) ∧
      ∀ i : Fin n, g.op.eval (g.inputs.map fun w =>
        (List.ofFn (row n X Y i) ++ (List.range k).map (vals n s i)).getD w false) = vals n s i k := by
  obtain ⟨hnew, a0, ha0, b0, hb0, h0⟩ := hval k
  have hB0 : (∅ : Set (Fin n)) ∈ Bk n X Y s k := Or.inl (Or.inl (Or.inl rfl))
  have hB1 : (Set.univ : Set (Fin n)) ∈ Bk n X Y s k := Or.inl (Or.inl (Or.inr rfl))
  have nondeg : ∀ a ∈ Bk n X Y s k, ∀ b ∈ Bk n X Y s k,
      (s.getD k ∅ = a ∪ b ∨ s.getD k ∅ = a ∩ b) → a ≠ ∅ ∧ a ≠ Set.univ ∧ b ≠ ∅ ∧ b ≠ Set.univ := by
    intro a ha b hb h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> rcases h with h | h <;> apply hnew <;> rw [h] <;>
      simp [hb, ha, hB0, hB1]
  by_cases hU : ∃ a ∈ Bk n X Y s k, ∃ b ∈ Bk n X Y s k, s.getD k ∅ = a ∪ b
  · obtain ⟨a, ha, b, hb, hab⟩ := hU
    obtain ⟨a0', a1', b0', b1'⟩ := nondeg a ha b hb (Or.inl hab)
    obtain ⟨wa, hwa⟩ := rep n X Y s k (le_of_lt k.2) a ha a0' a1'
    obtain ⟨wb, hwb⟩ := rep n X Y s k (le_of_lt k.2) b hb b0' b1'
    refine ⟨⟨GateOp.or, [wa, wb]⟩, Or.inr rfl, by simp, by simp, fun i => ?_⟩
    simp only [List.map_cons, List.map_nil, hwa i, hwb i, GateOp.eval, vals]
    rw [hab]
    simp
  · rcases h0 with h0 | h0
    · exact absurd ⟨a0, ha0, b0, hb0, h0⟩ hU
    · obtain ⟨a0', a1', b0', b1'⟩ := nondeg a0 ha0 b0 hb0 (Or.inr h0)
      obtain ⟨wa, hwa⟩ := rep n X Y s k (le_of_lt k.2) a0 ha0 a0' a1'
      obtain ⟨wb, hwb⟩ := rep n X Y s k (le_of_lt k.2) b0 hb0 b0' b1'
      refine ⟨⟨GateOp.and, [wa, wb]⟩, Or.inl rfl, by simp, fun _ => hU, fun i => ?_⟩
      simp only [List.map_cons, List.map_nil, hwa i, hwb i, GateOp.eval, vals]
      rw [h0]
      simp

theorem cast_ne_nat (a b : Fin 13) : Fin.castAdd 13 a ≠ Fin.natAdd 13 b := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

theorem cast_inj (a b : Fin 13) : Fin.castAdd 13 a = Fin.castAdd 13 b ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp at h'
    exact Fin.ext h'
  · rintro rfl; rfl

theorem nat_inj (a b : Fin 13) : Fin.natAdd 13 a = Fin.natAdd 13 b ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp at h'
    exact Fin.ext h'
  · rintro rfl; rfl

theorem core (h1898 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard)
    (n : ℕ) (X Y : Fin n → Finset (Fin 13))
    (hpos : ∀ p l : Fin 13, I p l → ∃ i, X i = {p} ∧ Y i = {l})
    (hneg : ∀ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬I p l) →
      (∀ l : Fin 13, (P.filter fun p => I p l).card ≤ 2) →
      (∀ p : Fin 13, (Q.filter fun l => I p l).card ≤ 2) → ∃ i, X i = P ∧ Y i = Q)
    (s : List (Set (Fin n)))
    (hval : ∀ k : Fin s.length, s.getD k ∅ ∉ Bk n X Y s k ∧ ∃ a ∈ Bk n X Y s k, ∃ b ∈ Bk n X Y s k,
      s.getD k ∅ = a ∪ b ∨ s.getD k ∅ = a ∩ b)
    (hmem : {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} ∈ BaseF n X Y ∪ {t | t ∈ s}) :
    13 ≤ {k : Fin s.length | ¬∃ a ∈ Bk n X Y s k, ∃ b ∈ Bk n X Y s k, s.getD k ∅ = a ∪ b}.ncard := by
  choose g hg using gate_ex n X Y s hval
  have hTB : {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} ∉ BaseF n X Y := by
    rintro ((h | h) | ⟨v, hv⟩)
    · obtain ⟨i, hi⟩ := hpos 0 0 (Or.inl rfl)
      have hin : i ∈ {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} := ⟨0, 0, Or.inl rfl, hi.1, hi.2⟩
      rw [h] at hin
      exact hin
    · obtain ⟨i, hi⟩ := hneg ∅ ∅ (by simp) (by simp) (by simp)
      have hin : i ∈ {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} := by
        rw [h]; trivial
      obtain ⟨p, l, -, hX, -⟩ := hin
      rw [hi.1] at hX
      exact absurd hX (by simp)
    · induction v using Fin.addCases with
      | left p =>
        obtain ⟨i, hi⟩ := hneg {p} ∅ (by simp) (fun l => (Finset.card_filter_le _ _).trans (by simp))
          (by simp)
        have hin : i ∈ {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} := by
          rw [← hv]; simp [hi.1]
        obtain ⟨p', l', -, -, hY⟩ := hin
        rw [hi.2] at hY
        exact absurd hY (by simp)
      | right l =>
        obtain ⟨i, hi⟩ := hneg ∅ {l} (by simp) (by simp)
          (fun p => (Finset.card_filter_le _ _).trans (by simp))
        have hin : i ∈ {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} := by
          rw [← hv]; simp [hi.2, -Fin.natAdd_eq_addNat]
        obtain ⟨p', l', -, hX, -⟩ := hin
        rw [hi.1] at hX
        exact absurd hX (by simp)
  rcases hmem with hm | hm
  · exact absurd hm hTB
  obtain ⟨t, ht, hst⟩ := List.getElem_of_mem hm
  have hw : ∀ i : Fin n, (⟨List.ofFn g, 26 + t⟩ : Circuit).wires (List.ofFn (row n X Y i))
      = List.ofFn (row n X Y i) ++ (List.range s.length).map (vals n s i) := by
    intro i
    have h := wires_spec (List.ofFn g) (List.ofFn (row n X Y i)) (vals n s i) (fun k hk => by
      have hk' : k < s.length := by simpa using hk
      rw [List.getElem_ofFn]
      exact (hg ⟨k, hk'⟩).2.2.2 i)
    rw [List.length_ofFn] at h
    exact h
  have hev : ∀ i : Fin n, circuitFun (13 + 13) ⟨List.ofFn g, 26 + t⟩ (row n X Y i)
      = decide (i ∈ {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}}) := by
    intro i
    show ((⟨List.ofFn g, 26 + t⟩ : Circuit).wires (List.ofFn (row n X Y i))).getD (26 + t) false = _
    rw [hw i, List.getD_append_right _ _ _ _ (by simp)]
    simp [vals, ht, hst]
  have hmono : Monotone2 ⟨List.ofFn g, 26 + t⟩ := by
    intro g' hg'
    obtain ⟨k, rfl⟩ := (List.mem_ofFn).1 hg'
    refine ⟨?_, (hg k).2.1⟩
    rcases (hg k).1 with h | h <;> rw [h] <;> simp
  have h13 := h1898 ⟨List.ofFn g, 26 + t⟩ hmono (by
    intro p l hpl
    obtain ⟨i, hX, hY⟩ := hpos p l hpl
    refine Eq.trans (congrArg (circuitFun (13 + 13) ⟨List.ofFn g, 26 + t⟩) (?_ : _ = row n X Y i))
      ((hev i).trans ?_)
    · funext x
      induction x using Fin.addCases with
      | left q => simp [row, hX, cast_ne_nat, cast_inj, -Fin.natAdd_eq_addNat]
      | right q => simp [row, hY, (cast_ne_nat _ _).symm, nat_inj, -Fin.natAdd_eq_addNat]
    · simp only [decide_eq_true_eq]
      exact ⟨p, l, hpl, hX, hY⟩) (by
    intro x4 _ hc
    obtain ⟨c2, c3⟩ := hc
    obtain ⟨i, hX, hY⟩ := hneg x4 (Finset.univ.filter fun l : Fin 13 => ∀ q ∈ x4, ¬I q l)
      (fun p hp l hl => (Finset.mem_filter.1 hl).2 p hp) (arc_pts x4 c3) (arc_lines x4 c2)
    refine Eq.trans (congrArg (circuitFun (13 + 13) ⟨List.ofFn g, 26 + t⟩) (?_ : _ = row n X Y i))
      ((hev i).trans ?_)
    · funext x
      induction x using Fin.addCases with
      | left q => simp [row, hX, cast_ne_nat, cast_inj, -Fin.natAdd_eq_addNat]
      | right q => simp [row, hY, (cast_ne_nat _ _).symm, nat_inj, -Fin.natAdd_eq_addNat]
    · simp only [decide_eq_false_iff_not]
      rintro ⟨p, l, hpl, hXp, hYl⟩
      have hp : p ∈ x4 := by rw [← hX, hXp]; simp
      have hl : l ∈ (Finset.univ.filter fun l : Fin 13 => ∀ q ∈ x4, ¬I q l) := by rw [← hY, hYl]; simp
      exact (Finset.mem_filter.1 hl).2 p hp hpl)
  refine le_trans h13 (Set.ncard_le_ncard_of_injOn (fun j => Fin.cast (List.length_ofFn) j) ?_ ?_
    (Set.toFinite _))
  · intro j hj
    have hj' : ((List.ofFn g).get j).op = GateOp.and := hj
    rw [List.get_ofFn] at hj'
    exact (hg _).2.2.1 hj'
  · intro a _ b _ h
    exact Fin.cast_injective _ h

end PEqualNP.Outside.L_meta_17461_aux

theorem PEqualNP.Outside.L_meta_17461 : (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : ℕ) (x3 x4 : Fin x2 → Finset (Fin (13 : ℕ))),   (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → ∃ (x8 : Fin x2), x3 x8 = {x5} ∧ x4 x8 = {x6}) →     (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) → (∀ (x9 : Fin (13 : ℕ)), {x10 ∈ x6 | x1 x10 x9}.card ≤ (2 : ℕ)) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x1 x10 x11}.card ≤ (2 : ℕ)) → ∃ (x11 : Fin x2), x3 x11 = x6 ∧ x4 x11 = x7) →       have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x3 x8)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x4 x8)) x7 = Bool.true};       ∀ (x8 : List (Set (Fin x2))), x8.length ≤ (63 : ℕ) → (∀ (x10 : Fin x8.length), x8.getD ↑x10 ∅ ∉ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ List.take (↑x10) x8} ∧ ∃ x11 ∈ x7 ∪ {x12 : Set (Fin x2) | x12 ∈ List.take (↑x10) x8}, ∃ x12 ∈ x7 ∪ {x13 : Set (Fin x2) | x13 ∈ List.take (↑x10) x8}, x8.getD ↑x10 ∅ = x11 ∪ x12 ∨ x8.getD ↑x10 ∅ = x11 ∩ x12) → {x11 : Fin x2 | ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x1 x12 x13 ∧ x3 x11 = {x12} ∧ x4 x11 = {x13}} ∈ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ x8} → (13 : ℕ) ≤ {x12 : Fin x8.length | ¬∃ x13 ∈ x7 ∪ {x14 : Set (Fin x2) | x14 ∈ List.take (↑x12) x8}, ∃ x14 ∈ x7 ∪ {x15 : Set (Fin x2) | x15 ∈ List.take (↑x12) x8}, x8.getD ↑x12 ∅ = x13 ∪ x14}.ncard) := by
  intro x1 n X Y hpos hneg B s hlen hval hmem
  exact PEqualNP.Outside.L_meta_17461_aux.core PEqualNP.Outside.L_meta_17461.and13 n X Y hpos hneg s hval hmem
