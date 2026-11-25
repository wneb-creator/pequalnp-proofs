import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_1898

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

-- Read each of the two slots, assigning the least unused gate with sign zero
-- on a first occurrence. Later assignments may not disturb previously read slots.
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

end PEqualNP.Outside.L_meta_1898

namespace PEqualNP.Outside.L_meta_1898

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

end PEqualNP.Outside.L_meta_1898

namespace PEqualNP.Outside.L_meta_1898

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

end PEqualNP.Outside.L_meta_1898
namespace PEqualNP.Outside.L_meta_1898

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

end PEqualNP.Outside.L_meta_1898

namespace PEqualNP.Outside.L_meta_1898

private abbrev sgInc (q m : Fin 13) := q = m ∨ q = m + 1 ∨ q = m + 3 ∨ q = m + 9
private abbrev sgPt := (Fin.castAdd 13 : Fin 13 → Fin 26)
private abbrev sgLn := (Fin.natAdd 13 : Fin 13 → Fin 26)
private def sgData : List (Nat × Nat) := [(0, 35777249544923), (1, 16836275385376), (2, 70560147653389), (2, 263891376406528), (1, 8416809216), (16, 281466386776064), (36, 792739058), (40, 1953679), (16, 5703717727342), (260, 205347809787920), (128, 10725122781296), (1280, 123205914198913)]
private def sgP : List Nat := [29, 39, 71, 77, 83, 85, 101, 105, 135, 141, 195, 201, 275, 281, 297, 329, 337, 549, 7, 13, 19, 21, 25, 35, 37, 41, 67, 69, 73, 81, 97, 131, 133, 137, 265, 273]
private def sgW : List Nat := [2592, 392, 896, 2816, 644, 2688, 2432, 2306, 776, 800, 772, 770, 580, 2624, 2114, 2562, 2564, 2184, 904, 2848, 708, 2720, 2656, 456, 2440, 2370, 900, 2944, 2818, 2692, 2434, 780, 808, 802, 2626, 2628]
private abbrev sgBit (m : List Nat) (s : Fin 36 × Fin 13) (q : Fin 13) :=
  (m.getD s.1.val 0).testBit (q - s.2).val

-- Four bits per coordinate; nine bits per row number (orbit times 13 plus shift).
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

-- The row table is that of the 36 cyclic orbits, numbered by orbit and shift.
-- The resulting witnesses work for an arbitrary seeded nonincident point/line pair.
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

end PEqualNP.Outside.L_meta_1898


namespace PEqualNP.Outside.L_meta_1898

-- For each rejected row, choose at most one absent operand per gate.
-- The choices simultaneously witness all vertices whose addition is accepted.
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
  -- Part 1: Basic AndCountCircuit n evaluation helpers
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

end PEqualNP.Outside.L_meta_1898
namespace PEqualNP.Outside.L_meta_1898
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

-- Direct output variables can be removed on the selected rows and their relevant extensions.
-- This lets us use the signed row certificate without a global restriction on the output.
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

end PEqualNP.Outside.L_meta_1898

namespace PEqualNP.Outside.L_meta_1898

open PEqualNP.AndCount in
theorem pg3Cofactor (n : ℕ) (E : AndCountCircuit n) (T : Finset (Fin n)) :
    E.WellFormed → E.eval T = false →
    ∃ F : AndCountCircuit n, F.WellFormed ∧ F.size = E.size ∧
      ∀ U : Finset (Fin n), F.eval U = E.eval (T ∪ U) := by
  classical
  intro hWF hT
  -- On every nonempty input, the OR of all variables represents true.
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
  · -- At the empty input there is no constant true, but the requested value is false.
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    have fuelFalse (d : ℕ) (i : Fin F.size) : F.gateValFuel ∅ d i = false := by
      induction d generalizing i with
      | zero => rfl
      | succ d ih => simp [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue, ih]
    rw [Finset.union_empty, hT]
    simp [AndCountCircuit.eval, AndCountCircuit.gateVal, fuelFalse]

end PEqualNP.Outside.L_meta_1898
namespace PEqualNP.Outside.L_meta_1898

-- Equality columns for the two endpoints at a vertex. Bit `i` belongs to
-- the `i`th candidate. The incident-row mask is common to all candidates.
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

-- Materialize hits by row before computing forced endpoints; `List` data
-- also lets the kernel share the projection of each row across vertices.
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

-- A candidate-elimination certificate `(a,b,j,k,r)`. Endpoints use twice
-- the vertex index plus the endpoint side. Vertex 12 denotes duplication as the
-- forcing reason; endpoint 24 denotes collision with a hit rather than collision
-- of two opposite forced endpoints. All hypotheses are checked on row `r`.
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

end PEqualNP.Outside.L_meta_1898
namespace PEqualNP.Outside.L_meta_1898

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

end PEqualNP.Outside.L_meta_1898
namespace PEqualNP.Outside.L_meta_1898

private def reLow (w : Nat) : Nat := (1 <<< w) - 1

private theorem reLow_bit (w i : Nat) : (reLow w).testBit i = decide (i<w) := by
  simp [reLow, Nat.shiftLeft_eq]

private theorem reBefore {k l w i : Nat} (h : k < l) (hi : i < w) :
    k*w+i < l*w := by
  have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at this
  omega

-- Replicate a width-w word into 2^d blocks, doubling the packed word each time.
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

-- Insert a (clipped) parent word into block n. Clipping also makes the
-- operation well-defined on words with stray high bits.
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

-- The canonical mask is exact, not just an overapproximation of valid lanes.
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

end PEqualNP.Outside.L_meta_1898
namespace PEqualNP.Outside.L_meta_1898

-- A parallel bit move keeps some input positions fixed and moves others
-- down by a common distance. Each mask is independent of the payload word.
abbrev RPlan := List (Nat × Nat × Nat)

def rcPext : RPlan → Nat → Nat
  | [], w => w
  | (s, k, v) :: p, w => rcPext p ((w &&& k) ||| ((w &&& v) >>> s))

-- Prefix parity by doubling, followed by the standard right-compress
-- schedule: at stage j a selected bit crosses 2^j holes if that bit of
-- its displacement is set. Only logarithmically many whole-word moves
-- are made. Correctness of each concrete schedule is checked separately.
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

-- Check coverage of all incoming lanes, no lost bits under right shift,
-- no two destinations in conflict, and the final range.
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

end PEqualNP.Outside.L_meta_1898
namespace PEqualNP.Outside.L_meta_1898

-- A dense frontier is recorded as four bit planes per endpoint. Its expansion
-- has one lane for each possible extension of each member of the frontier.
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

end PEqualNP.Outside.L_meta_1898
namespace PEqualNP.Outside.L_meta_1898

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

end PEqualNP.Outside.L_meta_1898
