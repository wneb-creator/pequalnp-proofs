import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17651_aux

abbrev V := Fin 13
def Near (p l : V) : Prop := p-l ∈ ({0,1,3,9} : Finset V)
instance (p l : V) : Decidable (Near p l) := inferInstanceAs (Decidable (_ ∈ (_ : Finset V)))
private abbrev Code := Nat × Nat
private def index (p l : V) := p.val * 13 + l.val
private def act (word : Nat) (i : V) : V := Fin.ofNat 13 ((word >>> (4 * i.val)) % 16)
private def Good (t : Code) : Prop := Function.Bijective (act t.1) ∧ Function.Bijective (act t.2) ∧
  ∀ x y : V, Near (act t.1 x) (act t.2 y) ↔ Near x y
private instance (t : Code) : Decidable (Good t) := by
  unfold Good Function.Bijective Function.Injective Function.Surjective
  infer_instance

def reps : List (V × V) := [(0,4),(1,0),(1,1),(4,4),(2,1)]
private def firstTable : Array Code := #[
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1612739660317728,1172747050833948),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2306141775508128,3501204568310298),
  (3582863703552528,3582863703552528),
  (961496268034368,64281090204948),
  (1873141406438403,1028497443279168),
  (3282623728394508,3282623728394508),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3285836428231173,749554303861188),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1012259710853643,572267101370058),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (661256292876348,3423215812285443),
  (2982383753236683,2982383753236683),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3033786950623323,2985669607038018),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (430705406648403,96449573624898),
  (2387686879003953,1543193177998368),
  (3582863703552528,3582863703552528),
  (1572901431280578,728257468121148),
  (2682143778081978,2682143778081978),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3504594936268218,2734717438903338),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1312499685159708,872507076527883),
  (3582863703552528,3582863703552528),
  (361016317721643,3122975837127618),
  (2381903802977193,2381903802977193),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (588872973059403,593051118126408),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2985596453073348,449314342334643),
  (3582863703552528,3582863703552528),
  (1272661456175793,428017492966443),
  (2081663828671128,2081663828671128),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (414768314209458,481618635281538),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2733546975468618,2685429849983793),
  (3582863703552528,3582863703552528),
  (2348184789330708,2344680260092593),
  (1781423867144583,1781423867144583),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2132693399980833,3202298537134113),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3204354961163433,2434480953406233),
  (3582863703552528,3582863703552528),
  (712019735695818,500725544789433),
  (1481184110090358,1481184110090358),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (446788394595378,288457058203698),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1837422771718938,2910872243091633),
  (3582863703552528,3582863703552528),
  (2385116516392098,3508009089260433),
  (2416798353042498,3525380749293873),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2645014686155553,111713303888673),
  (1787838332154393,1787412862218768),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3225989020943298,763766796027708),
  (3582863703552528,3582863703552528),
  (1467887353162938,2576432442201018),
  (2747689558652838,1850530214546298),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1583815550247318,1577008031277318),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2076228434017323,3213069481702338),
  (3582863703552528,3582863703552528),
  (968199513754533,690522428881833),
  (3430636292110953,2586885668517798),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (571104042889668,497436495192243),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2819231115233463,2150714355129483),
  (3582863703552528,3582863703552528),
  (1980393337961043,2041159607368338),
  (288632998753338,292866977543223),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (130465431493698,3455384295705393),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (144133860969258,3033575052625953),
  (3582863703552528,3582863703552528),
  (60776343415578,2822735862022833),
  (223928981472033,223928981472033)]
private def first (p l : V) : Code := firstTable.getD (index p l) (0,0)
private def secondTable : Array Code := #[
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2344830545572368,3470648025969168),
  (3582863703552528,3582863703552528),
  (1524574000919568,1225502224032528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1785171014335248,2907561730519728),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2891282456786448,2837393484575568),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2440488301171248,3512431606518048),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2380565691732528,3505636347905568),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1524574000919568,1225502224032528),
  (2440488301171248,3512431606518048),
  (3582863703552528,3582863703552528),
  (2440488301171248,3512431606518048),
  (2944039099964208,2942938841357088),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1612520352126768,1172732603292528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1524574000919568,1225502224032528),
  (3582863703552528,3582863703552528),
  (2944039099964208,2942938841357088),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2158429485569328,1260802769971488),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2153486052234288,1260492776321328),
  (3582863703552528,3582863703552528),
  (3316790411474448,3022048344679248),
  (1785171014335248,2907561730519728),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2942411314337328,2942411314337328),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2969349033039408,2951745099797808),
  (3582863703552528,3582863703552528),
  (3316790411474448,3022048344679248),
  (2124349389050928,1263019173242928),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1785171014335248,2907561730519728),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2863773737499408,2846181282837168),
  (3582863703552528,3582863703552528),
  (1607585497912368,1172471872788528),
  (1612520352126768,1172732603292528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2891282456786448,2837393484575568),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2370076137700368,3477231981851568),
  (3582863703552528,3582863703552528),
  (3494876282296368,3442116045092208),
  (2434398122449968,3512189829024048),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2171075000022288,1330856704373328),
  (2380565691732528,3505636347905568),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2380565691732528,3505636347905568),
  (3582863703552528,3582863703552528),
  (2158429485569328,1260802769971488),
  (2942411314337328,2942411314337328),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (2184273136858128,1333059741446928),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1902817756650288,2881171846617888),
  (3582863703552528,3582863703552528),
  (2957782852934448,2951181201872928),
  (2344830545572368,3470648025969168),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (1456405033129008,1174925758583088),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3144716408624688,2863890995381808),
  (3582863703552528,3582863703552528),
  (2891282456786448,2837393484575568),
  (2863773737499408,2846181282837168),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (763715422264368,3424327386274608),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (3582863703552528,3582863703552528),
  (767580822804528,3423997676251248),
  (3582863703552528,3582863703552528),
  (746140164503568,3406738945746768),
  (1314556992042768,1155076263262128)]
private def second (p l : V) : Code := secondTable.getD (index p l) (0,0)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem first_correct : ∀ p l : V, Near p l →
    Good (first p l) ∧ act (first p l).1 p=0 ∧ act (first p l).2 l=0 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem second_correct : ∀ p l : V, Near p l → (p,l) ≠ (0,0) →
    Good (second p l) ∧ act (second p l).1 0=0 ∧ act (second p l).2 0=0 ∧
      (act (second p l).1 p,act (second p l).2 l) ∈ reps := by decide +kernel

theorem normalize (p l q m : V) (pl : Near p l) (qm : Near q m) (distinct : (p,l) ≠ (q,m)) :
    ∃ σ τ : Equiv.Perm V, (∀ a b, Near (σ a) (τ b) ↔ Near a b) ∧ σ p=0 ∧ τ l=0 ∧ (σ q,τ m) ∈ reps := by
  classical
  let a := first p l
  obtain ⟨⟨ap,al,ai⟩,p0,l0⟩ := first_correct p l pl
  let u := act a.1 q
  let v := act a.2 m
  have inc : Near u v := (ai q m).mpr qm
  have different : (u,v) ≠ (0,0) := by
    intro eq
    have eu : act a.1 q=0 := congrArg Prod.fst eq
    have ev : act a.2 m=0 := congrArg Prod.snd eq
    exact distinct (Prod.ext (ap.1 (p0.trans eu.symm)) (al.1 (l0.trans ev.symm)))
  let b := second u v
  obtain ⟨⟨bp,bl,bi⟩,p1,l1,both⟩ := second_correct u v inc different
  let σ : Equiv.Perm V := (Equiv.ofBijective _ ap).trans (Equiv.ofBijective _ bp)
  let τ : Equiv.Perm V := (Equiv.ofBijective _ al).trans (Equiv.ofBijective _ bl)
  refine ⟨σ,τ,fun h k => (bi _ _).trans (ai h k), ?_, ?_, both⟩
  · change act b.1 (act a.1 p)=0
    change act a.1 p=0 at p0
    exact (congrArg (act b.1) p0).trans p1
  · change act b.2 (act a.2 l)=0
    change act a.2 l=0 at l0
    exact (congrArg (act b.2) l0).trans l1

abbrev Bits := Fin 26 → Bool
abbrev Reply := Bits → Bool × Bool

def flag (p l : V) : Bits := Fin.append (fun i => decide (i=p)) (fun i => decide (i=l))
def cap (Q : Finset V) := Q.card=4 ∧ ∀ l : V, (Q.filter (fun p => Near p l)).card ≤ 2
def negative (Q : Finset V) : Bits := Fin.append (fun i => decide (i∈Q))
  (fun l => decide (∀ p ∈ Q, ¬ Near p l))

def covers (F : Reply) := ∀ p l, Near p l → (F (flag p l)).1 = true ∨ (F (flag p l)).2 = true
def rejects (F : Reply) := ∀ Q, cap Q → F (negative Q) = (false,false)

def permutation (σ τ : Equiv.Perm V) : Equiv.Perm (Fin 26) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ τ).trans finSumFinEquiv)

private theorem pLeft (σ τ : Equiv.Perm V) (p : V) :
    permutation σ τ (Fin.castAdd 13 p) = Fin.castAdd 13 (σ p) := by
  change finSumFinEquiv (Sum.map σ τ ((finSumFinEquiv : V ⊕ V ≃ Fin (13+13)).symm (Fin.castAdd 13 p))) = _
  rw [finSumFinEquiv_symm_apply_castAdd p,Sum.map_inl,finSumFinEquiv_apply_left]

private theorem pRight (σ τ : Equiv.Perm V) (l : V) :
    permutation σ τ (Fin.natAdd 13 l) = Fin.natAdd 13 (τ l) := by
  change finSumFinEquiv (Sum.map σ τ ((finSumFinEquiv : V ⊕ V ≃ Fin (13+13)).symm (Fin.natAdd 13 l))) = _
  rw [finSumFinEquiv_symm_apply_natAdd l,Sum.map_inr,finSumFinEquiv_apply_right]

private theorem shift_flag (σ τ : Equiv.Perm V) (p l : V) :
    flag (σ p) (τ l) ∘ permutation σ τ = flag p l := by
  funext i
  cases i using Fin.addCases (m := 13) (n := 13) with
  | left i =>
    change flag _ _ (permutation σ τ (Fin.castAdd 13 i)) = flag _ _ (Fin.castAdd 13 i)
    rw [pLeft]; simp only [flag,Fin.append_left,Equiv.apply_eq_iff_eq]
  | right i =>
    change flag _ _ (permutation σ τ (Fin.natAdd 13 i)) = flag _ _ (Fin.natAdd 13 i)
    rw [pRight]; simp only [flag,Fin.append_right,Equiv.apply_eq_iff_eq]

private theorem shift_cap {σ τ : Equiv.Perm V} (iso : ∀ a b, Near (σ a) (τ b) ↔ Near a b)
    {Q : Finset V} (hc : cap Q) : cap (Q.map σ.toEmbedding) := by
  refine ⟨by simpa using hc.1,?_⟩
  intro l
  have H : (Q.map σ.toEmbedding).filter (fun p => Near p l) =
      (Q.filter (fun p => Near p (τ.symm l))).map σ.toEmbedding := by
    ext p
    obtain ⟨a,rfl⟩ := σ.surjective p
    have rel : Near (σ a) l ↔ Near a (τ.symm l) := by simpa using iso a (τ.symm l)
    simp [Finset.mem_filter,rel]
  rw [H,Finset.card_map]
  exact hc.2 _

private theorem shift_negative {σ τ : Equiv.Perm V} (iso : ∀ a b, Near (σ a) (τ b) ↔ Near a b)
    (Q : Finset V) : negative (Q.map σ.toEmbedding) ∘ permutation σ τ = negative Q := by
  funext i
  cases i using Fin.addCases (m := 13) (n := 13) with
  | left p =>
    change negative _ (permutation σ τ (Fin.castAdd 13 p)) = negative _ (Fin.castAdd 13 p)
    rw [pLeft]; simp [negative]
  | right l =>
    change negative _ (permutation σ τ (Fin.natAdd 13 l)) = negative _ (Fin.natAdd 13 l)
    rw [pRight]
    simp only [negative,Fin.append_right]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff,decide_eq_true_iff]
    constructor
    · intro none p hp
      exact fun edge => none (σ p) (Finset.mem_map.mpr ⟨p,hp,rfl⟩) ((iso p l).mpr edge)
    · intro none p hp
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hp
      exact fun edge => none a ha ((iso a l).mp edge)

theorem transport (F : Reply) {σ τ : Equiv.Perm V} (iso : ∀ a b, Near (σ a) (τ b) ↔ Near a b)
    (swap : Bool) (cp : covers F) (cr : rejects F) :
    let H : Reply := fun z => let r := F (z ∘ permutation σ τ); if swap then r.swap else r
    covers H ∧ rejects H := by
  dsimp only
  constructor
  · intro p l incidence
    obtain ⟨a,rfl⟩ := σ.surjective p
    obtain ⟨b,rfl⟩ := τ.surjective l
    have hit := cp a b ((iso a b).mp incidence)
    cases swap <;> simp only [shift_flag,Bool.false_eq_true,ite_false,ite_true,Prod.fst_swap,Prod.snd_swap] <;> tauto
  · intro Q hc
    let Q0 := Q.map σ.symm.toEmbedding
    have back : Q0.map σ.toEmbedding = Q := by ext p; simp [Q0]
    have invIso (p l) : Near (σ.symm p) (τ.symm l) ↔ Near p l := by
      simpa using (iso (σ.symm p) (τ.symm l)).symm
    have good := cr Q0 (shift_cap invIso hc)
    have transported := shift_negative iso Q0
    rw [back] at transported
    cases swap <;> simp [transported,good]

def reps4 : List (V × V) := [(0,4),(1,0),(1,1),(2,1)]

private theorem drop_fifth (a b : V) (h : (a,b) ∈ reps) (exclude : (a,b) ≠ (4,4)) : (a,b) ∈ reps4 := by
  simp only [reps,List.mem_cons,List.not_mem_nil,or_false] at h
  simp only [reps4,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem semantic_orbits (F : Reply) (cp : covers F) (cr : rejects F)
    (one : ∃ p l, Near p l ∧ F (flag p l) = (true,false))
    (two : ∃ q m, Near q m ∧ F (flag q m) = (false,true)) :
    ∃ (π : Equiv.Perm (Fin 26)) (s : Bool),
      let H : Reply := fun z => let r := F (z ∘ π); if s then r.swap else r
      covers H ∧ rejects H ∧ H (flag 0 0)=(true,false) ∧
      ∃ e ∈ reps4, H (flag e.1 e.2)=(false,true) := by
  obtain ⟨p,l,pl,r1⟩ := one
  obtain ⟨q,m,qm,r2⟩ := two
  have diff : (p,l) ≠ (q,m) := by rintro h; cases h; rw [r1] at r2; cases r2
  obtain ⟨σ,τ,iso,p0,l0,rep⟩ := normalize p l q m pl qm diff
  by_cases special : (σ q,τ m)=(4,4)
  · have xy : Near p m := (iso p m).mp (by rw [p0,show τ m=4 from congrArg Prod.snd special]; decide)
    obtain ⟨σ',τ',iso',q0,m0,rep'⟩ := normalize q m p l qm pl diff.symm
    have notbad : (σ' p,τ' l) ≠ (4,4) := by
      intro eq
      have edge := (iso' p m).mpr xy
      rw [m0,show σ' p=4 from congrArg Prod.fst eq] at edge
      exact (by decide : ¬ Near 4 0) edge
    have hfirst : flag 0 0 ∘ permutation σ' τ' = flag q m := by simpa [q0,m0] using shift_flag σ' τ' q m
    obtain ⟨c1,c2⟩ := transport F iso' true cp cr
    refine ⟨permutation σ' τ', true,c1,c2,?_,(σ' p,τ' l),drop_fifth _ _ rep' notbad,?_⟩
    · simp [hfirst,r2]
    · simp [shift_flag,r1]
  · have hfirst : flag 0 0 ∘ permutation σ τ = flag p l := by simpa [p0,l0] using shift_flag σ τ p l
    obtain ⟨c1,c2⟩ := transport F iso false cp cr
    refine ⟨permutation σ τ,false,c1,c2,?_,(σ q,τ m),drop_fifth _ _ rep special,?_⟩
    · simp [hfirst,r1]
    · simp [shift_flag,r2]

open PEqualNP.HeptadCover

def X (P L : Finset V) : Bits := Fin.append (fun i => decide (i∈P)) (fun i => decide (i∈L))

private theorem incidence : ∀ p l : V, p ∈ singerLines3 l ↔ Near p l := by decide +kernel
private theorem active : ∀ r : Bool × Bool, r ≠ (false,false) ↔ r.1=true ∨ r.2=true := by decide
private theorem code_mem : ∀ p l : V, (p,l) ∈ reps4 → 13*p.val + l.val ∈ ([4,13,14,27] : List Nat) := by decide +kernel

private theorem flag_eq (p l : V) : X {p} {l} = flag p l := by simp [X,flag]

private theorem cap_eq (Q : Finset V) : IsQuadrangle singerLines3 Q ↔ cap Q := by
  have eq (l : V) : Q.filter (fun p => Near p l) = Q ∩ singerLines3 l := by
    ext p; simp [incidence]
  simp only [cap,IsQuadrangle,eq]

private theorem neg_eq (Q : Finset V) : X Q (missLines singerLines3 Q) = negative Q := by
  unfold X negative
  congr 1
  funext l
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff,missLines,Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
  constructor
  · intro h p hp hi; exact h ((incidence p l).mpr hi) hp
  · intro h p hi hp; exact h p hp ((incidence p l).mp hi)

theorem normal_child : let X := fun (P L : Finset (Fin 13)) => Fin.append (fun i => decide (i ∈ P)) (fun i => decide (i ∈ L))
    let fits := fun (F : (Fin 26 → Bool) → Bool × Bool) =>
      (∀ p l : Fin 13, p ∈ singerLines3 l → F (X {p} {l}) ≠ (false,false)) ∧
      (∀ Q, IsQuadrangle singerLines3 Q → F (X Q (missLines singerLines3 Q)) = (false,false))
    let privateRow := fun (F : (Fin 26 → Bool) → Bool × Bool) (t : Bool × Bool) =>
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ F (X {p} {l}) = t
    let test := fun (F : (Fin 26 → Bool) → Bool × Bool) => F (X {0} {0}) = (true,false) ∧
       ∃ p l : Fin 13, 13*p.val+l.val ∈ ([4,13,14,27] : List ℕ) ∧ F (X {p} {l}) = (false,true)
    let swap := fun (t : Bool) (v : Bool × Bool) => if t then v.swap else v
    ∀ F, fits F → privateRow F (true,false) → privateRow F (false,true) →
      ∃ (π : Equiv.Perm (Fin 26)) (t : Bool), let H := fun x => swap t (F (x ∘ π))
      fits H ∧ test H := by
  dsimp only
  intro F fits firstPrivate secondPrivate
  obtain ⟨one,two⟩ := fits
  have yes : covers F := by
    intro p l pl
    have h := one p l ((incidence p l).mpr pl)
    change F (X {p} {l}) ≠ (false,false) at h
    rw [flag_eq] at h
    exact (active _).mp h
  have no : rejects F := by
    intro Q q
    have h := two Q ((cap_eq Q).mpr q)
    change F (X Q (missLines singerLines3 Q)) = (false,false) at h
    rwa [neg_eq] at h
  obtain ⟨p,l,hp,respond⟩ := firstPrivate
  obtain ⟨q,m,hq,reply⟩ := secondPrivate
  change F (X {p} {l}) = (true,false) at respond
  change F (X {q} {m}) = (false,true) at reply
  rw [flag_eq] at respond reply
  obtain ⟨π,t,ac,rj,h0,h1⟩ := semantic_orbits F yes no ⟨p,l,(incidence p l).mp hp,respond⟩
    ⟨q,m,(incidence q m).mp hq,reply⟩
  let H : Reply := fun z => if t then (F (z ∘ π)).swap else F (z ∘ π)
  change covers H at ac
  change rejects H at rj
  change H (flag 0 0)=(true,false) at h0
  change ∃ e ∈ reps4, H (flag e.1 e.2)=(false,true) at h1
  refine ⟨π,t,⟨?_,?_⟩,?_,?_⟩
  · intro p l pl
    change H (X {p} {l}) ≠ (false,false)
    rw [flag_eq]
    exact (active _).mpr (ac p l ((incidence p l).mp pl))
  · intro Q hQ
    change H (X Q (missLines singerLines3 Q)) = (false,false)
    rw [neg_eq]
    exact rj Q ((cap_eq Q).mp hQ)
  · change H (X {0} {0}) = (true,false)
    rwa [flag_eq]
  · obtain ⟨⟨p,l⟩,inside,response⟩ := h1
    refine ⟨p,l,code_mem p l inside,?_⟩
    change H (X {p} {l}) = (false,true)
    rwa [flag_eq]

end PEqualNP.Outside.L_meta_17651_aux

theorem PEqualNP.Outside.L_meta_17651 : (have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2); have x2 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Prop := fun (x2 : (Fin (26 : ℕ) → Bool) → Bool × Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2 (x1 {x3} {x4}) ≠ (Bool.false, Bool.false)) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2 (x1 x3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x3)) = (Bool.false, Bool.false); have x3 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Bool × Bool → Prop := fun (x3 : (Fin (26 : ℕ) → Bool) → Bool × Bool) (x4 : Bool × Bool) => ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (x1 {x5} {x6}) = x4; have x4 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Prop := fun (x4 : (Fin (26 : ℕ) → Bool) → Bool × Bool) => x4 (x1 {(0 : Fin (13 : ℕ))} {(0 : Fin (13 : ℕ))}) = (Bool.true, Bool.false) ∧ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (13 : ℕ) * ↑x5 + ↑x6 ∈ [(4 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ)] ∧ x4 (x1 {x5} {x6}) = (Bool.false, Bool.true); have x5 : Bool → Bool × Bool → Bool × Bool := fun (x5 : Bool) (x6 : Bool × Bool) => if x5 = Bool.true then x6.swap else x6; ∀ (x6 : (Fin (26 : ℕ) → Bool) → Bool × Bool),   x2 x6 →     x3 x6 (Bool.true, Bool.false) →       x3 x6 (Bool.false, Bool.true) →         ∃ (x10 : Equiv.Perm (Fin (26 : ℕ))) (x11 : Bool),           have x12 : (Fin (26 : ℕ) → Bool) → Bool × Bool := fun (x12 : Fin (26 : ℕ) → Bool) => x5 x11 (x6 (x12 ∘ ⇑x10));           x2 x12 ∧ x4 x12) := by
  exact PEqualNP.Outside.L_meta_17651_aux.normal_child
