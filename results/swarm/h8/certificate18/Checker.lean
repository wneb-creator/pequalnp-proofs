import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18

open PEqualNP.Outside.L_meta_6581

abbrev Word := Extended.Sig

def Impossible (target : Word) (cap : Nat) (ws : List Word) : Prop :=
  ∀ k, k ≤ cap → ¬ Extended.Live true target k ws.toFinset

lemma live_width {target : Word} {k : Nat} {S : Finset Word}
    (h : Extended.Live true target k S) : S.card ≤ k + 1 := by
  induction h using Extended.Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : Extended.bin d a b ∉ U := fun hm =>
      hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

lemma live_proper {target : Word} {k : Nat} {S : Finset Word}
    (h : Extended.Live true target k S) : ∀ a ∈ S, Extended.proper a := by
  induction h using Extended.Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf tail ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a hm => ih a (Finset.mem_insert_of_mem hm)⟩

def child (ws : List Word) (a b : Word) (d : Nat) (ka kb : Bool) : List Word :=
  Extended.bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

lemma erase_fin {ws : List Word} (h : ws.Nodup) (a : Word) :
    (ws.erase a).toFinset = ws.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

lemma kept_fin_word (k : Bool) (a : Word) (ws : List Word) :
    (kept k a ws).toFinset = if k then insert a ws.toFinset else ws.toFinset := by
  cases k <;> simp [kept]

lemma enum_step {target : Word} {cap : Nat} {ws : List Word}
    (hn : ws.Nodup) (out : target ∉ ws)
    (branches : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb,
      a ≠ b → Extended.bin d a b ∉ ws → Extended.proper (Extended.bin d a b) →
      (child ws a b d ka kb).length ≤ cap →
      Impossible target (cap - 1) (child ws a b d ka kb)) :
    Impossible target cap ws := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Extended.Live.ind with
  | stop hp =>
    have mem : target ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have am : a ∈ ws := List.mem_toFinset.mp
      (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp
      (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : Extended.bin d a b ∉ ws := fun hm =>
      hf (he ▸ List.mem_toFinset.mpr hm)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b by rfl, erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin_word, kept_fin_word, er, he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun hm => hn.not_mem_erase (List.mem_of_mem_erase hm)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have nd : (child ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, kept_nd ka a _ nk ax⟩
      intro hm
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (ke ▸ List.mem_toFinset.mpr hm)))
    have eq : (child ws a b d ka kb).toFinset = insert (Extended.bin d a b) U := by
      change (Extended.bin d a b :: kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_width tail
    have len : (child ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup nd, eq]
      omega
    have op : d < 4 := by rcases hd with hd | ⟨_, hd⟩ <;> omega
    exact branches a am b bm d op ka kb hab fresh hz len k (by omega)
      (eq.symm ▸ tail)

abbrev Choice := Nat × Word × Word

def gateCheck (oracle : Nat → List Word → Choice → Bool) (cap : Nat) (ws : List Word)
    (a b : Word) (d : Nat) (ka kb : Bool) : Bool :=
  let z := Extended.bin d a b
  if a == b then true else
  if z == Extended.zero then true else
  if z == Extended.one then true else
  if ws.contains z then true else
  if cap < (child ws a b d ka kb).length then true else
  oracle (cap - 1) (child ws a b d ka kb) (d,a,b)

def pairCheck (oracle : Nat → List Word → Choice → Bool) (cap : Nat) (ws : List Word)
    (a b : Word) : Bool :=
  (List.range 4).all fun d =>
    [false, true].all fun ka =>
      [false, true].all fun kb => gateCheck oracle cap ws a b d ka kb

def nodeCheck (target : Word) (oracle : Nat → List Word → Choice → Bool)
    (cap : Nat) (ws : List Word) : Bool :=
  decide ws.Nodup && !(ws.contains target) &&
    ws.all (fun a => ws.all (fun b => pairCheck oracle cap ws a b))

lemma nodeCheck_sound {target : Word} {oracle : Nat → List Word → Choice → Bool}
    {cap : Nat} {ws : List Word}
    (oracle_sound : ∀ k xs op, oracle k xs op = true → Impossible target k xs)
    (checked : nodeCheck target oracle cap ws = true) : Impossible target cap ws := by
  simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem] at checked
  have out : target ∉ ws := by
    intro ht
    simpa [ht] using checked.1.2
  apply enum_step checked.1.1 out
  intro a ha b hb d hd ka kb hab fresh hz len
  have pair := List.all_eq_true.mp (List.all_eq_true.mp checked.2 a ha) b hb
  have op := List.all_eq_true.mp pair d (List.mem_range.mpr hd)
  have keepa := List.all_eq_true.mp op ka (by cases ka <;> simp)
  have keepb := List.all_eq_true.mp keepa kb (by cases kb <;> simp)
  apply oracle_sound
  simpa [gateCheck, hab, hz.1, hz.2, List.contains_eq_mem, fresh,
    Nat.not_lt.mpr len] using keepb

def collisionCheck (target : Word) (r s : Extended.Row) (ws : List Word) : Bool :=
  (Extended.bit r target != Extended.bit s target) &&
    ws.all (fun w => Extended.bit r w == Extended.bit s w)

lemma collisionCheck_sound {target : Word} {r s : Extended.Row} {ws : List Word}
    (checked : collisionCheck target r s ws = true) (cap : Nat) :
    Impossible target cap ws := by
  simp only [collisionCheck, Bool.and_eq_true, bne_iff_ne, List.all_eq_true,
    beq_iff_eq] at checked
  intro k hk run
  obtain ⟨w, hw, different⟩ := Extended.live_row_difference run checked.1
  exact different (checked.2 w (List.mem_toFinset.mp hw))

lemma forest_sound {target : Word} {n : Nat}
    (state : Fin n → List Word) (budget : Fin n → Nat)
    (oracle : Fin n → Nat → List Word → Choice → Bool)
    (sound : ∀ i, (∀ j, budget j < budget i → Impossible target (budget j) (state j)) →
      ∀ k ws op, oracle i k ws op = true → Impossible target k ws)
    (checked : ∀ i, nodeCheck target (oracle i) (budget i) (state i) = true) :
    ∀ i, Impossible target (budget i) (state i) := by
  have go : ∀ b i, budget i = b → Impossible target (budget i) (state i) := by
    intro b
    induction b using Nat.strong_induction_on with
    | ind b ih =>
      intro i hi
      apply nodeCheck_sound (sound i ?_) (checked i)
      intro j hj
      exact ih (budget j) (by omega) j rfl
  intro i
  exact go (budget i) i rfl

structure State where
  live : List Word
  paidPrefix : List Choice

def unpack (codes i : Nat) : Nat := (codes >>> (32*i)) &&& 0xffffffff

def applyCode (st : State) (code : Nat) : State :=
  let ai := code &&& 31
  let bi := (code >>> 5) &&& 31
  let op := (code >>> 10) &&& 3
  let ka := code.testBit 12
  let kb := code.testBit 13
  let pos := (code >>> 14) &&& 31
  let a := st.live.getD ai Extended.zero
  let b := st.live.getD bi Extended.zero
  let rest := (st.live.zipIdx.filter fun (_,i) =>
    (i != ai || ka) && (i != bi || kb)).map Prod.fst
  let z := Extended.bin op a b
  ⟨rest.take pos ++ z :: rest.drop pos, st.paidPrefix ++ [(op,a,b)]⟩

def decodeState (codes : Nat) : Nat → Nat → State
  | 0, _ => ⟨Extended.initial, []⟩
  | fuel+1, i => if i=0 then ⟨Extended.initial, []⟩ else
      let code := unpack codes i
      applyCode (decodeState codes fuel (code >>> 19)) code

namespace Projection

def Impossible (u : Bool) (T : Word) (cap : Nat) (S : Finset Word) : Prop :=
  ∀ k, k ≤ cap → ¬ Extended.Live u T k S

lemma bit_zero (r : Extended.Row) : Extended.bit r Extended.zero = false := by
  simp [Extended.bit, Extended.zero]

def Slice (u : Bool) (raw : List Word) (T d : Word) (L : Nat) : Prop :=
  ∃ (f : Row → Extended.Row) (roots : List (Wire Row)), (∀ r, Extended.bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u roots (restrictRows f (Extended.observe a))) ∧
    ¬Constant (restrictRows f (Extended.observe T)) ∧
    ∀ p bank, Reach u roots p bank → Available u bank (restrictRows f (Extended.observe T)) → L ≤ p

def masked (d a : Word) := a &&& d
def availableB (u : Bool) (d : Word) (pool : List Word) (a : Word) :=
  let m := masked d a
  m == Extended.zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (Extended.neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Extended.Row} {d a b : Word} (dom : ∀ r, Extended.bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (Extended.observe a) = restrictRows f (Extended.observe b) := by
  funext r
  have h := congrArg (Extended.bit (f r)) eq
  change Extended.bit (f r) a = Extended.bit (f r) b
  simpa only [Extended.bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Extended.Row} {d a : Word} (dom : ∀ r, Extended.bit (f r) d = true)
    (eq : masked d a = Extended.zero) : restrictRows f (Extended.observe a) = fun _ => false := by
  funext r
  have he := congrArg (Extended.bit (f r)) eq
  change Extended.bit (f r) a = false
  rw [bit_zero] at he
  simpa only [Extended.bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Extended.Row} {d a : Word} (dom : ∀ r, Extended.bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (Extended.observe a) = fun _ => true := by
  funext r
  have he := congrArg (Extended.bit (f r)) eq
  change Extended.bit (f r) a = true
  rw [dom r] at he
  simpa only [Extended.bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Extended.Row) (bank : List (Wire Row)) (pool : List Word) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (Extended.observe a))

theorem availableB_sound {u} {f : Row → Extended.Row} {d a : Word} {bank pool}
    (dom : ∀ r, Extended.bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (Extended.observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [Extended.obs_neg] at h
    have e : inv (restrictRows f (inv (Extended.observe a))) = restrictRows f (Extended.observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Word × Word
def choiceVal (c : Choice) := Extended.bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Word) (pool : List Word) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Extended.Row} {d : Word} {roots bank pool q}
    (dom : ∀ r, Extended.bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,Extended.obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Word) (pool : List Word) : List Choice → Option (List Word)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Word} {f : Row → Extended.Row} (dom : ∀ r, Extended.bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Word) := masked d a == Extended.zero || masked d a == d
theorem count_constants {d : Word} {f : Row → Extended.Row} (dom : ∀ r, Extended.bit (f r) d = true)
    (ws : List Word) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map Extended.observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (Extended.observe a)) := by
        have hh : masked d a = Extended.zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih


abbrev BoundPool := Word × Nat × Nat × List Word
def BoundPool.domain (c : BoundPool) : Word := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Word := c.2.2.2

def ValidPool (u : Bool) (raw : List Word) (T : Word) (c : BoundPool) :=
  ∃ (f : Row → Extended.Row) (roots : List (Wire Row)) (bank : List (Wire Row)),
    (∀ r, Extended.bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (Extended.observe T)) ∧
    (∀ q ws, Reach u roots q ws → Available u ws (restrictRows f (Extended.observe T)) → c.bound ≤ q) ∧
    Reach u roots c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Word)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u roots n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map Extended.observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (Extended.list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (Extended.observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Word) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Word) (cs : List Choice) (d : Word) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


def cutCheck (c : BoundPool) (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  match ws with
  | [] => false
  | z::rest => (z == choiceVal op) && decide ws.Nodup && scalarPoolCut true c k rest op

lemma cutCheck_sound {raw T c k ws op} (valid : ValidPool true raw T c)
    (checked : cutCheck c k ws op = true) :
    Cert18.Impossible T k ws := by
  cases ws with
  | nil => simp [cutCheck] at checked
  | cons z rest =>
    simp only [cutCheck,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at checked
    obtain ⟨⟨rfl,nd⟩,cut⟩ := checked
    exact scalarPoolCut_sound valid nd cut

end Projection

namespace Automorphism
abbrev Word := Extended.Sig

set_option maxRecDepth 4096 in
lemma bit_zero (i : Extended.Row) : Extended.bit i Extended.zero = false := by
  simp [Extended.bit,Extended.zero]
set_option maxRecDepth 4096 in
lemma bit_one (i : Extended.Row) : Extended.bit i Extended.one = true := by
  unfold Extended.bit Extended.one
  rw [BitVec.getLsbD_allOnes]
  simp
set_option maxRecDepth 4096 in
lemma bit_bin (i : Extended.Row) (d : Nat) (a b : Word) : Extended.bit i (Extended.bin d a b) =
    (if d=0 then Extended.bit i a && Extended.bit i b else if d=1 then Extended.bit i a || Extended.bit i b else
      if d=2 then Extended.bit i a && !(Extended.bit i b) else !(Extended.bit i a) && Extended.bit i b) := by
  unfold Extended.bin
  split_ifs <;> simp [Extended.bit]

set_option maxRecDepth 4096 in
def rename (f : Extended.Row → Extended.Row) (a : Word) := Extended.table fun r => Extended.bit (f r) a
set_option maxRecDepth 4096 in
lemma bit_rename (f : Extended.Row → Extended.Row) (a : Word) (r : Extended.Row) :
    Extended.bit r (rename f a) = Extended.bit (f r) a := Extended.bit_table _ _
set_option maxRecDepth 4096 in
lemma observe_rename (f : Extended.Row → Extended.Row) (a : Word) :
    Extended.observe (rename f a) = restrictRows f (Extended.observe a) := by funext r; exact bit_rename f a r
set_option maxRecDepth 4096 in
lemma rename_bin (f : Extended.Row → Extended.Row) (d : Nat) (a b : Word) :
    rename f (Extended.bin d a b) = Extended.bin d (rename f a) (rename f b) := by
  apply Extended.bit_ext
  intro r
  simp only [bit_rename,bit_bin]

set_option maxRecDepth 4096 in
lemma rename_inj (f : Extended.Row → Extended.Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (Extended.bit r) h
  change Extended.bit ⟨j,hj⟩ a = Extended.bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
set_option maxRecDepth 4096 in
lemma rename_constants (f : Extended.Row → Extended.Row) : rename f Extended.zero = Extended.zero ∧ rename f Extended.one = Extended.one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f Extended.zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f Extended.one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
set_option maxRecDepth 4096 in
lemma live_rename {u T k S} (h : Extended.Live u T k S) (f : Extended.Row → Extended.Row) (onto : Function.Surjective f) :
    Extended.Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : Extended.proper v) : Extended.proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Extended.Live.ind with
  | stop hp => simpa using Extended.Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (Extended.bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Extended.Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

abbrev Move := Word × Word × Extended.Row
set_option maxRecDepth 4096 in
def shifted (d r : Extended.Row) : Extended.Row :=
  if h : r.val < 1024-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(1024-d.val),by omega⟩
set_option maxRecDepth 4096 in
def backwards (d : Extended.Row) : Extended.Row := Fin.ofNat 1024 (1024-d.val)
set_option maxRecDepth 4096 in
def rowMove (m : Move) (r : Extended.Row) : Extended.Row :=
  if Extended.bit r m.1 then shifted m.2.2 r else if Extended.bit r m.2.1 then shifted (backwards m.2.2) r else r
set_option maxRecDepth 4096 in
def mux (m a b : Word) := (m &&& a) ||| (~~~m &&& b)
set_option maxRecDepth 4096 in
def wordMove (m : Move) (a : Word) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

set_option maxRecDepth 4096 in
lemma bit_shift (d r : Extended.Row) (a : Word) : Extended.bit r (a.rotateRight d.val) = Extended.bit (shifted d r) a := by
  unfold Extended.bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 1024-d.val <;> simp [shifted,h,r.isLt]

set_option maxRecDepth 4096 in
lemma bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

set_option maxRecDepth 4096 in
lemma bit_mux (r : Extended.Row) (m a b : Word) :
    Extended.bit r (mux m a b) = if Extended.bit r m then Extended.bit r a else Extended.bit r b := by
  simp only [Extended.bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

set_option maxRecDepth 4096 in
lemma bit_move (r : Extended.Row) (m : Move) (a : Word) : Extended.bit r (wordMove m a) = Extended.bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases Extended.bit r m.1 <;> cases Extended.bit r m.2.1 <;> rfl

set_option maxRecDepth 4096 in
def movedRow (ms : List Move) (r : Extended.Row) := ms.foldl (fun j m => rowMove m j) r
set_option maxRecDepth 4096 in
def movedWord (ms : List Move) (a : Word) := ms.foldr wordMove a
set_option maxRecDepth 4096 in
lemma bit_moved (ms : List Move) (a : Word) (r : Extended.Row) :
    Extended.bit r (movedWord ms a) = Extended.bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
set_option maxRecDepth 4096 in
lemma moved_eq_rename (ms : List Move) (a : Word) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm


set_option maxRecDepth 4096 in
def coordinate (j : Fin 10) : Word := Extended.table fun r => r.val.testBit j.val
set_option maxRecDepth 4096 in
def coordinates : List Word := List.ofFn coordinate
set_option maxRecDepth 4096 in
lemma bit_coordinate (j : Fin 10) (r : Extended.Row) :
    Extended.bit r (coordinate j) = r.val.testBit j.val := Extended.bit_table _ _

set_option maxRecDepth 4096 in
lemma agree_coordinates (r s : Extended.Row)
    (h : ∀ a ∈ coordinates, Extended.bit r a = Extended.bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<10
  · let i : Fin 10 := ⟨j,hj⟩
    have hm : coordinate i ∈ coordinates := List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (bit_coordinate i r).symm.trans ((h _ hm).trans (bit_coordinate i s))
  · have le : 1024 ≤ 2^j := by
      change 2^10 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

set_option maxRecDepth 4096 in
def composedOK (p q : List Move) := coordinates.all (fun a => movedWord p (movedWord q a) == a)
set_option maxRecDepth 4096 in
lemma composed_id {p q} (h : composedOK p q = true) (r : Extended.Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_coordinates
  intro a ha
  rw [←bit_moved,←bit_moved]
  exact congrArg (Extended.bit r) (beq_iff_eq.mp (List.all_eq_true.mp h a ha))

set_option maxRecDepth 4096 in
def autoOK (target : Word) (p : List Move) :=
  movedWord p target == target && composedOK p p.reverse && composedOK p.reverse p

set_option maxRecDepth 4096 in
lemma live_moved {u target k S} (h : Extended.Live u target k S)
    (p : List Move) (ok : autoOK target p = true) :
    Extended.Live u target k (S.image (movedWord p)) := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) :=
    fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  have run := live_rename h (movedRow p) onto
  have he : rename (movedRow p) target = target := (moved_eq_rename p target).symm.trans ok.1.1
  rw [he] at run
  have funEq : rename (movedRow p) = movedWord p := funext fun a => (moved_eq_rename p a).symm
  rw [funEq] at run
  exact run

set_option maxRecDepth 4096 in
def linkCheck (p : List Move) (ws childws : List Word) : Bool :=
  decide ((ws.map (movedWord p)).toFinset = childws.toFinset)

set_option maxRecDepth 4096 in
lemma impossible_link {target : Word} {cap : Nat} {ws childws : List Word}
    (p : List Move) (ok : autoOK target p = true) (link : linkCheck p ws childws = true)
    (ih : ∀ k, k ≤ cap → ¬Extended.Live true target k childws.toFinset) :
    ∀ k, k ≤ cap → ¬Extended.Live true target k ws.toFinset := by
  intro k hk live
  have run := live_moved live p ok
  have he : (ws.map (movedWord p)).toFinset = childws.toFinset := of_decide_eq_true link
  have im : ws.toFinset.image (movedWord p) = (ws.map (movedWord p)).toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
  have he' := im.trans he
  rw [he'] at run
  exact ih k hk run

set_option maxRecDepth 4096 in
def swapMove (i j : Fin 10) : Move :=
  let lo := if i.val ≤ j.val then i else j
  let hi := if i.val ≤ j.val then j else i
  (coordinate lo &&& ~~~coordinate hi, coordinate hi &&& ~~~coordinate lo,
    Fin.ofNat 1024 (2^hi.val-2^lo.val))
set_option maxRecDepth 4096 in
def swapWords (swaps : List (Fin 10 × Fin 10)) : List Move :=
  swaps.map fun s => swapMove s.1 s.2

end Automorphism

namespace Cofactor

def positions (v : Fin 10) : List Nat :=
  match v.val with
  | 0 => [5, 8, 3, 2, 7, 0, 6, 4, 1]
  | 1 => [8, 6, 1, 0, 5, 3, 9, 2, 4]
  | 2 => [9, 6, 1, 2, 7, 4, 8, 0, 3]
  | 3 => [9, 7, 2, 1, 6, 4, 5, 3, 0]
  | 4 => [7, 5, 0, 4, 9, 2, 8, 1, 3]
  | 5 => [7, 5, 8, 6, 9, 2, 0, 3, 1]
  | 6 => [9, 6, 8, 5, 7, 4, 1, 3, 0]
  | 7 => [9, 7, 2, 3, 4, 6, 5, 1, 8]
  | 8 => [9, 7, 5, 0, 4, 6, 2, 8, 1]
  | 9 => [9, 7, 5, 8, 6, 4, 2, 0, 3]
  | _ => []

def inputIndex (v i : Fin 10) : Nat :=
  (match v.val with
  | 0 => [9, 4, 0, 1, 6, 7, 3, 5, 2, 8]
  | 1 => [6, 9, 4, 0, 1, 8, 7, 3, 5, 2]
  | 2 => [0, 4, 9, 6, 1, 5, 3, 7, 8, 2]
  | 3 => [0, 1, 6, 9, 4, 5, 2, 8, 7, 3]
  | 4 => [4, 0, 1, 6, 9, 3, 5, 2, 8, 7]
  | 5 => [4, 0, 1, 2, 3, 9, 5, 6, 7, 8]
  | 6 => [0, 4, 3, 2, 1, 5, 9, 8, 7, 6]
  | 7 => [0, 1, 6, 8, 5, 4, 2, 9, 3, 7]
  | 8 => [0, 1, 2, 7, 5, 4, 6, 3, 9, 8]
  | 9 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | _ => []).getD i.val 9

def embedAt (v : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 ((positions v).zipIdx.foldl
    (fun n (p,i) => n ||| (((r.val >>> i) &&& 1) <<< p)) 0)

def rowBack (v : Fin 10) (r : Extended.Row) : Row :=
  Fin.ofNat 512 ((positions v).zipIdx.foldl
    (fun n (p,i) => n ||| (((r.val >>> p) &&& 1) <<< i)) 0)

def cofactorSwaps (v : Fin 10) : List (Fin 10 × Fin 10) :=
  ([[(0,5),(1,8),(2,3),(4,7)],[(0,8),(1,6),(2,6),(3,8),(4,5),(5,8),(6,9),(7,9)],[(0,9),(1,6),(2,6),(3,6),(4,7),(5,7),(6,8),(7,9)],[(0,9),(1,7),(3,7),(4,6),(5,6),(8,9)],[(0,7),(1,5),(2,7),(3,4),(4,9),(5,7),(6,8),(8,9)],[(0,7),(1,5),(2,8),(3,6),(4,9),(5,8),(6,7)],[(0,9),(1,6),(2,8),(3,5),(4,7),(5,7),(8,9)],[(0,9),(1,7),(5,6)],[(0,9),(1,7),(2,5),(3,9),(5,6),(7,8)],[(0,9),(1,7),(2,5),(3,8),(4,6),(5,6),(7,9)]] : List (List (Fin 10 × Fin 10))).getD v.val []

def baseRow (r : Extended.Row) : Row := Fin.ofNat 512 r.val
def doubleWord (a : Sig) : Word := a ++ a
set_option maxRecDepth 4096 in
lemma bit_doubleWord (r : Extended.Row) (a : Sig) :
    Extended.bit r (doubleWord a) = bit (baseRow r) a := by
  change (a ++ a).getLsbD r.val = a.getLsbD (r.val % 512)
  rw [BitVec.getLsbD_append]
  by_cases h : r.val < 512
  · rw [ite_eq_left h,Nat.mod_eq_of_lt h]
  · rw [ite_eq_right h]
    congr 1
    omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma row_permutation : ∀ (v : Fin 10) (r : Extended.Row),
    baseRow (Automorphism.movedRow (Automorphism.swapWords (cofactorSwaps v)) r) = rowBack v r := by
  decide +kernel

def fastLiftWord (v : Fin 10) (a : Sig) : Word :=
  Automorphism.movedWord (Automorphism.swapWords (cofactorSwaps v)) (doubleWord a)

set_option maxRecDepth 4096 in
lemma bit_fastLiftWord (v : Fin 10) (a : Sig) (r : Extended.Row) :
    Extended.bit r (fastLiftWord v a) = bit (rowBack v r) a := by
  rw [fastLiftWord,Automorphism.bit_moved,bit_doubleWord,row_permutation]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma row_roundtrip : ∀ (v : Fin 10) (r : Row), rowBack v (embedAt v r) = r := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma target_rows : ∀ (v : Fin 10) (r : Row),
    Extended.bit (embedAt v r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma pin_rows : ∀ (v i : Fin 10) (r : Row),
    Extended.bit (embedAt v r) (Extended.pins.getD i.val Extended.zero) =
      bit r (inputs.getD (inputIndex v i) zero) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma pin_vanishes : ∀ (v : Fin 10) (r : Row),
    Extended.bit (embedAt v r) (Extended.pins.getD v.val Extended.zero) = false := by
  decide +kernel

lemma target_embedding (v : Fin 10) :
    restrictRows (embedAt v) (Extended.observe Extended.target) = observe graph := by
  funext r
  exact target_rows v r

lemma pin_projection (v i : Fin 10) :
    restrictRows (embedAt v) (Extended.observe (Extended.pins.getD i.val Extended.zero)) =
      observe (inputs.getD (inputIndex v i) zero) := by
  funext r
  exact pin_rows v i r

def liftWord (v : Fin 10) (a : Sig) : Word :=
  fastLiftWord v a

def liftDomain (v : Fin 10) (a : Sig) : Word :=
  liftWord v a &&& ~~~(Extended.pins.getD v.val Extended.zero)

lemma domain_embedding (v : Fin 10) (a : Sig) (r : Row) :
    Extended.bit (embedAt v r) (liftDomain v a) = bit r a := by
  have e := bit_fastLiftWord v a (embedAt v r)
  have h := pin_vanishes v r
  simp only [liftDomain, Extended.bit, BitVec.getLsbD_and, BitVec.getLsbD_not,
    (embedAt v r).isLt, decide_true, Bool.true_and]
  change (Extended.bit (embedAt v r) (liftWord v a) &&
    !(Extended.bit (embedAt v r) (Extended.pins.getD v.val Extended.zero))) = bit r a
  rw [h, show Extended.bit (embedAt v r) (liftWord v a) = bit r a from
    e.trans (congrArg (fun r => bit r a) (row_roundtrip v r))]
  simp

lemma pin_mem (a : Word) : a ∈ Extended.initial ↔
    ∃ i : Fin 10, Extended.pins.getD i.val Extended.zero = a := by
  have e : List.ofFn (fun i : Fin 10 => Extended.pins.getD i.val Extended.zero) =
      Extended.initial := by decide +kernel
  rw [←e, List.mem_ofFn]

lemma restricted_input {f : Row → Row} {roots : List (Wire Row)}
    (sup : ∀ a ∈ inputs, Available true roots (restrictRows f (observe a)))
    (n : Nat) : Available true roots (restrictRows f (observe (inputs.getD n zero))) := by
  simp only [List.getD_eq_getElem?_getD]
  cases he : inputs[n]? with
  | none =>
    simp only [Option.getD_none]
    exact Or.inr (Or.inl ⟨false, by funext r; simp [restrictRows,observe,bit,zero]⟩)
  | some a =>
    simp only [Option.getD_some]
    exact sup a (List.mem_of_getElem? he)

lemma lift_slice (v : Fin 10) {d : Sig} {L : Nat}
    (slice : PEqualNP.Outside.L_meta_6581.Slice true inputs graph d L) :
    Projection.Slice true Extended.initial Extended.target (liftDomain v d) L := by
  obtain ⟨f,roots,dom,sup,nc,lo⟩ := slice
  refine ⟨(embedAt v) ∘ f, roots.map observe, ?_, ?_, ?_, ?_⟩
  · intro r
    exact (domain_embedding v d (f r)).trans (dom r)
  · intro a ha
    obtain ⟨i,rfl⟩ := (pin_mem a).mp ha
    have e : restrictRows ((embedAt v) ∘ f)
        (Extended.observe (Extended.pins.getD i.val Extended.zero)) =
        restrictRows f (observe (inputs.getD (inputIndex v i) zero)) := by
      funext r
      exact pin_rows v i (f r)
    rw [e]
    exact restricted_input sup _
  · have e : restrictRows ((embedAt v) ∘ f) (Extended.observe Extended.target) =
        restrictRows f (observe graph) := by
      funext r
      exact target_rows v (f r)
    rwa [e]
  · have e : restrictRows ((embedAt v) ∘ f) (Extended.observe Extended.target) =
        restrictRows f (observe graph) := by
      funext r
      exact target_rows v (f r)
    rwa [e]

end Cofactor

namespace Cofactor

def column (i : Fin 215) : ColumnInfo := rootSCols.getD i.val (0,0,0,0,0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
lemma column_mem : ∀ i : Fin 215, column i ∈ rootSCols := by
  decide +kernel

lemma column_checked (i : Fin 215) :
    colCheck 511 (column i) (boundsBefore known383) = true := by
  have h := rootSGeom
  simp only [graphValid,Bool.and_eq_true] at h
  have all : rootSCols.all (fun c => colCheck 511 c (boundsBefore known383)) = true := h.1.2
  exact List.all_eq_true.mp all (column i) (column_mem i)

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
lemma column_raw : ∀ i : Fin 215, varsX (rawMask 511 (column i)) = inputs := by
  decide +kernel

lemma column_slice (v : Fin 10) (i : Fin 215) :
    Projection.Slice true Extended.initial Extended.target
      (liftDomain v (subcube (column i).1 (column i).2.1)) (column i).2.2.2.2 := by
  apply lift_slice
  have h := col_sound (u:=true) (m:=511) (column i) (boundsBefore known383)
    (before_sound known383 valid383) (column_checked i)
  rw [column_raw] at h
  have eq : chartGoal 511 = graph := by decide +kernel
  rwa [eq] at h

lemma whole_slice (v : Fin 10) :
    Projection.Slice true Extended.initial Extended.target (liftDomain v one) 15 := by
  apply lift_slice
  refine ⟨id, inputs, ?_, ?_, ?_, ?_⟩
  · intro r
    unfold bit one
    rw [BitVec.getLsbD_allOnes]
    simp [r.isLt]
  · intro a ha
    exact Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩)
  · intro hc
    obtain ⟨b,hb⟩ := hc
    have h0 := congrFun hb (0 : Row)
    have h1 := congrFun hb (3 : Row)
    have e0 : restrictRows id (observe graph) (0 : Row) = false := by decide +kernel
    have e1 : restrictRows id (observe graph) (3 : Row) = true := by decide +kernel
    rw [e0] at h0
    rw [e1] at h1
    cases h0.trans h1.symm
  · exact nineFloor

end Cofactor


namespace Cofactor

def source (v : Fin 10) (j : Fin 216) : Word × Nat :=
  if h : j.val < 215 then
    let c := column ⟨j.val,h⟩
    (liftDomain v (subcube c.1 c.2.1), c.2.2.2.2)
  else (liftDomain v one, 15)

lemma source_sound (v : Fin 10) (j : Fin 216) :
    Projection.Slice true Extended.initial Extended.target (source v j).1 (source v j).2 := by
  unfold source
  split
  · exact column_slice _ _
  · exact whole_slice _

end Cofactor

abbrev PoolHint := (Fin 10 × Fin 216) × Nat

def selectedPrefix (st : State) (mask : Nat) : List Choice :=
  (st.paidPrefix.zipIdx.filter fun (_,i) => mask.testBit i).map Prod.fst

def hintPool (st : State) (h : PoolHint) : Option Projection.BoundPool :=
  let source := Cofactor.source h.1.1 h.1.2
  Projection.materialize true Extended.initial (selectedPrefix st h.2) source.1 source.2

lemma hintPool_sound {st h c} (built : hintPool st h = some c) :
    Projection.ValidPool true Extended.initial Extended.target c := by
  exact Projection.materialize_sound (Cofactor.source_sound h.1.1 h.1.2) built

def poolList (st : State) (hs : List PoolHint) : List Projection.BoundPool :=
  hs.filterMap (hintPool st)

lemma poolList_sound {st hs c} (hc : c ∈ poolList st hs) :
    Projection.ValidPool true Extended.initial Extended.target c := by
  obtain ⟨h,hm,built⟩ := List.mem_filterMap.mp hc
  exact hintPool_sound built

abbrev Pair := Extended.Row × Extended.Row

def profilePairs (ws : List Word) (pairs : List Pair) : List Pair :=
  pairs.filter fun p => decide ((ws.countP fun a =>
    Extended.bit p.1 a != Extended.bit p.2 a) ≤ 2)

abbrev Link (n : Nat) := Fin n × List Automorphism.Move

def replayOracle {n : Nat} (states : Fin n → State) (budget : Fin n → Nat)
    (i : Fin n) (pools : List Projection.BoundPool) (pairs : List Pair)
    (links : List (Link n)) (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  pairs.any (fun p => collisionCheck Extended.target p.1 p.2 ws) ||
  pools.any (fun c => Projection.cutCheck c k ws op) ||
  links.any (fun l => decide (k ≤ budget l.1 ∧ budget l.1 < budget i) &&
    Automorphism.linkCheck l.2 ws (states l.1).live)

lemma replayOracle_sound {n : Nat} {states : Fin n → State} {budget : Fin n → Nat}
    {i : Fin n} {pools : List Projection.BoundPool} {pairs : List Pair}
    {links : List (Link n)}
    (pool_ok : ∀ c ∈ pools, Projection.ValidPool true Extended.initial Extended.target c)
    (links_ok : ∀ l ∈ links, Automorphism.autoOK Extended.target l.2 = true)
    (earlier : ∀ j, budget j < budget i → Impossible Extended.target (budget j) (states j).live)
    {k ws op} (checked : replayOracle states budget i pools pairs links k ws op = true) :
    Impossible Extended.target k ws := by
  simp only [replayOracle,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true,
    decide_eq_true_eq] at checked
  rcases checked with (⟨p,hp,cut⟩ | ⟨c,hc,cut⟩) | ⟨l,hl,⟨kb,lt⟩,link⟩
  · exact collisionCheck_sound cut k
  · exact Projection.cutCheck_sound (pool_ok c hc) cut
  · intro j hj run
    exact Automorphism.impossible_link l.2 (links_ok l hl) link (earlier l.1 lt) j
      (hj.trans kb) run


end PEqualNP.Outside.L_meta_2373_aux.Cert18
