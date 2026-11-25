import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4413

/- With the two supplied disjunctions, each of the eight input banks needs at least
fourteen binary gates in the monotone case and thirteen when wire complements are free.
A circuit of length thirteen that uses a negation has at most twelve binary gates. -/

/- The bottom half holds thirteen copies of the sampled column. In the top
half each positive row is broadcast along one band. A shift aligns opposite
output labels for the separation test. -/
abbrev W := BitVec 1534

def ar (s : Bool) : Nat := if s then 4 else 2

def gate : Nat → W → W → W
  | 0, a, b => a &&& b
  | 1, a, b => a ||| b
  | 2, a, b => a &&& ~~~b
  | _, a, b => b &&& ~~~a

def bop {n : Nat} : Nat → BitVec n → BitVec n → BitVec n
  | 0,a,b => a &&& b
  | 1,a,b => a ||| b
  | 2,a,b => a &&& ~~~b
  | _,a,b => b &&& ~~~a

theorem gate_bop (j : Nat) (a b : W) : gate j a b = bop j a b := by
  rcases j with _ | _ | _ | j <;> rfl

theorem bop_append {m n} (j : Nat) (a b : BitVec m) (x y : BitVec n) :
    bop j (a ++ x) (b ++ y) = bop j a b ++ bop j x y := by
  rcases j with _ | _ | _ | j <;> simp [bop]

theorem bound_op {j : Nat} {s : Bool} (h : j < ar s) : j < 4 := by
  cases s <;> simp_all [ar] <;> omega

set_option maxRecDepth 10000 in
theorem idle (j : Nat) (a : W) :
    (gate j 0 a = 0 ∨ gate j 0 a = a) ∧
    (gate j a 0 = 0 ∨ gate j a 0 = a) ∧
    (gate j a a = 0 ∨ gate j a a = a) := by
  have id1 : a &&& ~~~(0 : W) = a := BitVec.and_allOnes
  rcases j with _ | _ | _ | j
  · exact ⟨Or.inl BitVec.zero_and,Or.inl BitVec.and_zero,Or.inr BitVec.and_self⟩
  · exact ⟨Or.inr BitVec.zero_or,Or.inr BitVec.or_zero,Or.inr BitVec.or_self⟩
  · exact ⟨Or.inl BitVec.zero_and,Or.inr id1,Or.inl (BitVec.and_not_self a)⟩
  · exact ⟨Or.inr id1,Or.inl BitVec.zero_and,Or.inl (BitVec.and_not_self a)⟩

theorem mask_gate (d : W) (j : Nat) (a b : W) :
    gate j a b &&& d = gate j (a &&& d) (b &&& d) := by
  rcases j with _ | _ | _ | j <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [gate, BitVec.getLsbD_not, hi] <;> grind

inductive Build (s : Bool) (roots : Finset W) : Nat → Finset W → Prop
  | start : Build s roots 0 (insert 0 roots)
  | step {p B a b} (prev : Build s roots p B) (ha : a ∈ B) (hb : b ∈ B)
      (j : Nat) (legal : j < ar s) : Build s roots (p+1) (insert (gate j a b) B)

theorem build_zero {s R p B} (h : Build s R p B) : (0 : W) ∈ B := by
  induction h with
  | start => simp
  | step _ _ _ _ _ ih => exact Finset.mem_insert_of_mem ih

def Low (s : Bool) (R : List W) (T : W) (n : Nat) : Prop :=
  ∀ p B, Build s R.toFinset p B → T ∈ B → n ≤ p

/- Read a circuit backwards from its output. Each live value is used later.
The set U records all other uses, including any repeated use of an operand. -/
inductive Plan (s : Bool) (T : W) : Nat → Finset W → Prop
  | stop (hT : T ≠ 0) : Plan s T 0 {T}
  | step {k U a b} (j : Nat) (legal : j < ar s) (ha : a ≠ 0) (hb : b ≠ 0) (ne : a ≠ b)
      (fresh : gate j a b ∉ insert a (insert b U))
      (tail : Plan s T k (insert (gate j a b) U)) : Plan s T (k+1) (insert a (insert b U))

theorem plan_nonzero {s T k S} (h : Plan s T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction h with
  | stop hp => simpa using hp
  | step j hj ha hb ne fresh _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem plan_size {s T k S} (h : Plan s T k S) : S.card ≤ k+1 := by
  induction h with
  | stop => simp
  | @step k U a b j _ _ _ _ fresh _ ih =>
    have hz : gate j a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hz] at ih
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega

theorem unwind {s R p B} (birth : Build s R p B) {T k S} (run : Plan s T k S) (sub : S ⊆ B) :
    ∃ h V, h ≤ k+p ∧ Plan s T h V ∧ V ⊆ R := by
  induction birth generalizing k S with
  | start =>
    refine ⟨k,S,by omega,run,?_⟩
    intro a ha
    exact (Finset.mem_insert.mp (sub ha)).resolve_left (plan_nonzero run a ha)
  | @step p B a b prev ha hb j hj ih =>
    let z := gate j a b
    by_cases used : z ∈ S
    · by_cases known : z ∈ B
      · have hs : S ⊆ B := by
          intro w hw
          exact (Finset.mem_insert.mp (sub hw)).elim (fun e => e ▸ known) id
        obtain ⟨h,V,q,rest,v⟩ := ih run hs
        exact ⟨h,V,by omega,rest,v⟩
      · have hz : z ≠ 0 := fun e => known (e ▸ build_zero prev)
        have az : a ≠ 0 := by
          rintro rfl
          exact (idle j b).1.elim hz (fun e => known (show gate j 0 b ∈ B from by rw [e]; exact hb))
        have bz : b ≠ 0 := by
          rintro rfl
          exact (idle j a).2.1.elim hz (fun e => known (show gate j a 0 ∈ B from by rw [e]; exact ha))
        have ab : a ≠ b := by
          rintro rfl
          exact (idle j a).2.2.elim hz (fun e => known (show gate j a a ∈ B from by rw [e]; exact ha))
        let U := S.erase z
        have small : U ⊆ B := by
          intro w hw
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hw
          exact (Finset.mem_insert.mp (sub mem)).resolve_left ne
        have next : Plan s T k (insert z U) := by simpa [U,Finset.insert_erase used] using run
        have full : insert a (insert b U) ⊆ B := Finset.insert_subset ha (Finset.insert_subset hb small)
        have pre := Plan.step j hj az bz ab (fun hm => known (full hm)) next
        obtain ⟨h,V,q,rest,v⟩ := ih pre full
        exact ⟨h,V,by omega,rest,v⟩
    · have hs : S ⊆ B := by
        intro w hw
        exact (Finset.mem_insert.mp (sub hw)).resolve_left (fun e => used (show gate j a b ∈ S from e ▸ hw))
      obtain ⟨h,V,q,rest,v⟩ := ih run hs
      exact ⟨h,V,by omega,rest,v⟩

def cost (d w : W) : Nat := if w &&& d = 0 then 1 else 0
def mass (d : W) (S : Finset W) := S.sum (cost d)

theorem mass_ins (d a : W) (S : Finset W) :
    mass d (insert a S) ≤ mass d S + cost d a := by
  by_cases h : a ∈ S
  · simp [Finset.insert_eq_of_mem h]
  · simp [mass, Finset.sum_insert h, Nat.add_comm]

/- Restricting the rows saves a gate for each live value that vanishes.
The first gate using it becomes a constant or a wire. The induction counts the
vanishing values only once when an operand has several uses. -/
theorem project {s T k S} (run : Plan s T k S) (d : W) {R p B}
    (born : Build s R p B) (supply : ∀ w ∈ S, w &&& d ∈ B) (nz : T &&& d ≠ 0) :
    ∃ q C, Build s R q C ∧ T &&& d ∈ C ∧ q + mass d S ≤ p+k := by
  induction run generalizing p B with
  | stop =>
    exact ⟨p,B,born,supply _ (by simp),by simp only [mass,Finset.sum_singleton,cost,if_neg nz,Nat.add_zero,Nat.le_refl]⟩
  | @step k U a b j legal ha hb ab fresh _ ih =>
    let z := gate j a b
    have hU : z ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have sm : mass d (insert z U) = mass d U + cost d z := by
      simp [mass,Finset.sum_insert hU,Nat.add_comm]
    have g1 := mass_ins d a (insert b U)
    have g2 := mass_ins d b U
    have ma := supply a (Finset.mem_insert_self _ _)
    have mb := supply b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have mu (w) (hw : w ∈ U) := supply w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    have op : z &&& d = gate j (a &&& d) (b &&& d) := mask_gate d j a b
    by_cases az : a &&& d = 0
    · have ze : z &&& d = 0 ∨ z &&& d = b &&& d := by
        rw [op,az]
        exact (idle j (b &&& d)).1
      have mz : z &&& d ∈ B := ze.elim (fun e => e ▸ build_zero born) (fun e => e ▸ mb)
      obtain ⟨q,C,hq,hm,le⟩ := ih born (by simpa only [Finset.forall_mem_insert] using And.intro mz mu)
      rw [sm] at le
      by_cases bz : b &&& d = 0
      · have zz : z &&& d = 0 := ze.elim id (fun e => e.trans bz)
        simp only [cost,if_pos az,if_pos bz,if_pos zz] at le g1 g2
        exact ⟨q,C,hq,hm,by omega⟩
      · simp only [cost,if_pos az,if_neg bz] at g1 g2
        exact ⟨q,C,hq,hm,by omega⟩
    · by_cases bz : b &&& d = 0
      · have ze : z &&& d = 0 ∨ z &&& d = a &&& d := by
          rw [op,bz]
          exact (idle j (a &&& d)).2.1
        have mz : z &&& d ∈ B := ze.elim (fun e => e ▸ build_zero born) (fun e => e ▸ ma)
        obtain ⟨q,C,hq,hm,le⟩ := ih born (by simpa only [Finset.forall_mem_insert] using And.intro mz mu)
        rw [sm] at le
        simp only [cost,if_neg az,if_pos bz] at g1 g2
        exact ⟨q,C,hq,hm,by omega⟩
      · let next := Build.step born ma mb j legal
        have sub : ∀ w ∈ insert z U, w &&& d ∈ insert (gate j (a &&& d) (b &&& d)) B := by
          simp only [Finset.forall_mem_insert]
          exact ⟨op ▸ Finset.mem_insert_self _ _,fun w h => Finset.mem_insert_of_mem (mu w h)⟩
        obtain ⟨q,C,hq,hm,le⟩ := ih next sub
        rw [sm] at le
        simp only [cost,if_neg az,if_neg bz] at g1 g2
        exact ⟨q,C,hq,hm,by omega⟩

def Bad (s : Bool) (T : W) (k : Nat) (ws : List W) : Prop :=
  ∀ n, n ≤ k → ¬Plan s T n ws.toFinset

theorem low_plan {s T R L k S} (lo : Low s R T L) (run : Plan s T k S) (sub : S ⊆ R.toFinset)
    (nz : T ≠ 0) : L ≤ k := by
  obtain ⟨q,C,born,mem,le⟩ := project run (BitVec.allOnes 1534) (R:=R.toFinset) Build.start
    (by intro w hw; rw [BitVec.and_allOnes]; exact Finset.mem_insert_of_mem (sub hw))
    (by rwa [BitVec.and_allOnes])
  rw [BitVec.and_allOnes] at mem
  have lb := lo q C born mem
  omega
/- At the cardinality bound, both operands of every gate have their last
use there. Any subadditive cost of the target is therefore bounded by the
sum of the costs of the current wires. -/
theorem tight_sum {s T k S} (run : Plan s T k S) (f : W → Nat)
    (sub : ∀ j, j < ar s → ∀ a b, f (gate j a b) ≤ f a + f b) :
    S.card ≤ k+1 ∧ (k+1 ≤ S.card → f T ≤ S.sum f) := by
  induction run with
  | stop => simp
  | @step n U a b j legal _ _ _ fresh tail ih =>
    have hz : gate j a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem hz] at ih
    have ha := Finset.card_insert_le a (insert b U)
    have hb := Finset.card_insert_le b U
    refine ⟨by omega,fun size => ?_⟩
    have na : a ∉ insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at size
      omega
    have nb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at size
      have cap := Finset.card_insert_le a U
      omega
    have weight := ih.2 (by omega)
    rw [Finset.sum_insert hz] at weight
    rw [Finset.sum_insert na,Finset.sum_insert nb]
    have add := sub j legal a b
    omega

def sample : (n : Nat) → Nat → W → BitVec n
  | 0,_,_ => 0
  | n+1,r,w => sample n (r/64) w ++ BitVec.ofBool (w.getLsbD (r % 64))

theorem extracted (j : Nat) (a b : W) (i : Nat) :
    BitVec.ofBool ((gate j a b).getLsbD i) =
    bop j (BitVec.ofBool (a.getLsbD i)) (BitVec.ofBool (b.getLsbD i)) := by
  rcases j with _ | _ | _ | j <;> by_cases hr : i < 1534 <;>
    cases x : a.getLsbD i <;> cases y : b.getLsbD i <;>
    simp_all [bop,gate,BitVec.getLsbD_not,BitVec.getLsbD_of_ge]

theorem sample_gate (n r j : Nat) (a b : W) :
    sample n r (gate j a b) = bop j (sample n r a) (sample n r b) := by
  induction n generalizing r with
  | zero => exact @Subsingleton.elim (BitVec 0) _ _ _
  | succ n ih => rw [sample,sample,sample,bop_append,ih,extracted]

def charge {n} (v : Nat) (a : BitVec n) := (v >>> (2*a.toNat)) % 4
/- Two bits per observed pattern. The three finite theorems below check
subadditivity on all pairs of patterns for each permitted gate. -/
def sixTab (s : Bool) : Nat :=
  if s then 0x2558bbbe6a9d7a6969ad76a9beee2558 else 0x448aaae044859590448559904480448
def fourTab : Nat := 0x14655914

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mono_six : ∀ j : Fin 2, ∀ a b : BitVec 6,
    charge (sixTab false) (bop j.val a b) ≤ charge (sixTab false) a + charge (sixTab false) b := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem signed_six : ∀ j : Fin 4, ∀ a b : BitVec 6,
    charge (sixTab true) (bop j.val a b) ≤ charge (sixTab true) a + charge (sixTab true) b := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem any_four : ∀ j : Fin 4, ∀ a b : BitVec 4,
    charge fourTab (bop j.val a b) ≤ charge fourTab a + charge fourTab b := by decide +kernel

def sampleCode : Nat → Nat → W → Nat
  | 0,_,_ => 0
  | n+1,r,w => sampleCode n (r/64) w <<< 1 ||| (w.getLsbD (r % 64)).toNat

theorem sampleCode_eq (n r : Nat) (w : W) : sampleCode n r w = (sample n r w).toNat := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp [sampleCode,sample,ih,BitVec.toNat_append,BitVec.toNat_ofBool]

def fee (s : Bool) (r : Nat) (w : W) : Nat :=
  if r < 68719476736 then (sixTab s >>> (2*sampleCode 6 r w)) % 4
  else (fourTab >>> (2*sampleCode 4 r w)) % 4

theorem fee_sub (s : Bool) (r j : Nat) (hj : j < ar s) (a b : W) :
    fee s r (gate j a b) ≤ fee s r a + fee s r b := by
  have old (v : W) : fee s r v = if r < 68719476736 then charge (sixTab s) (sample 6 r v)
      else charge fourTab (sample 4 r v) := by simp only [fee,charge,sampleCode_eq]
  simp only [old]
  split
  · rw [sample_gate]
    cases s
    · exact mono_six ⟨j,hj⟩ _ _
    · exact signed_six ⟨j,hj⟩ _ _
  · rw [sample_gate]
    exact any_four ⟨j,bound_op hj⟩ _ _

def heavy (s : Bool) (r : Nat) (T : W) (ws : List W) :=
  decide ((ws.map (fee s r)).sum < fee s r T)

theorem heavy_bad {ws : List W} {s T k r} (nd : ws.Nodup) (len : ws.length = k+1)
    (chk : heavy s r T ws = true) : Bad s T k ws := by
  intro n cap run
  have hc := List.toFinset_card_of_nodup nd
  obtain ⟨_,cost⟩ := tight_sum run (fee s r) (fee_sub s r)
  specialize cost (by omega)
  rw [List.sum_toFinset _ nd] at cost
  have bad := of_decide_eq_true chk
  omega
def delta (s : Bool) (w : W) : W :=
  if s then (w >>> 767) ^^^ w else (w >>> 767) &&& ~~~w

def cover (s : Bool) : List W → W
  | [] => 0
  | a::ws => delta s a ||| cover s ws

theorem delta_gate {s : Bool} {j : Nat} (legal : j < ar s) (a b : W) (i : Nat)
    (h : (delta s (gate j a b)).getLsbD i = true) :
    (delta s a).getLsbD i = true ∨ (delta s b).getLsbD i = true := by
  have lim := bound_op legal
  by_cases hp : 767+i < 1534
  · have hi : i < 1534 := by omega
    cases s <;> simp only [ar,ite_false,ite_true,Bool.false_eq_true] at legal <;>
      interval_cases j <;> simp_all [delta,gate,BitVec.getLsbD_not] <;> grind
  · have falseBit (v : W) : v.getLsbD (767+i) = false :=
      BitVec.getLsbD_of_ge _ _ (by omega)
    cases s <;> interval_cases j <;>
      simp_all [delta,gate,BitVec.getLsbD_not] <;> grind

theorem plan_bit {s T k S} (run : Plan s T k S) (i : Nat)
    (h : (delta s T).getLsbD i = true) : ∃ w ∈ S, (delta s w).getLsbD i = true := by
  induction run with
  | stop => exact ⟨T,by simp,h⟩
  | @step k U a b j legal _ _ _ _ _ ih =>
    obtain ⟨w,hw,yes⟩ := ih
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases delta_gate legal a b i yes with yes | yes
      · exact ⟨a,by simp,yes⟩
      · exact ⟨b,by simp,yes⟩
    · exact ⟨w,by simp [hw],yes⟩

theorem cover_bit {s ws i} : (cover s ws).getLsbD i = true ↔
    ∃ w ∈ ws, (delta s w).getLsbD i = true := by
  induction ws with
  | nil => simp [cover]
  | cons a ws ih => simp only [cover,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

def separated (s : Bool) (T : W) (ws : List W) :=
  (delta false T &&& cover s ws) == delta false T

theorem plan_sep {s T k ws} (run : Plan s T k (List.toFinset ws)) : separated s T ws = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  by_cases h : (delta false T).getLsbD i = true
  · have hs : (delta s T).getLsbD i = true := by
      cases s
      · exact h
      · simp only [delta,ite_false,Bool.false_eq_true,BitVec.getLsbD_and,
          BitVec.getLsbD_ushiftRight,BitVec.getLsbD_not,hi,decide_true,Bool.true_and,
          Bool.and_eq_true,Bool.not_eq_true'] at h
        simp only [delta,ite_true,BitVec.getLsbD_xor,BitVec.getLsbD_ushiftRight,h.1,h.2]
        rfl
    obtain ⟨w,hm,hw⟩ := plan_bit run i hs
    rw [h,(cover_bit.mpr ⟨w,List.mem_toFinset.mp hm,hw⟩)]
    rfl
  · simp [Bool.eq_false_iff.mpr h]

structure Fact where
  d : W
  roots : List W
  target : W
  bound : Nat
deriving Inhabited

def Sound (s : Bool) (f : Fact) := Low s f.roots f.target f.bound

structure Rule where
  d : W
  pool : List W
  rank : Nat
deriving Inhabited

def Valid (s : Bool) (T : W) (r : Rule) : Prop :=
  ∀ k S, Plan s T k S → (∀ w ∈ S, w &&& r.d = 0 ∨ w &&& r.d ∈ r.pool) →
    r.rank + mass r.d S ≤ k

def paid (s : Bool) (w : List W) (code : Nat) : W :=
  gate (code % ar s) (w.getD ((code / 4) % 16) 0) (w.getD (code/64) 0)

def material (s : Bool) (roots : List W) : List Nat → List W
  | [] => roots
  | c::cs => material s (roots ++ [paid s roots c]) cs

theorem read_bank {s R p B} (born : Build s R p B) {ws : List W} (sub : ∀ w ∈ ws, w ∈ B) (i : Nat) :
    ws.getD i 0 ∈ B := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => exact build_zero born
  | some v => exact sub _ (List.mem_of_getElem? h)

theorem material_build {s R p B} (born : Build s R p B) (ws : List W)
    (sub : ∀ w ∈ ws, w ∈ B) (cs : List Nat) :
    ∃ C, Build s R (p+cs.length) C ∧ ∀ w ∈ material s ws cs, w ∈ C := by
  induction cs generalizing p B ws with
  | nil => exact ⟨B,born,sub⟩
  | cons c cs ih =>
    have h := Build.step born (read_bank born sub ((c/4)%16)) (read_bank born sub (c/64))
      (c % ar s) (Nat.mod_lt _ (by cases s <;> decide))
    obtain ⟨C,b,inc⟩ := ih h (ws ++ [paid s ws c]) (by
      intro w hw
      rcases List.mem_append.mp hw with orig | extra
      · exact Finset.mem_insert_of_mem (sub _ orig)
      · have eq : w = paid s ws c := by simpa using extra
        exact eq ▸ Finset.mem_insert_self _ _)
    exact ⟨C,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b,inc⟩

def makeRule (s : Bool) (f : Fact) (cs : List Nat) : Rule :=
  ⟨f.d,material s f.roots cs,f.bound-cs.length⟩

theorem make_valid {s T} (f : Fact) (cs : List Nat) (sound : Sound s f)
    (eq : T &&& f.d = f.target) (nz : f.target ≠ 0) (small : cs.length ≤ f.bound) :
    Valid s T (makeRule s f cs) := by
  intro k S run supply
  obtain ⟨B,born,all⟩ := material_build (s:=s) (R:=f.roots.toFinset) Build.start f.roots
    (fun w hw => Finset.mem_insert_of_mem (List.mem_toFinset.mpr hw)) cs
  obtain ⟨q,C,hq,mem,le⟩ := project run f.d born (by
    intro w hw
    rcases supply w hw with zero | hp
    · exact zero ▸ build_zero born
    · exact all _ hp) (eq ▸ nz)
  have lower := sound _ _ hq (eq ▸ mem)
  change f.bound-cs.length + mass f.d S ≤ k
  omega

def blocks (r : Rule) (k : Nat) (ws : List W) : Bool :=
  k < r.rank + (ws.countP fun w => (w &&& r.d) == 0) &&
  ws.all fun w => (w &&& r.d) == 0 || r.pool.contains (w &&& r.d)

theorem mass_count (d : W) (ws : List W) (nd : ws.Nodup) :
    mass d ws.toFinset = ws.countP (fun w => (w &&& d) == 0) := by
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp nd
    have hm : a ∉ ws.toFinset := by simpa using ha
    rw [List.toFinset_cons,mass,Finset.sum_insert hm,←mass,ih hn,List.countP_cons]
    by_cases eq : a &&& d = 0
    · simp only [cost,if_pos eq,eq,beq_self_eq_true,ite_true,Nat.add_comm]
    · have no := beq_eq_false_iff_ne.mpr eq
      simp only [cost,if_neg eq,no,Bool.false_eq_true,ite_false,Nat.zero_add,Nat.add_zero]

theorem blocked {s T r k ws} (valid : Valid s T r) (nd : List.Nodup ws)
    (h : blocks r k ws = true) : Bad s T k ws := by
  intro n hn run
  obtain ⟨l,inc⟩ := Bool.and_eq_true_iff.mp h
  have bound := of_decide_eq_true l
  have lo := valid _ _ run (by
    intro w hw
    have h := List.all_eq_true.mp inc w (List.mem_toFinset.mp hw)
    simpa only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] using h)
  rw [mass_count r.d ws nd] at lo
  omega

def remain (ws : List W) (a b : W) (ka kb : Bool) :=
  ws.filter (fun w => (w != a || ka) && (w != b || kb))

def child (ws : List W) (a b : W) (op : Nat) (ka kb : Bool) :=
  gate op a b :: remain ws a b ka kb

theorem reverse_gate {s j} (leg : j < ar s) (a b : W) :
    ∃ i < ar s, gate i b a = gate j a b := by
  have lt := bound_op leg
  cases s <;> simp [ar] at leg ⊢ <;> interval_cases j
  all_goals first
    | exact ⟨0,by decide,BitVec.and_comm ..⟩
    | exact ⟨1,by decide,BitVec.or_comm ..⟩
    | exact ⟨2,by decide,rfl⟩
    | exact ⟨3,by decide,rfl⟩

theorem branches {s T k ws} (nd : List.Nodup ws) (missing : T ∉ ws)
    (each : ∀ a ∈ ws, ∀ b ∈ ws, a < b → ∀ j < ar s, ∀ ka kb, gate j a b ∉ ws →
      gate j a b ≠ 0 → (child ws a b j ka kb).length ≤ k →
      Bad s T (k-1) (child ws a b j ka kb)) : Bad s T k ws := by
  intro n hn run
  generalize eq : ws.toFinset = S at run
  cases run with
  | stop =>
    exact missing (List.mem_toFinset.mp (eq.symm ▸ Finset.mem_singleton_self _))
  | @step n U a b j leg ha hb hab fresh tail =>
    have go (a b : W) (j : Nat) (lt : a < b) (leg : j < ar s)
        (eq : ws.toFinset = insert a (insert b U)) (fresh : gate j a b ∉ insert a (insert b U))
        (tail : Plan s T n (insert (gate j a b) U)) : False := by
      have am : a ∈ ws := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_self _ _)
      have bm : b ∈ ws := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      let ka := decide (a ∈ U)
      let kb := decide (b ∈ U)
      have keep : (remain ws a b ka kb).toFinset = U := by
        ext w
        have ew : w ∈ ws ↔ w = a ∨ w = b ∨ w ∈ U := by
          rw [←List.mem_toFinset,eq]; simp
        simp only [List.mem_toFinset,List.mem_filter,remain,Bool.and_eq_true,
          Bool.or_eq_true,bne_iff_ne,ka,kb,decide_eq_true_eq,ew]
        grind
      have q : (child ws a b j ka kb).toFinset = insert (gate j a b) U := by simp [child,keep]
      have f : gate j a b ∉ ws := fun h => fresh (eq ▸ List.mem_toFinset.mpr h)
      have z : gate j a b ≠ 0 := plan_nonzero tail _ (Finset.mem_insert_self _ _)
      have nc : (child ws a b j ka kb).Nodup := List.nodup_cons.mpr
        ⟨fun hm => f (List.mem_of_mem_filter hm),nd.filter _⟩
      have len := List.toFinset_card_of_nodup nc
      rw [q] at len
      have size := plan_size tail
      exact each a am b bm lt j leg ka kb f z (by omega) n (by omega) (q.symm ▸ tail)
    rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => hab (BitVec.eq_of_toNat_eq e)) with lt | gt
    · exact go a b j lt leg eq fresh tail
    · obtain ⟨i,hi,same⟩ := reverse_gate leg a b
      exact go b a i gt hi (by simpa only [Finset.insert_comm b a] using eq)
        (by simpa only [same,Finset.insert_comm b a] using fresh) (same.symm ▸ tail)
abbrev Recipe := Nat × List Nat

def same (ws vs : List W) := ws.all vs.contains && vs.all ws.contains

theorem same_set {ws vs} (h : same ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
  ext w
  simp only [List.mem_toFinset]
  exact ⟨fun m => List.contains_iff_mem.mp (List.all_eq_true.mp a _ m),
    fun m => List.contains_iff_mem.mp (List.all_eq_true.mp b _ m)⟩
theorem subset_sep {s T k S} (run : Plan s T k S) (ws : List W) (sub : S ⊆ ws.toFinset) :
    separated s T ws = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  by_cases h : (delta false T).getLsbD i = true
  · have hs : (delta s T).getLsbD i = true := by
      cases s
      · exact h
      · simp only [delta,ite_false,Bool.false_eq_true,BitVec.getLsbD_and,
          BitVec.getLsbD_ushiftRight,BitVec.getLsbD_not,hi,decide_true,Bool.true_and,
          Bool.and_eq_true,Bool.not_eq_true'] at h
        simp only [delta,ite_true,BitVec.getLsbD_xor,BitVec.getLsbD_ushiftRight,h.1,h.2]
        rfl
    obtain ⟨w,hm,hw⟩ := plan_bit run i hs
    rw [h,(cover_bit.mpr ⟨w,List.mem_toFinset.mp (sub hm),hw⟩)]
    rfl
  · simp [Bool.eq_false_iff.mpr h]

def remove (ws : List W) (w : W) := ws.filter (· != w)

theorem excluding {S : Finset W} {ws : List W} {w} (h : S ⊆ ws.toFinset) (miss : w ∉ S) :
    S ⊆ (remove ws w).toFinset := by
  intro x hx
  have eq : x ≠ w := fun e => miss (e ▸ hx)
  exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_toFinset.mp (h hx),bne_iff_ne.mpr eq⟩)

def needed (s : Bool) (T : W) (ws raw : List W) :=
  raw.all fun w => !separated s T (remove ws w)

theorem forced {s T ws raw k S} (run : Plan s T k S) (sub : S ⊆ List.toFinset ws)
    (h : needed s T ws raw = true) : raw.toFinset ⊆ S := by
  intro w hw
  by_contra miss
  have bad := List.all_eq_true.mp h w (List.mem_toFinset.mp hw)
  have yes := subset_sep run _ (excluding sub miss)
  simp_all

theorem low_card {s T k ws raw} (nz : T ≠ 0) (need : needed s T ws raw = true)
    (nd : raw.Nodup) (len : k+1 ≤ raw.length) : Low s ws T k := by
  intro p B born mem
  obtain ⟨n,S,budget,run,sub⟩ := unwind born (Plan.stop nz) (Finset.singleton_subset_iff.mpr mem)
  have hc := Finset.card_le_card (forced run sub need)
  rw [List.toFinset_card_of_nodup nd] at hc
  have size := plan_size run
  omega

theorem low_search {s T k raw es} (nz : T ≠ 0) (need : needed s T (raw++es) raw = true)
    (without : ∀ w ∈ es, Low s (remove (raw++es) w) T k)
    (no : Bad s T (k-1) (raw++es)) : Low s (raw++es) T k := by
  intro p B born mem
  obtain ⟨n,S,budget,run,sub⟩ := unwind born (Plan.stop nz) (Finset.singleton_subset_iff.mpr mem)
  by_cases all : ∀ w ∈ es, w ∈ S
  · have whole : (raw++es).toFinset = S := by
      refine Finset.Subset.antisymm ?_ sub
      intro w hw
      rcases List.mem_append.mp (List.mem_toFinset.mp hw) with hm | hm
      · exact forced run sub need (List.mem_toFinset.mpr hm)
      · exact all w hm
    by_contra! small
    exact no n (by omega) (whole.symm ▸ run)
  · push_neg at all
    obtain ⟨w,hw,miss⟩ := all
    have le := low_plan (without w hw) run (excluding sub miss) nz
    omega

theorem weaken {s R T a b} (h : Low s R T a) (le : b ≤ a) : Low s R T b :=
  fun p B r m => le.trans (h p B r m)
abbrev Sm := BitVec 59

def stack {α : Type} (f : α → Sm) : (xs : List α) → BitVec (59*xs.length)
  | [] => 0
  | x::xs => stack f xs ++ f x

theorem stack_op {α : Type} (f g : α → Sm) (j : Nat) (xs : List α) :
    stack (fun x => bop j (f x) (g x)) xs = bop j (stack f xs) (stack g xs) := by
  induction xs with
  | nil => exact @Subsingleton.elim (BitVec 0) _ _ _
  | cons x xs ih => rw [stack,stack,stack,bop_append,ih]

def positives : List Nat := [3,6,10,12,15,17,26,37,41,50,53,54,58]
def tile (v : Sm) (i : Nat) : Sm := if v.getLsbD i then BitVec.allOnes 59 else 0
def expand (v : Sm) : W :=
  stack (tile v) positives ++ stack (fun _ => v) positives

theorem tile_op (j : Nat) (a b : Sm) (i : Nat) :
    tile (bop j a b) i = bop j (tile a i) (tile b i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rcases j with _ | _ | _ | j <;> by_cases hi : i < 59 <;>
    cases x : a.getLsbD i <;> cases y : b.getLsbD i <;>
    simp_all [bop,tile,BitVec.getLsbD_not,BitVec.getLsbD_allOnes] <;> grind

theorem expand_op (j : Nat) (a b : Sm) : expand (bop j a b) = gate j (expand a) (expand b) := by
  rw [gate_bop]
  have h1 : tile (bop j a b) = fun i => bop j (tile a i) (tile b i) := funext (tile_op j a b)
  exact (congrArg₂ (fun x y : BitVec (59*positives.length) => x ++ y)
    ((congrArg (fun f => stack f positives) h1).trans (stack_op _ _ j positives))
    (stack_op (fun _ => a) (fun _ => b) j positives)).trans
    (bop_append j _ _ _ _).symm

set_option maxRecDepth 10000 in
theorem expand_zero : expand 0 = 0 := by decide +kernel

def rawWords : List Sm :=
  [360930119642124586,432486920269079116,293578547141297264,289365901620316032,
   439119665042618368,297239789478805504,306275578149863424,540467122476679168,576425567931334656]

def rawGoal : Sm := 316380210352264264
def xword (i : Nat) : Sm := rawWords.getD i 0
/- On a proper induced graph only the empty assignment, singletons and pairs
are needed. Their samples are preserved by every graph isomorphism. -/
def maskOf (m : Nat) : Sm :=
  ((List.range 9).filter fun i => !m.testBit i).foldl (fun v i => v &&& ~~~(xword i)) (if m=511 then BitVec.allOnes 59 else 66964093258432511)
def rawSet (m : Nat) := ((List.range 9).filter m.testBit).map fun i => expand (xword i &&& maskOf m)
def extraWord (m e : Nat) := expand ((xword (e/10) ||| xword (e % 10)) &&& maskOf m)
def extraSet (m : Nat) (es : List Nat) := es.map (extraWord m)
def inputSet (m : Nat) (es : List Nat) := rawSet m ++ extraSet m es
def goalAt (m : Nat) := expand (rawGoal &&& maskOf m)
def item (m : Nat) (es : List Nat) (v : Nat) : Fact :=
  ⟨expand (maskOf m),inputSet m es,goalAt m,v⟩
def Claim (s : Bool) (m : Nat) (es : List Nat) (n : Nat) := Sound s (item m es n)

/- Spread thirteen bits to the starts of the bands, then broadcast each bit
by multiplying by the word of fifty-nine ones. -/
def bandWord (c : Nat) : W :=
  let stripe := 0x1000000000000002000000000000004000000000000008000000000000010000000000000020000000000000040000000000000080000000000000100000000000000200000000000000400000000000000800000000000001
  let v := c >>> 59
  let v := (v ||| (v <<< 464)) &&& 0x1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff
  let v := (v ||| (v <<< 232)) &&& 0x10000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000f
  let v := (v ||| (v <<< 116)) &&& 0x100000000000000000000000000000c0000000000000000000000000000300000000000000000000000000000c0000000000000000000000000000300000000000000000000000000000c00000000000000000000000000003
  let v := (v ||| (v <<< 58)) &&& stripe
  BitVec.ofNat 1534 (((v * 0x7ffffffffffffff) <<< 767) ||| ((c &&& 0x7ffffffffffffff)*stripe))

def bitsAt (rows : List Nat) (w : W) : BitVec rows.length :=
  match rows with
  | [] => 0
  | r::rs => bitsAt rs w ++ BitVec.ofBool (w.getLsbD r)

theorem pick_op (j : Nat) (a b : W) (r : Nat) :
    BitVec.ofBool ((gate j a b).getLsbD r) =
      bop j (BitVec.ofBool (a.getLsbD r)) (BitVec.ofBool (b.getLsbD r)) := by
  rcases j with _ | _ | _ | j <;> by_cases hr : r < 1534 <;>
    cases x : a.getLsbD r <;> cases y : b.getLsbD r <;>
    simp_all [bop,gate,BitVec.getLsbD_not,BitVec.getLsbD_of_ge]

theorem bits_op (j : Nat) (a b : W) (rows : List Nat) :
    bitsAt rows (gate j a b) = bop j (bitsAt rows a) (bitsAt rows b) := by
  induction rows with
  | nil => exact @Subsingleton.elim (BitVec 0) _ _ _
  | cons r rs ih => rw [bitsAt,bitsAt,bitsAt,bop_append,ih,pick_op]

def relabel (rows : List Nat) (w : W) : W := expand ((bitsAt rows w).setWidth 59)

theorem relabel_op (rows : List Nat) (h : rows.length = 59) (j : Nat) (a b : W) :
    relabel rows (gate j a b) = gate j (relabel rows a) (relabel rows b) := by
  unfold relabel
  rw [bits_op,←expand_op]
  apply congrArg expand
  generalize bitsAt rows a = a' , bitsAt rows b = b'
  generalize rows.length = n at *
  subst n
  simp

theorem transfer {s R S T G n} (old : Low s S G n) (f : W → W) (zero : f 0 = 0)
    (hom : ∀ j a b, f (gate j a b) = gate j (f a) (f b)) (target : f T = G)
    (roots : ∀ w ∈ R, f w ∈ S) : Low s R T n := by
  intro p B born mem
  have mapBuild {q B} (h : Build s R.toFinset q B) :
      ∃ C, Build s S.toFinset q C ∧ ∀ w ∈ B, f w ∈ C := by
    induction h with
    | start =>
      refine ⟨_,Build.start,?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hm
      · rw [zero]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (roots w (List.mem_toFinset.mp hm)))
    | @step p B a b prev ha hb j leg ih =>
      obtain ⟨C,hc,all⟩ := ih
      refine ⟨_,Build.step hc (all a ha) (all b hb) j leg,?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hm
      · simp only [hom, Finset.mem_insert_self]
      · exact Finset.mem_insert_of_mem (all w hm)
  obtain ⟨C,hc,inc⟩ := mapBuild born
  exact old p C hc (target ▸ inc T mem)

def related (R S : List W) (T G : W) (rows : List Nat) :=
  rows.length == 59 && relabel rows 0 == 0 && relabel rows T == G &&
    R.all (fun w => S.contains (relabel rows w))

theorem by_rows {R S T G s n} (lo : Low s S G n) (rs : List Nat) (h : related R S T G rs = true) :
    Low s R T n := by
  simp only [related,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_iff_mem] at h
  exact transfer lo _ h.1.1.2 (relabel_op rs h.1.1.1) h.1.2 h.2

theorem shrink {s m es a b} (bound : Claim s m es a) (h : b ≤ a) : Claim s m es b :=
  weaken bound h

theorem rename_rows {s m es q fs n} (lower : Claim s q fs n) (rows : List Nat)
    (h : related (inputSet m es) (inputSet q fs) (goalAt m) (goalAt q) rows = true) :
    Claim s m es n := by_rows lower rows h
abbrev G := Fin 3 × List (Fin 25)

/- Normalize a wire by its value on the all-zero row. An inversion then
costs no binary gate. An AND or OR becomes one of four binary operations
on the normalized wires. With no inversions, two operations suffice. -/
def norm (a : Sm) := if a.getLsbD 0 then ~~~a else a
def clean (a : Sm) := a.getLsbD 0 = true → a = BitVec.allOnes 59
def holds (s : Bool) (B : Finset W) (a : Sm) :=
  expand (norm a) ∈ B ∧ (s = false → clean a)

theorem norm_inv (a : Sm) : norm (~~~a) = norm a := by
  cases h : a.getLsbD 0 <;> simp_all [norm,BitVec.getLsbD_not]

theorem norm_bin (j : Nat) (lt : j < 2) (a b : Sm) :
    ∃ i < 4, norm (bop j a b) = bop i (norm a) (norm b) := by
  interval_cases j <;> cases ha : a.getLsbD 0 <;> cases hb : b.getLsbD 0
  · exact ⟨0,by decide,by simp_all [norm,bop]⟩
  · exact ⟨2,by decide,by simp_all [norm,bop]⟩
  · exact ⟨3,by decide,by simp_all [norm,bop,BitVec.and_comm]⟩
  · exact ⟨1,by decide,by simp_all [norm,bop,BitVec.not_and]⟩
  · exact ⟨1,by decide,by simp_all [norm,bop]⟩
  · exact ⟨3,by decide,by simp_all [norm,bop,BitVec.not_or,BitVec.and_comm]⟩
  · exact ⟨2,by decide,by simp_all [norm,bop,BitVec.not_or]⟩
  · exact ⟨0,by decide,by simp_all [norm,bop,BitVec.not_or]⟩

theorem clean_bin (j : Nat) (lt : j < 2) {a b : Sm} (ca : clean a) (cb : clean b) :
    clean (bop j a b) := by
  intro h
  interval_cases j
  · obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp (show a.getLsbD 0 && b.getLsbD 0 = true by simpa [bop] using h)
    rw [bop,ca x,cb y,BitVec.and_self]
  · rcases Bool.or_eq_true_iff.mp (show a.getLsbD 0 || b.getLsbD 0 = true by simpa [bop] using h) with x | y
    · rw [bop,ca x,BitVec.allOnes_or]
    · rw [bop,cb y,BitVec.or_allOnes]

set_option maxRecDepth 10000 in
theorem holds_const {s R p B} (born : Build s R p B) :
    holds s B 0 ∧ holds s B (BitVec.allOnes 59) := by
  have z : norm 0 = 0 := rfl
  have o : norm (BitVec.allOnes 59) = 0 := by decide
  constructor
  · exact ⟨by rw [z,expand_zero]; exact build_zero born,by simp [clean]⟩
  · exact ⟨by rw [o,expand_zero]; exact build_zero born,fun _ _ => rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem holds_binary {s R p B a b} (born : Build s R p B) (ha : holds s B a) (hb : holds s B b)
    (j : Nat) (lt : j < 2) :
    ∃ q C, Build s R q C ∧ q ≤ p+1 ∧ B ⊆ C ∧ holds s C (bop j a b) := by
  have good : s = false → clean (bop j a b) := fun h => clean_bin j lt (ha.2 h) (hb.2 h)
  obtain ⟨i,hi,eq⟩ := norm_bin j lt a b
  have act : expand (norm (bop j a b)) = gate i (expand (norm a)) (expand (norm b)) := by
    rw [eq,expand_op]
  by_cases ok : i < ar s
  · exact ⟨p+1,_,Build.step born ha.1 hb.1 i ok,by omega,Finset.subset_insert _ _,
      act ▸ Finset.mem_insert_self _ _,good⟩
  · have hs : s = false := by cases s <;> simp_all [ar]
    by_cases az : a.getLsbD 0 = true
    · have au := ha.2 hs az
      have bit : expand (norm a) = 0 := by rw [au,show norm (BitVec.allOnes 59) = 0 by decide,expand_zero]
      rw [bit] at act
      rcases (idle i (expand (norm b))).1 with z | z
      · exact ⟨p,B,born,by omega,Finset.Subset.rfl,Eq.mpr (congrArg (fun w : W => w ∈ B) (act.trans z)) (build_zero born),good⟩
      · exact ⟨p,B,born,by omega,Finset.Subset.rfl,Eq.mpr (congrArg (fun w : W => w ∈ B) (act.trans z)) hb.1,good⟩
    by_cases bz : b.getLsbD 0 = true
    · have bu := hb.2 hs bz
      have bit : expand (norm b) = 0 := by rw [bu,show norm (BitVec.allOnes 59) = 0 by decide,expand_zero]
      rw [bit] at act
      rcases (idle i (expand (norm a))).2.1 with z | z
      · exact ⟨p,B,born,by omega,Finset.Subset.rfl,Eq.mpr (congrArg (fun w : W => w ∈ B) (act.trans z)) (build_zero born),good⟩
      · exact ⟨p,B,born,by omega,Finset.Subset.rfl,Eq.mpr (congrArg (fun w : W => w ∈ B) (act.trans z)) ha.1,good⟩
    have ab : norm (bop j a b) = bop j (norm a) (norm b) := by
      have af := Bool.eq_false_iff.mpr az
      have bf := Bool.eq_false_iff.mpr bz
      interval_cases j <;> simp only [norm,bop,BitVec.getLsbD_or,BitVec.getLsbD_and,
        af,bf,Bool.and_self,Bool.or_self,Bool.false_eq_true,ite_false]
    have leg : j < ar s := by rw [hs]; exact lt
    exact ⟨p+1,_,Build.step born ha.1 hb.1 j leg,by omega,Finset.subset_insert _ _,
      Eq.mpr (congrArg (fun w : W => w ∈ insert (gate j (expand (norm a)) (expand (norm b))) B)
        ((congrArg expand ab).trans (expand_op j _ _))) (Finset.mem_insert_self _ _),good⟩

def evalGate (w : List Sm) (g : G) :=
  let xs := g.2.map fun i => w.getD i.val 0
  if g.1 = 0 then xs.foldr (· &&& ·) (~~~0)
  else if g.1 = 1 then xs.foldr (· ||| ·) 0 else ~~~xs.headD 0

def grow (w : List Sm) (g : G) := w ++ [evalGate w g]
def tally (gs : List G) := gs.countP fun g => g.1 != 2

theorem fetch_hold {s R p B} (born : Build s R p B) {ws : List Sm}
    (inc : ∀ w ∈ ws, holds s B w) (i : Nat) : holds s B (ws.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => exact (holds_const born).1
  | some v => exact inc v (List.mem_of_getElem? h)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem append_gate {s R p B} (born : Build s R p B) (w : List Sm) (inc : ∀ v ∈ w, holds s B v)
    (g : G) (arity : g.2.length ≤ 2) (invOk : g.1 = 2 → s = true) :
    ∃ q C, Build s R q C ∧ q ≤ p + (if g.1 = 2 then 0 else 1) ∧
      B ⊆ C ∧ holds s C (evalGate w g) := by
  obtain ⟨op,args⟩ := g
  have pin (i : Fin 25) := fetch_hold born inc i.val
  have negcase (n : Sm) (h : holds s B n) (e : s = true) : holds s B (~~~n) := by
    exact ⟨by rw [norm_inv]; exact h.1,by simp [e]⟩
  have ones (v : Sm) : v &&& ~~~(0 : Sm) = v := BitVec.and_allOnes
  have oz (v : Sm) : v ||| (0 : Sm) = v := BitVec.or_zero
  by_cases nt : op = 2
  · subst op
    refine ⟨p,B,born,by simp,Finset.Subset.rfl,?_⟩
    change holds s B (~~~((args.map fun i : Fin 25 => w.getD i.val 0).headD 0))
    apply negcase _ _ (invOk rfl)
    cases args with
    | nil => exact (holds_const born).1
    | cons i rest => exact pin i
  have bin : op = 0 ∨ op = 1 := by omega
  change args.length ≤ 2 at arity
  change ∃ q C, Build s R q C ∧ q ≤ p+(if op = 2 then 0 else 1) ∧ B ⊆ C ∧ holds s C _
  rw [if_neg nt]
  cases args with
  | nil =>
    refine ⟨p,B,born,by simp,Finset.Subset.rfl,?_⟩
    rcases bin with rfl | rfl
    · exact (holds_const born).2
    · exact (holds_const born).1
  | cons i rest =>
    cases rest with
    | nil =>
      refine ⟨p,B,born,by simp,Finset.Subset.rfl,?_⟩
      rcases bin with rfl | rfl
      · change holds s B (w.getD i.val 0 &&& ~~~(0 : Sm))
        rw [ones]; exact pin i
      · change holds s B (w.getD i.val 0 ||| 0)
        rw [oz]; exact pin i
    | cons h tail =>
      have e : tail = [] := by simpa using arity
      subst tail
      rcases bin with rfl | rfl
      · change ∃ q C, Build s R q C ∧ q ≤ p+1 ∧ B ⊆ C ∧ holds s C
          (w.getD i.val 0 &&& (w.getD h.val 0 &&& ~~~(0 : Sm)))
        rw [ones]; exact holds_binary born (pin i) (pin h) 0 (by decide)
      · change ∃ q C, Build s R q C ∧ q ≤ p+1 ∧ B ⊆ C ∧ holds s C
          (w.getD i.val 0 ||| (w.getD h.val 0 ||| 0))
        rw [oz]; exact holds_binary born (pin i) (pin h) 1 (by decide)

theorem build_trace {s R p B} (born : Build s R p B) (gs : List G) (w : List Sm)
    (inc : ∀ v ∈ w, holds s B v) (arity : ∀ g ∈ gs, g.2.length ≤ 2)
    (invOk : ∀ g ∈ gs, g.1 = 2 → s = true) :
    ∃ q C, Build s R q C ∧ q ≤ p+tally gs ∧ ∀ v ∈ gs.foldl grow w, holds s C v := by
  induction gs generalizing p B w with
  | nil => exact ⟨p,B,born,by simp [tally],inc⟩
  | cons g gs ih =>
    obtain ⟨q,C,hc,hq,sub,got⟩ := append_gate born w inc g (arity g (by simp)) (invOk g (by simp))
    obtain ⟨r,D,hd,hr,all⟩ := ih hc (grow w g) (by
      intro v hv
      rcases List.mem_append.mp hv with old | one
      · exact ⟨sub (inc v old).1,(inc v old).2⟩
      · have e : v = evalGate w g := by simpa using one
        exact e ▸ got) (fun z hz => arity z (by simp [hz])) (fun z hz => invOk z (by simp [hz]))
    refine ⟨r,D,hd,?_,all⟩
    simp only [tally,List.countP_cons] at hr ⊢
    by_cases e : g.1 = 2 <;> simp [e] at hq ⊢ <;> omega

def actual (a b : Fin 9) := rawWords ++ [xword 0 ||| xword 4,xword a.val ||| xword b.val]
def key (a b : Fin 9) := 10*min a.val b.val + max a.val b.val

set_option maxRecDepth 10000 in
theorem actual_data : ∀ a b : Fin 9,
    (actual a b).map expand = inputSet 511 [4,key a b] ∧
    (actual a b).all (fun v => !v.getLsbD 0) = true := by decide +kernel

theorem finish (s : Bool) (a b : Fin 9) (gs : List G) (out : Fin 25)
    (arity : ∀ g ∈ gs, g.2.length ≤ 2) (invOk : ∀ g ∈ gs, g.1 = 2 → s = true)
    (bound : Claim s 511 [4,key a b] (tally gs+1)) :
    (gs.foldl grow (actual a b)).getD out.val 0 ≠ rawGoal := by
  intro eq
  obtain ⟨inputs,bits⟩ := actual_data a b
  obtain ⟨q,C,born,cap,all⟩ := build_trace (R:=(inputSet 511 [4,key a b]).toFinset)
    (s:=s) Build.start gs (actual a b) (by
      intro v hv
      have h : v.getLsbD 0 = false := by simpa using List.all_eq_true.mp bits v hv
      have normal : norm v = v := by simp only [norm,h,Bool.false_eq_true,ite_false]
      refine ⟨?_,fun _ hp => (Bool.noConfusion (h.symm.trans hp))⟩
      rw [normal,←inputs]
      exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hv)))
    arity invOk
  have h := (fetch_hold born all out.val).1
  rw [eq] at h
  have tgt : expand (norm rawGoal) = goalAt 511 := by decide +kernel
  rw [tgt] at h
  have low : tally gs+1 ≤ q := bound q C born h
  omega

theorem from_bounds (a b : Fin 9) (gs : List G) (out : Fin 25) (small : gs.length ≤ 13)
    (arity : ∀ g ∈ gs, g.2.length ≤ 2) (mono : Claim false 511 [4,key a b] 14)
    (signed : Claim true 511 [4,key a b] 13) :
    (gs.foldl grow (actual a b)).getD out.val 0 ≠ rawGoal := by
  by_cases inv : ∃ g ∈ gs, g.1 = 2
  · obtain ⟨g,mem,isNot⟩ := inv
    have ht : tally gs < gs.length := List.countP_lt_length_iff.mpr ⟨g,mem,by simp [isNot]⟩
    exact finish true a b gs out arity (by simp) (shrink signed (by omega))
  · have ht : tally gs ≤ gs.length := List.countP_le_length
    exact finish false a b gs out arity (fun g mem op => False.elim (inv ⟨g,mem,op⟩))
      (shrink mono (by omega))
def retain (a b : W) (ka kb : Bool) (others : List W) :=
  let v := if kb then b::others else others
  if ka then a::v else v

theorem rearrange {ws : List W} (nd : ws.Nodup) {a b : W} (aa : a ∈ ws)
    (bb : b ∈ ws) (ab : a ≠ b) (ka kb : Bool) :
    (remain ws a b ka kb).Perm (retain a b ka kb (remain ws a b false false)) := by
  have na : a ∉ remain ws a b false false := by simp [remain]
  have nb : b ∉ remain ws a b false false := by simp [remain]
  have nd0 : (remain ws a b false false).Nodup := nd.filter _
  have good : (retain a b ka kb (remain ws a b false false)).Nodup := by
    cases ka <;> cases kb <;> simp [retain,nd0,na,nb,ab]
  apply (List.perm_ext_iff_of_nodup (nd.filter _) good).mpr
  intro w
  cases ka <;> cases kb <;>
    simp only [retain,remain,List.mem_filter,List.mem_cons,Bool.and_eq_true,Bool.or_true,
      Bool.or_false,bne_iff_ne,ite_true,ite_false,Bool.false_eq_true,true_and,and_true] <;> grind

theorem cov_perm {s : Bool} {xs ys : List W} (p : xs.Perm ys) : cover s xs = cover s ys := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  apply Bool.eq_iff_iff.mpr
  rw [cover_bit,cover_bit]
  exact ⟨fun ⟨w,h,v⟩ => ⟨w,p.mem_iff.mp h,v⟩,fun ⟨w,h,v⟩ => ⟨w,p.mem_iff.mpr h,v⟩⟩

structure Pick where
  wire : W
  rest : List W
  cov : W

def picks (s : Bool) : List W → List Pick
  | [] => []
  | a::ws => ⟨a,ws,cover s ws⟩ ::
      (picks s ws).map fun p => ⟨p.wire,a::p.rest,delta s a ||| p.cov⟩

theorem pick_one (s : Bool) {ws : List W} (a : W) (ha : a ∈ ws) :
    ∃ p ∈ picks s ws, p.wire=a ∧ ws.Perm (a::p.rest) ∧ p.cov = cover s p.rest := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | tail
    · exact ⟨_,List.mem_cons_self,rfl,List.Perm.refl _,rfl⟩
    · obtain ⟨p,hp,eq,perm,cov⟩ := ih tail
      exact ⟨_,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩),eq,
        (perm.cons _).trans (List.Perm.swap _ _ _),by simp [cover,cov]⟩

theorem retain_perm (a b : W) (ka kb : Bool) {xs ys : List W} (p : xs.Perm ys) :
    (retain a b ka kb xs).Perm (retain a b ka kb ys) := by
  cases ka <;> cases kb <;> first | exact p | exact p.cons _ | exact (p.cons _).cons _

def withCover (s : Bool) (a b : W) (ka kb : Bool) (c : W) :=
  let u := if kb then delta s b ||| c else c
  if ka then delta s a ||| u else u

def withSize (ka kb : Bool) (n : Nat) := n+kb.toNat+ka.toNat

def spent (a b : W) (ka kb : Bool) := retain a b (!ka) (!kb) []

theorem split_use {ws : List W} (nd : ws.Nodup) {a b : W} (aa : a ∈ ws) (bb : b ∈ ws)
    (ab : a ≠ b) (ka kb : Bool) : ws.Perm (spent a b ka kb ++ remain ws a b ka kb) := by
  let tail := remain ws a b false false
  have whole : ws.Perm (a::b::tail) := by simpa [tail,remain,retain] using rearrange nd aa bb ab true true
  have suffixPerm := rearrange nd aa bb ab ka kb
  apply whole.trans (List.Perm.trans _ (suffixPerm.symm.append_left (spent a b ka kb)))
  cases ka <;> cases kb <;> first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _

theorem retain_cover (s : Bool) (a b : W) (ka kb : Bool) (others : List W) :
    cover s (retain a b ka kb others) = withCover s a b ka kb (cover s others) := by
  cases ka <;> cases kb <;> rfl

theorem retain_length (a b : W) (ka kb : Bool) (others : List W) :
    (retain a b ka kb others).length = withSize ka kb others.length := by
  cases ka <;> cases kb <;> simp [retain,withSize]

/- If one use can be shared, a retained operand must cover the deficit
of every subadditive cost. This checks possible shared uses once per state. -/
def keepers (s : Bool) (T : W) (k : Nat) (ws : List W) (rs : List Nat) : List W :=
  if rs.isEmpty || ws.length != k then ws else
    let tests := rs.map fun r => (r,fee s r T - (ws.map (fee s r)).sum)
    ws.filter fun w => tests.all fun p => p.2 ≤ fee s p.1 w

theorem keep_mem {s T k ws rs w} (mem : w ∈ ws)
    (cost : ws.length = k → ∀ r ∈ rs, fee s r T ≤ (ws.map (fee s r)).sum + fee s r w) :
    w ∈ keepers s T k ws rs := by
  unfold keepers
  split
  · exact mem
  · rename_i h
    have len : ws.length = k := by simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr h)).2
    refine List.mem_filter.mpr ⟨mem,List.all_eq_true.mpr ?_⟩
    intro p hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    have bound := cost len r hr
    exact decide_eq_true (by dsimp; omega)

theorem use_cost {s T k ws a b j ka kb w n} (nd : ws.Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (leg : j < ar s) (fresh : gate j a b ∉ ws)
    (cap : n ≤ k-1) (run : Plan s T n (child ws a b j ka kb).toFinset)
    (len : ws.length = k) (use : (ka = true ∧ w = a) ∨ (kb = true ∧ w = b)) (r : Nat) :
    fee s r T ≤ (ws.map (fee s r)).sum + fee s r w := by
  let f := fee s r
  let v := child ws a b j ka kb
  have nv : v.Nodup := List.nodup_cons.mpr
    ⟨fun hm => fresh (List.mem_of_mem_filter hm),nd.filter _⟩
  have whole : ws.Perm (a::b::remain ws a b false false) := by
    simpa [remain,retain] using rearrange nd ha hb ne true true
  have pp := rearrange nd ha hb ne ka kb
  have l1 := whole.length_eq
  have l2 := pp.length_eq
  have card : v.toFinset.card = v.length := List.toFinset_card_of_nodup nv
  obtain ⟨size,bound⟩ := tight_sum run f (fee_sub s r)
  change v.toFinset.card ≤ n+1 at size
  have lenv : v.length = (remain ws a b ka kb).length+1 := rfl
  have big : n+1 ≤ v.toFinset.card := by
    cases ka <;> cases kb <;> simp_all [retain] <;> omega
  specialize bound big
  rw [List.sum_toFinset _ nv] at bound
  have s1 := (whole.map f).sum_eq
  have s2 := (pp.map f).sum_eq
  have add := fee_sub s r j leg a b
  change f (gate j a b) ≤ f a + f b at add
  change f T ≤ f (gate j a b) + ((remain ws a b ka kb).map f).sum at bound
  change f T ≤ (ws.map f).sum + f w
  cases ka <;> cases kb <;>
    simp_all only [retain,ite_true,ite_false,Bool.false_eq_true,false_and,true_and,
      or_false,false_or,or_self,List.length_cons,List.map_cons,List.sum_cons] <;> omega
/- A ticket lists the live wires by their indices. For each surviving
child, one digit selects a formula cost, a restriction to a smaller graph,
or a state at the preceding level. The proof enumerates every child. -/
structure Ticket where
  state : Nat
  mark : Nat
  costs : Nat
  views : Nat
  palette : Nat
  data : Nat
deriving Inhabited

structure Book where
  signed : Bool
  roots : List W
  target : W
  limit : Nat
  ruleCount : Nat
  rule : Nat → Rule
  hint : Nat → Nat
  width : Nat
  wires : Nat → List W
  size : Nat → Nat
  atLevel : Nat → Nat → Ticket

def allGood (b : Book) (k : Nat) := ∀ i, i < b.size k →
  Bad b.signed b.target k (b.wires (b.atLevel k i).state)

def unpack (word : Nat → W) (width : Nat) : Nat → Nat → List W
  | 0,_ => []
  | n+1,v => word (v % (2^width)) :: unpack word width n (v >>> width)

def unpackState (word : Nat → W) (width code : Nat) := unpack word width (code % 16) (code >>> 4)

def shortcut (b : Book) (k code : Nat) (ws : List W) :=
  let i := code/3
  if code % 3 = 0 then ws.length == k+1 && heavy b.signed (b.hint i) b.target ws
  else i < b.ruleCount && blocks (b.rule i) k ws

theorem shortcut_bad {b k code ws} (nd : List.Nodup ws)
    (valid : ∀ i, i < b.ruleCount → Valid b.signed b.target (b.rule i))
    (ok : shortcut b k code ws = true) : Bad b.signed b.target k ws := by
  unfold shortcut at ok
  split at ok
  · obtain ⟨len,yes⟩ := Bool.and_eq_true_iff.mp ok
    exact heavy_bad nd (beq_iff_eq.mp len) yes
  · obtain ⟨hi,cut⟩ := Bool.and_eq_true_iff.mp ok
    exact blocked (valid _ (of_decide_eq_true hi)) nd cut

def viewAt (table i : Nat) := (table >>> (8+24*i)) % 16777216

def holes (ws : List W) (code : Nat) : List W :=
  let k := (code >>> 12) % 16
  let l := (code >>> 16) % 16
  if k=0 then [] else if l=0 then [ws.getD (k-1) 0] else [ws.getD (k-1) 0,ws.getD (l-1) 0]

def usable (r : Rule) (w : W) := (w &&& r.d) == 0 || r.pool.contains (w &&& r.d)

def zeroAt (r : Rule) (w : W) := (w &&& r.d) == 0

structure Choice where
  z : W
  rest : List W
  used : List W

def Choice.live (c : Choice) := c.z::c.rest

def viewsPass (b : Book) (ws : List W) (table : Nat) :=
  (List.range (table % 256)).all fun i =>
    let c := viewAt table i
    let r := b.rule (c % 4096)
    (c % 4096 < b.ruleCount && (c >>> 20) ≤ ws.countP (zeroAt r)) &&
      ws.all fun w => (holes ws c).contains w || usable r w

def afterCut (r : Rule) (hs : List W) (zeros k : Nat) (v : Choice) :=
  usable r v.z && hs.all (fun h => !v.rest.contains h) &&
    k + v.used.countP (zeroAt r) < r.rank + zeros + (zeroAt r v.z).toNat

theorem after_bad {b : Book} {src : List W} {table i k} {v : Choice} (nd : v.live.Nodup) (part : src.Perm (v.used++v.rest))
    (valid : ∀ i, i < b.ruleCount → Valid b.signed b.target (b.rule i))
    (views : viewsPass b src table = true) (hi : i < table % 256)
    (test : afterCut (b.rule (viewAt table i % 4096)) (holes src (viewAt table i)) (viewAt table i >>> 20) k v = true) :
    Bad b.signed b.target k v.live := by
  have check := List.all_eq_true.mp views i (List.mem_range.mpr hi)
  obtain ⟨pair,all⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨idx,zeroBound⟩ := Bool.and_eq_true_iff.mp pair
  let r := b.rule (viewAt table i % 4096)
  have sum := part.countP_eq (zeroAt r)
  rw [List.countP_append] at sum
  have zeros := of_decide_eq_true zeroBound
  change viewAt table i >>> 20 ≤ src.countP (zeroAt r) at zeros
  obtain ⟨pair,cap⟩ := Bool.and_eq_true_iff.mp test
  obtain ⟨first,miss⟩ := Bool.and_eq_true_iff.mp pair
  have lt := of_decide_eq_true cap
  change k+v.used.countP (zeroAt r) < r.rank+(viewAt table i >>> 20)+(zeroAt r v.z).toNat at lt
  apply blocked (valid _ (of_decide_eq_true idx)) nd
  refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true ?_,List.all_eq_true.mpr ?_⟩
  · change k < r.rank+(v.z::v.rest).countP (zeroAt r)
    rw [List.countP_cons]
    cases h : zeroAt r v.z <;> simp_all <;> omega
  ·
    intro w hw
    rcases List.mem_cons.mp hw with rfl | tail
    · exact first
    · have sub := part.mem_iff.mpr (List.mem_append_right _ tail)
      rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp all w sub) with hole | ok
      · have no := List.all_eq_true.mp miss w (List.contains_iff_mem.mp hole)
        exact False.elim ((show w ∉ v.rest by simpa using no) tail)
      · exact ok

def why (b : Book) (src : List W) (table k code : Nat) (v : Choice) :=
  if code % 3 = 2 then
    code/3 < b.size k && same v.live (b.wires (b.atLevel k (code/3)).state)
  else if code % 3 = 1 then
    let i := code/3
    let c := viewAt table i
    i < table % 256 && afterCut (b.rule (c % 4096)) (holes src c) (c >>> 20) k v
  else shortcut b k code v.live

theorem why_bad {b : Book} {src : List W} {table k code} {v : Choice} (nd : v.live.Nodup) (part : src.Perm (v.used++v.rest))
    (valid : ∀ i, i < b.ruleCount → Valid b.signed b.target (b.rule i))
    (views : viewsPass b src table = true) (known : allGood b k)
    (ok : why b src table k code v = true) : Bad b.signed b.target k v.live := by
  unfold why at ok
  split at ok
  · obtain ⟨hi,he⟩ := Bool.and_eq_true_iff.mp ok
    intro n hn run
    exact known _ (of_decide_eq_true hi) n hn (same_set he ▸ run)
  · split at ok
    · obtain ⟨hi,test⟩ := Bool.and_eq_true_iff.mp ok
      exact after_bad nd part valid views (of_decide_eq_true hi) test
    · exact shortcut_bad nd valid ok

def decodeCosts (atId : Nat → Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,v => if v=0 then [] else atId (v % 4096-1) :: decodeCosts atId n (v >>> 12)

def flags (tight free : Bool) (allowed : List W) (w : W) : List Bool :=
  if tight then [false] else if free || allowed.contains w then [false,true] else [false]

def offspring (s : Bool) (T : W) (k : Nat) (ws : List W) (rs : List Nat) :=
  let allowed := keepers s T k ws rs
  let tight := ws.length == k+1
  let size := ws.length-2
  (picks s ws).flatMap fun p => (picks s p.rest).flatMap fun q =>
    let a := p.wire
    let b := q.wire
    if a.toNat < b.toNat then
      (flags tight rs.isEmpty allowed a).flatMap fun ka => (flags tight rs.isEmpty allowed b).flatMap fun kb =>
        let rest := retain a b ka kb q.rest
        if withSize ka kb size < k then
          let seen := withCover s a b ka kb q.cov
          let wanted := delta false T
          (List.range (ar s)).filterMap fun j =>
            let z := gate j a b
            if (wanted &&& (delta s z ||| seen)) == wanted then
              if z == 0 || ws.contains z then none else some (⟨z,rest,spent a b ka kb⟩ : Choice)
            else none
        else []
    else []

theorem exhaust_children {s T k ws rs} (nd : ws.Nodup) (miss : T ∉ ws)
    (known : ∀ v ∈ offspring s T k ws rs, v.live.Nodup → ws.Perm (v.used++v.rest) →
      Bad s T (k-1) v.live) : Bad s T k ws := by
  apply branches nd miss
  intro a ha b hb lt j leg ka kb fresh nz len
  let v := child ws a b j ka kb
  have nv : v.Nodup := List.nodup_cons.mpr
    ⟨fun hm => fresh (List.mem_of_mem_filter hm),nd.filter _⟩
  intro n hn run
  have sep := plan_sep (ws:=v) run
  have size : (remain ws a b ka kb).length < k := by
    change (remain ws a b ka kb).length+1 ≤ k at len
    omega
  have ne : a ≠ b := fun e => (Nat.ne_of_lt (show a.toNat < b.toNat from lt)) (congrArg BitVec.toNat e)
  obtain ⟨pa,hpa,eqa,perma,_⟩ := pick_one s a ha
  have bp : b ∈ pa.rest := (List.mem_cons.mp (perma.mem_iff.mp hb)).resolve_left (Ne.symm ne)
  obtain ⟨pb,hpb,eqb,permb,cs⟩ := pick_one s b bp
  have whole : ws.Perm (a::b::remain ws a b false false) := by
    simpa [remain,retain] using rearrange nd ha hb ne true true
  have mix := perma.trans (permb.cons a)
  have sameRest := (whole.symm.trans mix).cons_inv.cons_inv
  have hperm := rearrange nd ha hb ne ka kb
  have restPerm := hperm.trans (retain_perm a b ka kb sameRest)
  have sz : withSize ka kb (ws.length-2) < k := by
    have length := mix.length_eq
    simp only [List.length_cons] at length
    rw [show ws.length-2=pb.rest.length by omega,←retain_length a b,restPerm.length_eq.symm]
    exact size
  have cov := (cov_perm (s:=s) restPerm).trans (retain_cover _ _ _ _ _ _)
  have allowed (x : W) (hx : x ∈ ws) (use : (ka = true ∧ x=a) ∨ (kb = true ∧ x=b)) :
      (keepers s T k ws rs).contains x = true :=
    List.contains_iff_mem.mpr (keep_mem hx (fun h r _ => use_cost nd ha hb ne leg fresh hn run h use r))
  have limit : ws.length = k+1 → ka=false ∧ kb=false := by
    have l := mix.length_eq
    simp only [List.length_cons] at l
    intro atLimit
    cases ka <;> cases kb <;> simp_all [withSize] <;> omega
  have inFlags (c : Bool) (x : W) (cap : ws.length=k+1 → c=false)
      (ok : c=true → (keepers s T k ws rs).contains x=true) :
      c ∈ flags (ws.length == k+1) rs.isEmpty (keepers s T k ws rs) x := by
    by_cases len : ws.length = k+1
    · simp [flags,len,cap len]
    · cases h : c with
      | false => simp [flags,len]; split <;> simp
      | true =>
        have hm := List.contains_iff_mem.mp (ok h)
        simp [flags,len,hm]
  have fa := inFlags ka a (fun h => (limit h).1) (fun h => allowed a ha (Or.inl ⟨h,rfl⟩))
  have fb := inFlags kb b (fun h => (limit h).2) (fun h => allowed b hb (Or.inr ⟨h,rfl⟩))
  let entry : Choice := ⟨gate j a b,retain a b ka kb pb.rest,spent a b ka kb⟩
  have ok : entry ∈ offspring s T k ws rs := by
    apply List.mem_flatMap.mpr
    refine ⟨pa,hpa,List.mem_flatMap.mpr ⟨pb,hpb,?_⟩⟩
    simp only [eqa,eqb]
    rw [if_pos (show a.toNat < b.toNat from lt)]
    apply List.mem_flatMap.mpr
    refine ⟨ka,fa,List.mem_flatMap.mpr ⟨kb,fb,?_⟩⟩
    simp only [sz,ite_true]
    apply List.mem_filterMap.mpr
    refine ⟨j,List.mem_range.mpr leg,?_⟩
    have no := Bool.eq_false_iff.mpr (fun h => fresh (List.contains_iff_mem.mp h))
    have z0 := beq_eq_false_iff_ne.mpr nz
    change (delta false T &&& (delta s (gate j a b) ||| cover s (remain ws a b ka kb))) == delta false T at sep
    rw [cov,←cs] at sep
    simp only [z0,no,Bool.or_self,Bool.false_eq_true,ite_false,sep,ite_true]
    rfl
  have swap := restPerm.cons (gate j a b)
  exact known _ ok (swap.nodup_iff.mp nv)
    ((split_use nd ha hb ne ka kb).trans (restPerm.append_left _)) n hn ((List.toFinset_eq_of_perm _ _ swap) ▸ run)

def tickets (b : Book) (src : List W) (table k pal width : Nat) : Nat → List Choice → Bool
  | _,[] => true
  | data,v::vs =>
    let ix := data % (2^width)
    let tag := if pal=0 then ix else (pal >>> (4+ix*b.width)) % (2^b.width)
    why b src table k tag v && tickets b src table k pal width (data >>> width) vs

theorem tickets_ok {b src table k vs data pal width}
    (valid : ∀ i, i < b.ruleCount → Valid b.signed b.target (b.rule i))
    (views : viewsPass b src table = true) (prev : allGood b k)
    (ok : tickets b src table k pal width data vs = true) :
    ∀ v ∈ vs, v.live.Nodup → src.Perm (v.used++v.rest) → Bad b.signed b.target k v.live := by
  induction vs generalizing data with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp ok
    intro v hv nv sub
    rcases List.mem_cons.mp hv with rfl | h
    · exact why_bad nv sub valid views prev first
    · exact ih rest v h nv sub

def linePass (b : Book) (k : Nat) (e : Ticket) :=
  let ws := b.wires e.state
  decide ws.Nodup && (k+1 < ws.length || !separated b.signed b.target ws ||
    if e.mark == 0 then !ws.contains b.target && viewsPass b ws e.views && tickets b ws e.views (k-1) e.palette
      (if e.palette=0 then b.width else e.palette % 16) e.data
        (offspring b.signed b.target k ws (decodeCosts b.hint 3 e.costs))
    else shortcut b k (e.mark-1) ws)

theorem line_ok {b k e}
    (valid : ∀ i, i < b.ruleCount → Valid b.signed b.target (b.rule i))
    (prev : allGood b (k-1)) (ok : linePass b k e = true) :
    Bad b.signed b.target k (b.wires e.state) := by
  let ws := b.wires e.state
  change decide ws.Nodup && (_ || _ || _) = true at ok
  obtain ⟨nd,other⟩ := Bool.and_eq_true_iff.mp ok
  have hn := of_decide_eq_true nd
  rcases Bool.or_eq_true_iff.mp other with early | passed
  · rcases Bool.or_eq_true_iff.mp early with big | sep
    · intro n cap run
      have count := plan_size run
      rw [List.toFinset_card_of_nodup hn] at count
      have sz := of_decide_eq_true big
      change k+1 < ws.length at sz
      omega
    · intro n cap run
      have ht := plan_sep (ws:=ws) run
      change (!separated b.signed b.target ws) = true at sep
      simp_all
  · by_cases h : e.mark = 0
    · simp only [h,beq_self_eq_true,ite_true,Bool.and_eq_true,Bool.not_eq_true'] at passed
      exact exhaust_children hn (by simpa using passed.1.1) (tickets_ok valid passed.1.2 prev passed.2)
    · simp only [beq_eq_false_iff_ne.mpr h,Bool.false_eq_true,ite_false] at passed
      exact shortcut_bad hn valid passed

def bookRange (b : Book) (k i n : Nat) :=
  (List.range n).all fun j => linePass b k (b.atLevel k (i+j))

theorem book_split {b k i a c} (l : bookRange b k i a = true) (r : bookRange b k (i+a) c = true) :
    bookRange b k i (a+c) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have lt := List.mem_range.mp hj
  by_cases first : j<a
  · exact List.all_eq_true.mp l j (List.mem_range.mpr first)
  · have h := List.all_eq_true.mp r (j-a) (List.mem_range.mpr (by omega))
    simpa only [show i+a+(j-a)=i+j by omega] using h

theorem book_level (b : Book) (k : Nat)
    (valid : ∀ i, i < b.ruleCount → Valid b.signed b.target (b.rule i))
    (prev : allGood b (k-1)) (ok : bookRange b k 0 (b.size k) = true) : allGood b k := by
  intro i hi
  apply line_ok valid prev
  have h := List.all_eq_true.mp ok i (List.mem_range.mpr hi)
  simpa only [Nat.zero_add] using h

theorem book_empty (b : Book) (k : Nat) (h : b.size k = 0) : allGood b k := by
  intro i hi
  omega

theorem book_end (b : Book) (good : allGood b b.limit) (nonempty : 0 < b.size b.limit)
    (start : b.wires (b.atLevel b.limit 0).state = b.roots) :
    Bad b.signed b.target b.limit b.roots := start ▸ good 0 nonempty

def readRule {s} (fs : Nat → {f : Fact // Sound s f}) (rs : Nat → Recipe) (i : Nat) :=
  let r := rs i
  makeRule s (fs r.1).val r.2

def legalAt {s} (T : W) (fs : Nat → {f : Fact // Sound s f}) (rs : Nat → Recipe) (i : Nat) :=
  let r := rs i
  let f := (fs r.1).val
  (T &&& f.d == f.target) && f.target != 0 && r.2.length ≤ f.bound

theorem validateRules {s T n} (fs : Nat → {f : Fact // Sound s f}) (rs : Nat → Recipe)
    (ok : (List.range n).all (legalAt T fs rs) = true) :
    ∀ i, i < n → Valid s T (readRule fs rs i) := by
  intro i hi
  have ch := List.all_eq_true.mp ok i (List.mem_range.mpr hi)
  simp only [legalAt,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ch
  exact make_valid _ _ (fs (rs i).1).property ch.1.1 ch.1.2 ch.2
def hintsm31 (i : Nat) : Nat := (0xc28524e3c7864907183c634e24a1419069c30a0c83451831871068618c385343 >>> (37*(i % 16))) % 137438953472
def wiresm31 (i : Nat) : W := bandWord ((0xc00000000000f80000a00000000000878000300000000000447000180000000000224c00480000000000112a >>> (72*(i % 8))) % 4722366482869645213696)
def levm31k6 (i : Nat) : Ticket := (#[⟨0x46885,0,0x0,0x0,0x127b0c03,0x204180ca048⟩] : Array Ticket).getD (i % 8) default
def treem31 : Book :=
  ⟨false,inputSet 31 [],goalAt 31,6,0,(fun _ => default),hintsm31,5,unpackState wiresm31 3,(fun k => match k with | 6 => 1 | _ => 0),fun k => match k with
    | 6 => levm31k6
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm31 : ∀ i, i < 0 → Valid false (goalAt 31) ((treem31).rule i) := by
  intro i hi
  omega
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm31k6i0 : bookRange treem31 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm31k6 : allGood treem31 6 :=
  book_level treem31 6 rulesm31 (book_empty treem31 5 rfl) passm31k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm31 : Claim false 31 [] 7 := by
  apply low_search (s:=false) (T:=goalAt 31) (raw:=rawSet 31) (es:=extraSet 31 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end treem31 goodm31k6 (by decide) (by decide +kernel)
def hintsm31e4 (i : Nat) : Nat := (0xa3053883c78c69c49418c388343 >>> (37*(i % 16))) % 137438953472
def wiresm31e4 (i : Nat) : W := bandWord ((0xc80000000000f92a00c00000000000f80000a00000000000878000300000000000447000180000000000224c00480000000000112a >>> (72*(i % 8))) % 4722366482869645213696)
def levm31e4k6 (i : Nat) : Ticket := (#[⟨0x2c6886,0,0x2001,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def treem31e4 : Book :=
  ⟨false,inputSet 31 [4],goalAt 31,6,0,(fun _ => default),hintsm31e4,4,unpackState wiresm31e4 3,(fun k => match k with | 6 => 1 | _ => 0),fun k => match k with
    | 6 => levm31e4k6
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm31e4 : ∀ i, i < 0 → Valid false (goalAt 31) ((treem31e4).rule i) := by
  intro i hi
  omega
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm31e4k6i0 : bookRange treem31e4 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm31e4k6 : allGood treem31e4 6 :=
  book_level treem31e4 6 rulesm31e4 (book_empty treem31e4 5 rfl) passm31e4k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm31e4 : Claim false 31 [4] 7 := by
  apply low_search (s:=false) (T:=goalAt 31) (raw:=rawSet 31) (es:=extraSet 31 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 31 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 31 [4]) (extraWord 31 4) = inputSet 31 [] := by decide +kernel
      change Low false (remove (inputSet 31 [4]) (extraWord 31 4)) (goalAt 31) 7
      rw [eq]
      exact claimm31
  · exact book_end treem31e4 goodm31e4k6 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm167 : Claim false 167 [] 7 :=
  rename_rows claimm31 [0,1,2,3,4,5,6,34,35,36,37,16,17,18,19,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintsm189 (i : Nat) : Nat := (0x1494a2744aa4ca235911850b35078f4548e8307cb4273143e5a0e98a >>> (37*(i % 16))) % 137438953472
def wiresm189 (i : Nat) : W := bandWord ((0xc0000036c000000000900000200005b000000c00001000040d80000a000004000108580042000002000084430014000000800021122 >>> (72*(i % 8))) % 4722366482869645213696)
def levm189k7 (i : Nat) : Ticket := (#[⟨0x2c6886,0,0x0,0x0,0xf624c03,0x6002080c9801200010⟩] : Array Ticket).getD (i % 8) default
def treem189 : Book :=
  ⟨false,inputSet 189 [],goalAt 189,7,0,(fun _ => default),hintsm189,5,unpackState wiresm189 3,(fun k => match k with | 7 => 1 | _ => 0),fun k => match k with
    | 7 => levm189k7
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm189 : ∀ i, i < 0 → Valid false (goalAt 189) ((treem189).rule i) := by
  intro i hi
  omega
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm189k7i0 : bookRange treem189 7 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm189k7 : allGood treem189 7 :=
  book_level treem189 7 rulesm189 (book_empty treem189 6 rfl) passm189k7i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm189 : Claim false 189 [] 8 := by
  apply low_search (s:=false) (T:=goalAt 189) (raw:=rawSet 189) (es:=extraSet 189 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end treem189 goodm189k7 (by decide) (by decide +kernel)
def hintsm189e4 (i : Nat) : Nat := (0xa4ca235911460b41078f9684e6287cb41d3143e5a1320a >>> (37*(i % 16))) % 137438953472
def wiresm189e4 (i : Nat) : W := bandWord ((0xc0000036c000000000900000200005b000001c00001080042d92200c00001000040d80000a000004000108580042000002000084430014000000800021122 >>> (72*(i % 8))) % 4722366482869645213696)
def levm189e4k7 (i : Nat) : Ticket := (#[⟨0x1356887,0,0x5003,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def treem189e4 : Book :=
  ⟨false,inputSet 189 [4],goalAt 189,7,0,(fun _ => default),hintsm189e4,5,unpackState wiresm189e4 3,(fun k => match k with | 7 => 1 | _ => 0),fun k => match k with
    | 7 => levm189e4k7
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm189e4 : ∀ i, i < 0 → Valid false (goalAt 189) ((treem189e4).rule i) := by
  intro i hi
  omega
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm189e4k7i0 : bookRange treem189e4 7 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm189e4k7 : allGood treem189e4 7 :=
  book_level treem189e4 7 rulesm189e4 (book_empty treem189e4 6 rfl) passm189e4k7i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm189e4 : Claim false 189 [4] 8 := by
  apply low_search (s:=false) (T:=goalAt 189) (raw:=rawSet 189) (es:=extraSet 189 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 189 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 189 [4]) (extraWord 189 4) = inputSet 189 [] := by decide +kernel
      change Low false (remove (inputSet 189 [4]) (extraWord 189 4)) (goalAt 189) 8
      rw [eq]
      exact claimm189
  · exact book_end treem189e4 goodm189e4k7 (by decide) (by decide +kernel)
def hintsm187 (i : Nat) : Nat := (0xa439235911e8a91d060f0c98e83149eb132063e95a4243 >>> (37*(i % 16))) % 137438953472
def wiresm187 (i : Nat) : W := bandWord ((0x94800035c0002110a080000035c0000000009000002000057000000c00001000040b80001c80000480012938a00800000400010838000080000100004220c01480000080002110a >>> (72*(i % 8))) % 4722366482869645213696)
def levm187k5 (i : Nat) : Ticket := (#[⟨0x2c4476,0,0x0,0x0,0x0,0xc3⟩,⟨0x358436,0,0x0,0x0,0x0,0x180⟩] : Array Ticket).getD (i % 8) default
def levm187k6 (i : Nat) : Ticket := (#[⟨0x358886,0,0x5003,0x0,0x0,0x1522⟩] : Array Ticket).getD (i % 8) default
def treem187 : Book :=
  ⟨false,inputSet 187 [],goalAt 187,6,0,(fun _ => default),hintsm187,5,unpackState wiresm187 3,(fun k => match k with | 5 => 2 | 6 => 1 | _ => 0),fun k => match k with
    | 5 => levm187k5
    | 6 => levm187k6
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm187 : ∀ i, i < 0 → Valid false (goalAt 187) ((treem187).rule i) := by
  intro i hi
  omega
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm187k5i0 : bookRange treem187 5 0 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm187k5 : allGood treem187 5 :=
  book_level treem187 5 rulesm187 (book_empty treem187 4 rfl) passm187k5i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm187k6i0 : bookRange treem187 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm187k6 : allGood treem187 6 :=
  book_level treem187 6 rulesm187 goodm187k5 passm187k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm187 : Claim false 187 [] 7 := by
  apply low_search (s:=false) (T:=goalAt 187) (raw:=rawSet 187) (es:=extraSet 187 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end treem187 goodm187k6 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm190 : Claim false 190 [] 7 :=
  rename_rows claimm187 [0,4,2,6,0,0,0,11,14,13,0,7,10,9,0,15,34,37,36,0,40,0,38,0,0,0,0,0,0,0,0,0,0,0,16,19,18,0,22,0,20,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintsm191 (i : Nat) : Nat := ((if i < 112 then (if i < 48 then (if i < 16 then 0x1831d410191a549880c88c9cc4063253a62031831d31018ca689080c89ea484064464e42031831d21018a9458c80c54a2464063063a81431929d20a18c3ce9050c6147482863063a4143 else (if i < 32 then 0xc8a73241864538d20c34a7469061913a34830c61d1a41864531520c32274668618c3a33430c61c29a186a539890c34a74c48618c3a62431f4ad21218aa539090c7ca74848618c3a3243 else 0xc8a62c818630e1640c89ea511864464e88c3187d13461913d69a30c88c9cd18630f3a68c31851d34618c18e9a30c6534491864464e48c31831d24618c18e4a30c60c71b1863063898c3)) else (if i < 80 then (if i < 64 then 0x651099230a0c8a05192871c828c2912241461479120a30a3089051850644828c2832091460c5273481863ce9a40c31874d2061914e39030c89d1c818630e8e40c32299120618c388903 else 0x141912263250c82531850641298c0cf21648606510b2430aa54a0e192d344870c94fa243861489121c30c4454ce186220a670c0e98d634606510b1a30fa6648d186531a468c3d1212346) else (if i < 96 then 0xd4a530a5063cd985287d34262940e58d6906072c69c83032884e418552a5098c2832284c64a7d13263250e39931929f44898c9438e44c6154a922630a3d49131851e44898c9432244c6 else 0x1e61a9a850f18d4d42835295099494fa264ca0d4a53265063cd9932831e6cc7143cc35324a1e31a99250fa684c8287cb4264143c635320a4b4d130a5253e8985292d324c2949438e614a))) else (if i < 160 then (if i < 128 then 0x1f4a919c60f4548ce307864c66980cf26820c074c940a611a54a053089ea502984464e814c234a540a6033c9a05307d2a462983e5a1398a1f29a9cc50f18d4e62878c69d3143cca1350a else (if i < 144 then 0x1460b41078f4548e8307a24c74183c3263a0c1e192450603a64a233089ea511984464e88cc223254466033c9a23301944d11980cf2568cc067927466033c9363307a2a46b183d126358c else 0x1850b35078c2852283c5182d131e28316898f1850b32c78c1859963c50c9d0a1e30a16638f0d29d41a786945a0d3c64a2cc69e19115634f1488b4127869459893c1a242849e0d105424f)) else (if i < 192 then (if i < 176 then 0x527d11a68a90e48d24465342c4220e9916211072c8b1088c18e5884460c6ac4220cf256211194d0b0a88c3e8585441d322c2a23063961511879ab0a8833c95854549f4102a23038e6a0f else 0x679344688ca689234460c7491a2329a168d1074c8b4688c18d5a3441d32291a20e99138d1074c89468a93288d645499246b22a439235915261b1ac8a90c98d6454cb446a22a65923511) else (if i < 208 then 0x523249c92a93d44e394552a509ca1a94a84e50c79b42728aa54a0e9435295074a18f3683a5154a940b28a3d4a05943529502ca18f3681651479340b28a0c8a059549ea1c2ca0e99288d1 else 0x951156a2906647449483301a24a43142cd2524651684e90c60ab25486293512a43142a8952a4a513a25525249d12a91924e89548c6a744aa4a253a25)))) >>> (37*(i % 16))) % 137438953472
def wiresm191 (i : Nat) : W := bandWord (((if i < 32 then (if i < 16 then (if i < 8 then 0x578000028000a557a04300000200008447001580000180006336e00180000100004226c00180000100004224c01480000080002112a001800000000000048000000000000000020 else 0x4b00000600018c7f001f80000580016b7ee00b80000500014a7cc01e8000048001297aa00a0000040001087a000a0000040001087800578000038000e777e0438000030000c667c) else (if i < 24 then 0x4f00001200048fc7001d80001180046fb6e00d80001100044fa4c01c80001080042f92a00c00001000040f82000c00001000040f80004b8000070001ce7fc05f8000068001ad7fa else 0xd30000220005f44700958000218005f336e0918000210005f224c0948000208005f112a0900000200005f00200900000200005f000004f8000130004cfe7c05f8000128004afd7a)) else (if i < 48 then (if i < 40 then 0x9c8000308005ff92a09c0000300005ff8000db0000260005fc7f009b8000250005fa7cc09e8000248005f97aa09a0000240005f87800d38000230005f667c0d78000228005f557a else 0xc3000037c000844700d5800037c0006336e0c1800037c0004224c0d4800037c0002112a0c0000037c000000200c0000037c000000000df0000320005ffc7009d8000310005ffa4c) else (if i < 56 then 0xdc800037c0042f92a0cc000037c0040f8000cb000037c0018c7f00cb800037c0014a7cc0de800037c001297aa0ca000037c001087800c3800037c000c667c0d7800037c000a557a else 0xcf000037c0048fc700cd800037c0044fa4c))) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm191 (i : Nat) : {f : Fact // Sound false f} := (if i < 2 then (if i < 1 then ⟨item 31 [] 7,claimm31⟩ else ⟨item 167 [] 7,claimm167⟩) else (if i < 3 then ⟨item 189 [] 8,claimm189⟩ else (if i < 4 then ⟨item 187 [] 7,claimm187⟩ else ⟨item 190 [] 7,claimm190⟩)))
def recsm191 (i : Nat) : Recipe := ((if i < 8 then #[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(3,[129]),(3,[321]),(4,[197])] else #[(4,[261])]) : Array Recipe).getD (i % 8) default
def levm191k6 (i : Nat) : Ticket := (#[⟨0x1a2831ec5f67,0,0x0,0x0,0x0,0x0⟩,⟨0x2a4831cc7e27,0,0x0,0x0,0x0,0x0⟩,⟨0x1a4860ccb347,0,0x0,0x0,0x0,0x39⟩,⟨0x2a2830a85df7,0,0x0,0x0,0x0,0xc6⟩] : Array Ticket).getD (i % 8) default
def levm191k7 (i : Nat) : Ticket := ((if i < 8 then #[⟨0xa9a48a0c7b178,0,0x0,0x0,0x0,0x2⟩,⟨0x6922860c7b368,0,0x0,0x0,0x0,0x2⟩,⟨0xa9a48a0c731f8,0,0x0,0x0,0x0,0x5⟩,⟨0xa922830877e28,0,0x0,0x0,0x0,0x5⟩,⟨0xa9a4860c73228,0,0x0,0x0,0x0,0x5⟩,⟨0xa9a2830875f68,0,0x0,0x0,0x0,0x2⟩,⟨0x6922860c2b348,0,0x0,0x10100601,0x0,0x6900800496⟩,⟨0xa9a4860ccb0d8,0,0x0,0x0,0x0,0x8⟩] else (if i < 16 then #[⟨0x6922860ccb2d8,0,0x0,0x0,0x0,0x8⟩,⟨0x1a4860ccb327,0,0x51,0x0,0x0,0x27c390203c⟩,⟨0x68a1830ac5f68,0,0x0,0x0,0x0,0x290d5f⟩,⟨0xa9a4860c23348,0,0x0,0x10100501,0x0,0x8700102030⟩,⟨0x2a48608d7627,0,0xd108e,0x0,0x0,0x0⟩,⟨0x1a48608db727,0,0xa100f,0x0,0x0,0x0⟩,⟨0xa922860c2a1f8,0,0x0,0x10200801,0x0,0x5580b00631⟩,⟨0xa9a2860c2a178,0,0x0,0x10200701,0x0,0x9d80b00592⟩] else #[⟨0x2a2860957667,0,0x9a04a,0x0,0x0,0x0⟩,⟨0x1a286095b767,0,0xb4074,0x0,0x0,0x0⟩,⟨0xa9a2830955df8,0,0x0,0x0,0x0,0xb⟩,⟨0xa9228309d5df8,0,0x0,0x0,0x0,0xb⟩,⟨0xa9218308c7e28,0,0x0,0x0,0x0,0x578d17⟩,⟨0x2a2830977e67,0,0x34,0x0,0x0,0x2cc9384c6⟩])) : Array Ticket).getD (i % 8) default
def levm191k8 (i : Nat) : Ticket := ((if i < 40 then (if i < 16 then (if i < 8 then #[⟨0xa9a48a1830848,0,0x8d073,0x0,0x0,0x0⟩,⟨0xa9a48a18308b8,0,0xd3033,0x0,0x0,0x0⟩,⟨0xa9a48a1830938,0,0x73033,0x0,0x0,0x0⟩,⟨0xa9a48a18309b8,0,0x73033,0x0,0x0,0x0⟩,⟨0xa9a48a1830ab8,0,0x73033,0x0,0x0,0x0⟩,⟨0xa9a48a1830a08,0,0xa001c,0x10100220100002,0x0,0x404⟩,⟨0xa9a48a1830b08,0,0x75033,0x10100220100002,0x0,0x404⟩,⟨0xa9a48a1831ec8,0,0xa0,0x20200001,0x0,0x14025f43c69001⟩] else #[⟨0xa9a48a1821c18,0,0xdd0a0,0x0,0x0,0x0⟩,⟨0xa9a48a1830898,0,0x68033,0x0,0x0,0x0⟩,⟨0xa9a48a1831478,0,0xdd07e,0x10200301,0x0,0x1⟩,⟨0xa9a48a0c21c88,0,0xdd068,0x10200201,0x0,0x1⟩,⟨0xa9a48a0c21df8,0,0xa0,0x20200001,0x0,0x4c8c95280b02001⟩,⟨0xa9a48a1830908,0,0x99011,0x10100220100102,0x0,0x404⟩,⟨0xa9a48a1831cc8,0,0xdd,0x20200101,0x0,0x8340e0209f69001⟩,⟨0x2a6922860c21e29,0,0x0,0x0,0x0,0xe02daa14451⟩]) else (if i < 24 then #[⟨0x2a6922860c21f29,0,0x0,0x10100301,0x0,0x20d0c0016a97d690960c030⟩,⟨0xa9a48a1830988,0,0x65019,0x10100220100102,0x0,0x404⟩,⟨0xa9a48a0c21d78,0,0xdd,0x20200101,0x0,0x466a008e152801⟩,⟨0x2a6922860c21e69,0,0x0,0x10100401,0x0,0x26a121325295c0045112048⟩,⟨0x2a6922860c21f69,0,0x0,0x0,0x0,0x115700525896⟩,⟨0xa9a48a18309e8,0,0x73035,0x0,0x0,0x0⟩,⟨0xa922860c271d8,0,0x82073,0x10200201,0x0,0x1⟩,⟨0xa9a48a1830a38,0,0x9c01f,0x20100101,0x0,0x1⟩] else (if i < 32 then #[⟨0xa9a48a1830a78,0,0x7301c,0x0,0x0,0x0⟩,⟨0xa922860c27268,0,0x7301f,0x20200101,0x0,0x1⟩,⟨0xa9a48a1830ae8,0,0x8d03a,0x20100001,0x0,0x1⟩,⟨0x2a6922860c2b0d9,0,0x0,0x0,0x0,0x1a49301749a466a8142ac90⟩,⟨0x6922860c2b2d8,0,0xa0073,0x10200210000002,0x0,0x41a7741491804⟩,⟨0xa9a48a1830b38,0,0x8d050,0x20100120100002,0x0,0x404⟩,⟨0xa9a48a18332c8,0,0x50,0x20200001,0x0,0x74a21089f068170f001⟩,⟨0x6922860c2b328,0,0x51,0x10100620200110000003,0x0,0x4ea0749601e4c93c145f404⟩] else #[⟨0xa9a48a1830b78,0,0x73033,0x20100001,0x0,0x1⟩,⟨0x2a6922860c2b179,0,0x0,0x0,0x0,0x25820270fc008ed2589c⟩,⟨0x6922860c2b368,0,0x73050,0x20200101,0x0,0x80ed01401⟩,⟨0xa9a48a1821558,0,0xaf03a,0x20200101,0x0,0x1⟩,⟨0xa9a48a18215d8,0,0x7e03a,0x20200001,0x0,0x1⟩,⟨0xa9a48a18308e8,0,0x7e03a,0x20100101,0x0,0x1⟩,⟨0xa9a48a1830968,0,0x73033,0x0,0x0,0x0⟩,⟨0xa9a48a1830a18,0,0x6f02f,0x20100001,0x0,0x1⟩]))) else (if i < 64 then (if i < 48 then #[⟨0xa9a48a1830b18,0,0x73033,0x0,0x0,0x0⟩,⟨0xa9a48a18220d8,0,0xd0001,0x20200101,0x0,0x1⟩,⟨0xa9a48a18222d8,0,0x68001,0x20200001,0x0,0x1⟩,⟨0xa9a48a1830918,0,0x73031,0x0,0x0,0x0⟩,⟨0xa9a48a1830998,0,0x6802f,0x20100101,0x0,0x1⟩,⟨0xa9a48a1830a48,0,0x73032,0x0,0x0,0x0⟩,⟨0xa9a48a1830b48,0,0xb508d,0x10100301,0x0,0x8c016a8142acab⟩,⟨0xa9a48a18235d8,0,0xd308d,0x20200001,0x0,0x9801⟩] else (if i < 56 then #[⟨0xa9a48a18236d8,0,0xb508d,0x20200001,0x0,0xa5209190242001⟩,⟨0xa9a4860c230d8,0,0xdd0d3,0x10200210000102,0x0,0x52005d2608c04⟩,⟨0xa9a4860c234f8,0,0xb5099,0x10200301,0x0,0x1⟩,⟨0xa9a4860c23628,0,0xd408d,0x20200001,0x0,0x9801⟩,⟨0xa9a4860c23728,0,0xb508d,0x20200001,0x0,0xa4d86fd2646801⟩,⟨0xa9a48a1830a88,0,0xd3073,0x10100401,0x0,0xbc2c2288a57001⟩,⟨0xa9a48a1830b88,0,0x73033,0x0,0x0,0x0⟩,⟨0xa9a48a18255d8,0,0xd3073,0x20200001,0x0,0xc9687b01805401⟩] else #[⟨0xa9a48a18256d8,0,0xb5073,0x20200001,0x0,0xd401⟩,⟨0x2a6922860c255f9,0,0x0,0x0,0x0,0x156798385adec5702c2288a⟩,⟨0xa9a2860c25158,0,0xb7090,0x10200201,0x0,0x1⟩,⟨0xa9a2860c25578,0,0xdd0b5,0x10200310000102,0x0,0x4385a02f0116b⟩,⟨0xa9a2860c25668,0,0xd3073,0x20200001,0x0,0x6e56b0c81b58801⟩,⟨0xa9a2860c25768,0,0xb6073,0x20200001,0x0,0xd401⟩,⟨0xa922860c275f8,0,0xa008d,0x10200310000002,0x0,0x43b0b1f57b004⟩,⟨0xa922860c27628,0,0xd108e,0x20200101,0x0,0x9801⟩])) else (if i < 72 then #[⟨0x2a6922860c27579,0,0x0,0x0,0x0,0x1710be760ed68559f52289c⟩,⟨0xa922860c27668,0,0xd2073,0x20200101,0x0,0x5c5ef7d43207801⟩,⟨0x6922860c2b6f8,0,0x8d075,0x10200301,0x0,0x1⟩,⟨0x2a6922860c232d9,0,0x0,0x0,0x0,0x21c474234815606a552ac30⟩,⟨0x6922860c2b728,0,0xb308d,0x20200101,0x0,0x47429379a469001⟩,⟨0x6922860c2b768,0,0xb4074,0x20200101,0x0,0xd401⟩,⟨0xa9a48a1830a58,0,0x9c033,0x20100001,0x0,0x1⟩,⟨0x2a6922860c231f9,0,0x0,0x0,0x0,0x3b49c0f8fc0205114451⟩] else (if i < 80 then #[⟨0xa922860c27e28,0,0x8d033,0x20200101,0x0,0xf80b25801⟩,⟨0xa9a48a1830a98,0,0x6f033,0x20100120100002,0x0,0x404⟩,⟨0xa9a48a0c25df8,0,0x33,0x20200001,0x0,0x104e40ec38258c938401⟩,⟨0xa922860c27e68,0,0x34,0x10100820200110000003,0x0,0x44112de67bc2c4c85401c04⟩,⟨0xa9a48a1830b58,0,0x75033,0x0,0x0,0x0⟩,⟨0x6922860c2bf28,0,0xd9033,0x20200101,0x0,0x1⟩,⟨0xa9a48a1830b98,0,0x73033,0x20100101,0x0,0x1⟩,⟨0xa9a4860c23228,0,0xd3050,0x20200001,0x0,0xf8fc03801⟩] else #[⟨0xa9a4860c23328,0,0x50,0x10100510000120200003,0x0,0x10fc01d1d468230760d0c001⟩,⟨0xa9a4860c23f28,0,0x99033,0x20200001,0x0,0x1⟩,⟨0xa9a2860c25268,0,0x90019,0x20200001,0x0,0x1⟩,⟨0xa9a2860c25e68,0,0x33,0x10100710000120200003,0x0,0x10415c5620bc5a9a84801c01⟩,⟨0xa9a2860c25f68,0,0xb5033,0x20200001,0x0,0x801127001⟩])))) : Array Ticket).getD (i % 8) default
def levm191k9 (i : Nat) : Ticket := ((if i < 8 then #[⟨0xa9a48a1830808,0,0x0,0x0,0x1dd6915c558ab2285a1200e02c08014024,0x555555555655555555855555959595b57a898565c5453525190⟩,⟨0xa9a48a1830878,0,0x0,0x10100220100120100003,0xa51da7203e0ec380d4320bc2c0a42608c200741a05c1404407010015,0x139ca719d670a5695785d36ceb59d6b364eab0ce739aa739ceb3ace734ce689cce230a732ce739cc809cc60⟩,⟨0xa9a48a18309c8,0,0x0,0x10100310100220100120000004,0x77583571562ac4e1344a11c441041102807010014,0x9aabaaa810000aaaabaaa710000aa4300006caeaadbcac520000fa0000⟩,⟨0xa9a48a1830ac8,0,0x0,0x10100310100220100120000004,0x1dd571353f0e72ac681946217c5c1645614c5005c1402807010015,0x7000d7bdef7b02002c007be117bd4f7a420000007bc8300100049e77ca6f93e4610000051e5⟩,⟨0xa9a48a1830858,0,0x0,0x10100320100120100003,0x829dd5dd5c4d4b72a0741c46e1ac501042007407010015,0x5ad6b5ae2b5ad6b5056b5ad6b5b16b5ad2162deb6adab435677adae6ad6b5c1645acc05aca05b862⟩,⟨0xa9a48a1830888,0,0x0,0x10100420100120100003,0x26d775a44d48620c801f47a1dc4e1142307407010015,0x294a5294a5298a5604a5294a52960529561294a56954d2b4ae2a5cd6b4a62bca42b46229500294e0⟩,⟨0xa9a48a18308d8,0,0x0,0x10100410100310000220000120100005,0xa51835dc9e26c982549223c8c224831f47114c0d02807010015,0x462108421084210c02178421085c10b6318c4426084b08421108e2108b1946718c5408c520084218c5038c8c4⟩,⟨0xa9a48a1830958,0,0x0,0x10100410100310000220000120100005,0xa515c4d4b92d8b32c0ad2a8a7290a1218741ac0d02807010015,0x46210c0217842e085a108421084210842108651644425884a0842110842116318c6718c5208c5008c8e38c4c4⟩] else (if i < 16 then #[⟨0xa9a48a18309d8,0,0x0,0x10100410100310000220100120000005,0x276775a4571534d4c5308bf2f0a72848f224771b8441040d02807010015,0x83e318c62b0800003a56a52d18c521000006c668180000084c10942108423800001ab18c4a400000⟩,⟨0xa9a48a1830ad8,0,0x0,0x10100410100310000220100120000005,0x871dd691534d4d1338cb320aa29092230801e8561400d02807010015,0x200056318c62b0800f002559cdd19c521001a004667180000084c109421204210006002918c4a4⟩,⟨0xa9a48a18309f8,0,0x0,0x10100410100220100120000004,0x775aa5dce3380dd368d7350bc2b48a1dc5a144480981102807010015,0x246344c831a0100000798c6338c633420000000000c59a6654e7454d2200000054c539883⟩,⟨0xa9a48a1830af8,0,0x0,0x10100410100220100120000004,0x1dd6915c3b0e9398c82dc8a1e85a1201402807010015,0xa5298a56840060005294a9294ab080000000a001c57950e4b8ae388000020541483⟩,⟨0xa9a48a18308c8,0,0x0,0x10100310100220000120100004,0x2949f26d3f0f23bce735ccb2ac951c45c164470b02902807010015,0x2d61084210842108421084218042f08421084315b56c5c9610842a94d725c9225ad0b5d1655ace05acc074483⟩,⟨0xa9a48a18308f8,0,0x0,0x10100410100220000120100004,0x1c86a9a43d4e6350a82608a20c5a0c02902807010015,0x294210842108421084210b42108421094a52b8ae284210a50e53d0e3894531605294832958029560⟩,⟨0xa9a48a1830a28,0,0x0,0x10100410100310100220000120000005,0x6a9a43bcda350bf2ac9b24c8a2245a120470bc0d02807010015,0x108421084210000008421086200001039de300000704210b1526cd6748800000a741cc400000⟩,⟨0xa9a48a1830b28,0,0x0,0x10100410100310100220000120000005,0x6a9a43d4f23a4e6338ab2788c2285f164480c80d02807010015,0x2000421084210800000421086210c000780063386003400084215a64c9c8ca10008000a6618e4⟩] else #[⟨0xa9a48a1830948,0,0x0,0x10100310100220000120100004,0x1da571563e0b02ac741884a1143502807010014,0x551111b1111111111111111115555c5c511a115d9c5c829595e5557055605543⟩,⟨0xa9a48a1830978,0,0x0,0x10100410100220000120100004,0x29488a0a3f8fb3b0e0374c22cc8a21865168480e03502807010015,0x18c10c421804210842108421084210842108426318ce91986085610aa529aa49120c7350c531c83319e0319a0⟩,⟨0xa9a48a1830a68,0,0x0,0x10100410100310100220000120000005,0x571563ecf838cdd314b62aca12284d128480ec0d02807010015,0x86210c00000021084210842108400001e6338600000d085810a66b948ca10000020a632ce400000⟩,⟨0xa9a48a1830b68,0,0x0,0x10100410100310100220000120000005,0x15c558fe3b0d12e4ab2908a1a062168480f80d02807010015,0x10c021000200042108421084200000633c6003800085a10aa4c898cb10009000a631d04⟩])) : Array Ticket).getD (i % 8) default
def levm191k10 (i : Nat) : Ticket := (#[⟨0x2a6922860c27,0,0x0,0x10000220000120000003,0x0,0x4010ec010e0010d4040c8040bc010b001010040a4040980408c0108001074010680105c0405004044070380702c010200101402⟩] : Array Ticket).getD (i % 8) default
def treem191 : Book :=
  ⟨false,inputSet 191 [],goalAt 191,10,9,readRule factsm191 recsm191,hintsm191,10,unpackState wiresm191 6,(fun k => match k with | 6 => 4 | 7 => 22 | 8 => 85 | 9 => 20 | 10 => 1 | _ => 0),fun k => match k with
    | 6 => levm191k6
    | 7 => levm191k7
    | 8 => levm191k8
    | 9 => levm191k9
    | 10 => levm191k10
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm191 : ∀ i, i < 9 → Valid false (goalAt 191) ((treem191).rule i) := by
  exact validateRules factsm191 recsm191 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k6i0 : bookRange treem191 6 0 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191k6 : allGood treem191 6 :=
  book_level treem191 6 rulesm191 (book_empty treem191 5 rfl) passm191k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k7i0 : bookRange treem191 7 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k7i16 : bookRange treem191 7 16 6 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191k7 : allGood treem191 7 :=
  book_level treem191 7 rulesm191 goodm191k6 (@book_split treem191 7 0 16 6 passm191k7i0 passm191k7i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k8i0 : bookRange treem191 8 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k8i16 : bookRange treem191 8 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k8i32 : bookRange treem191 8 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k8i48 : bookRange treem191 8 48 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k8i64 : bookRange treem191 8 64 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k8i80 : bookRange treem191 8 80 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191k8 : allGood treem191 8 :=
  book_level treem191 8 rulesm191 goodm191k7 (@book_split treem191 8 0 48 37 (@book_split treem191 8 0 16 32 passm191k8i0 (@book_split treem191 8 16 16 16 passm191k8i16 passm191k8i32)) (@book_split treem191 8 48 16 21 passm191k8i48 (@book_split treem191 8 64 16 5 passm191k8i64 passm191k8i80)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k9i0 : bookRange treem191 9 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k9i16 : bookRange treem191 9 16 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191k9 : allGood treem191 9 :=
  book_level treem191 9 rulesm191 goodm191k8 (@book_split treem191 9 0 16 4 passm191k9i0 passm191k9i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191k10i0 : bookRange treem191 10 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191k10 : allGood treem191 10 :=
  book_level treem191 10 rulesm191 goodm191k9 passm191k10i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm191 : Claim false 191 [] 11 := by
  apply low_search (s:=false) (T:=goalAt 191) (raw:=rawSet 191) (es:=extraSet 191 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end treem191 goodm191k10 (by decide) (by decide +kernel)
def hintsm191e4 (i : Nat) : Nat := ((if i < 64 then (if i < 32 then (if i < 16 then 0xc89d19a1863ce8cd0c31874668618a4c83430c79c41a18630e20d0c32270a68618c3853430c61d19218c94e9880c65342840644f5122031831c69018c94e9050c60c74828630638d143 else 0xc61d1c818630e2240c31870b20644f5288c31831d24618ca685a30c60c72d186329a128c31831c94618c18e3630c3229c690618c3a34830c61c42418630e1520c3229c668618a4e3343) else (if i < 48 then 0x1e89099c30c4454ce186142a670c31105338606510b1a3032884c91851e45028c2912241461479120a30a0c89051851e41a28c28320d1460c79d34818630e9a40c3229c72061913a3903 else 0x6510b483039634e41850641ab0c28f2284c64a1c722630a3d49131851e44898c9432244c61419122630a0c84931850641a98c2832094c6154a941c3253e890e1852244870c283224386)) else (if i < 96 then (if i < 80 then 0xc79a42c50f18d4d42929f44c99418c3664ca4a79a4265063cd2132831e6cc7143c635324a1e31ab1050f9684c8287ca6a64143c635320a4b4c930a5250e39852835294c294329a1314a else 0x1460b41078a3055883c51829c41e28c14d20f1e8a91d060f0c98e8301d325119844f5288cc223274466033c9a233019e4d04183e5a1398a1f29a9cc50f18d4e6287cb41d3143c634e98a) else (if i < 112 then 0x526491ac8a90e48d6441d322c4223063562111850b35078c2855283c61429341e44a148a0f1850a45078a305a263d2982a931e94c14998f1850a42c78c28598e3c61429071e29116820f else (if i < 128 then 0xd4a542728aa54a0e9431e6d074a0e9916991194d124688ca685a34465322d1a20e99168d11831cb4688c18d5a34549f24cb22a4c926591521c932c8a930d9964549f446b22a4ca23591 else 0x30a166a294a88ab5148a305a26a52982ad3520cc8e892906791449483301a24a52982ad2524651685a9525249d12a91924e89548c6a744aa4a253a25)))) >>> (37*(i % 16))) % 137438953472
def wiresm191e4 (i : Nat) : W := bandWord (((if i < 32 then (if i < 16 then (if i < 8 then 0x1080000000042200800800000000000c12000880000000000a10800a000000000008500000800000000006028000000000000004020001800000000002048000000000000000020 else 0x578000028000a557a04300000200008447001580000180006336e00180000100004626c00180000100004224c01480000080002112a018000000000428100010000000000424020) else (if i < 24 then 0xc00001000040f82000c00001000040f80004b00000600018c7f000b80000500014a7cc01e8000048001297aa00a00000400010c7a000a0000040001087800438000030000c667c else 0x5f8000128004afd7a04f00001200048fc7001d80001180046fb6e00d80001100044fa4c01c80001080042f92a008000010800008100000000010800004020000800010800002008)) else (if i < 48 then (if i < 40 then 0x918000210005f224c0948000208005f112a0900000200005f40200900000200005f000005f8000168005afffa01f80001580056ffee01e80001480052ffaa05f8000138004eff7e else 0x9e8000348005fffaa0df8000328005ffd7a09d8000318005ffb6e09d8000310005ffa4c09c8000308005ff92a09c0000300005ff80009a0000240005f87800d30000220005f4470) else (if i < 56 then 0xcc000037c0040f8000ca000037c001087800c3000037c000844700c1800037c0004224c0d4800037c0002112a0c8800037c0000a1080c0000037c000040200c0000037c00000000 else 0xde800037c0052ffaa0df800037c004afd7a0dd800037c0046fb6e0dc800037c0042f92a))) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm191e4 (i : Nat) : {f : Fact // Sound false f} := (if i < 3 then (if i < 1 then ⟨item 31 [] 7,claimm31⟩ else (if i < 2 then ⟨item 31 [4] 7,claimm31e4⟩ else ⟨item 167 [] 7,claimm167⟩)) else (if i < 5 then (if i < 4 then ⟨item 189 [] 8,claimm189⟩ else ⟨item 189 [4] 8,claimm189e4⟩) else (if i < 6 then ⟨item 187 [] 7,claimm187⟩ else ⟨item 190 [] 7,claimm190⟩)))
def recsm191e4 (i : Nat) : Recipe := (#[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])] : Array Recipe).getD (i % 8) default
def levm191e4k7 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x2459138b2b27,0,0x80020,0x0,0x0,0x0⟩,⟨0x1bc2439351c7,0,0x83071,0x201,0x0,0x1⟩,⟨0x3044e29c9eb7,0,0x5302d,0x0,0x0,0x0⟩,⟨0x2444e29cd387,0,0x85067,0x0,0x0,0x0⟩,⟨0x3044e2a776a7,0,0x3b087,0x0,0x0,0x0⟩,⟨0x3044b2a87ea7,0,0x6102c,0x0,0x0,0x0⟩,⟨0x1bc0e2d3a6a7,0,0xe08b,0x0,0x0,0x0⟩,⟨0x2458e2d3db87,0,0x85023,0x0,0x0,0x0⟩] else #[⟨0x3091638a0447,0,0x4b017,0x0,0x0,0x0⟩]) : Array Ticket).getD (i % 8) default
def levm191e4k8 (i : Nat) : Ticket := ((if i < 24 then (if i < 8 then #[⟨0xc2459138b29f8,0,0x4500e,0x10100320100202,0x0,0x204⟩,⟨0x6f044e2ca9aa8,0,0x61038,0x0,0x0,0x0⟩,⟨0x6f091138a35c8,0,0x8c028,0x0,0x0,0x0⟩,⟨0xc2459138b2838,0,0x53009,0x0,0x0,0x0⟩,⟨0xc2459138b2a08,0,0x49020,0x20100201,0x0,0x1⟩,⟨0xc2459138b2858,0,0x5300b,0x0,0x0,0x2⟩,⟨0xc2459138b2a28,0,0x51020,0x0,0x0,0x0⟩,⟨0x6f091138a51c8,0,0x83071,0x800310000202,0x0,0x40a04⟩] else (if i < 16 then #[⟨0x6f091638b4d48,0,0x83071,0x10000201,0x0,0x205⟩,⟨0x6f091138b2ac8,0,0x83060,0x10100601,0x0,0x1⟩,⟨0x6f091138a7278,0,0x5306003a,0x0,0x0,0x8⟩,⟨0x6f091138a7348,0,0x71060,0x800301,0x0,0x1601⟩,⟨0x6f091138b4dc8,0,0x83071,0x10000201,0x0,0x205⟩,⟨0xc2444e2ca71f8,0,0x71060,0x10100310100202,0x0,0x204⟩,⟨0xc2444e2ca72b8,0,0x53059,0x10100301,0x0,0x1001⟩,⟨0xc2444e2ca7388,0,0x70067,0x10100301,0x0,0x1601⟩] else #[⟨0xc2459138a9dd8,0,0x5301c,0x20100001,0x0,0x1c01⟩,⟨0x6f044e2ca9ea8,0,0x82060,0x0,0x0,0xe⟩,⟨0xc2459138b2878,0,0x8306c053,0x10100610100320100003,0x0,0x1c0204⟩,⟨0xc2459138b2ad8,0,0x53020,0x0,0x0,0x0⟩,⟨0xc1644e2ca9eb8,0,0x5307b,0x10100301,0x0,0x1001⟩,⟨0xc2459138b2988,0,0x5300e,0x10100301,0x0,0x1⟩,⟨0xc2459138b2b98,0,0x53020,0x20100001,0x0,0x1⟩,⟨0x91644e2cad388,0,0x85054,0x10100310100002,0x0,0x41604⟩])) else (if i < 40 then (if i < 32 then #[⟨0xc2444e2ca76a8,0,0x31057,0x20200001,0x0,0x1c01⟩,⟨0x6f044e2caa2a8,0,0x61010,0x10000110800002,0x0,0x440204⟩,⟨0xc2459138b2888,0,0x53020,0x20100001,0x0,0x1⟩,⟨0xc2459138b2ae8,0,0x4f015,0x10100320100220100003,0x0,0x40807⟩,⟨0xc245912caa1f8,0,0x6802c,0x20100001,0x0,0x2201⟩,⟨0xc2459138b2998,0,0x53020,0x0,0x0,0x0⟩,⟨0xc2459138b2ba8,0,0x53020,0x10100320100220100003,0x0,0x40807⟩,⟨0x6f091638b4e98,0,0x8300e,0x0,0x0,0x14⟩] else #[⟨0x6f091638b4f68,0,0x7203800e,0x10000201,0x0,0x2e01⟩,⟨0x6f091138b4ea8,0,0x8300e,0x10000201,0x0,0x214⟩,⟨0xc2459138b4df8,0,0x8c00e,0x20100201,0x0,0x1⟩,⟨0xc2459138b4f88,0,0x8c023,0x20100201,0x0,0x2e01⟩,⟨0xc2459138b2868,0,0x62020,0x0,0x0,0x0⟩,⟨0xc2459138b2a38,0,0x5300e,0x10100301,0x0,0x1⟩,⟨0x6f044e2caa6a8,0,0x8a00e,0x0,0x0,0x14⟩,⟨0xc2459138b2898,0,0x64020,0x0,0x0,0x0⟩]) else (if i < 48 then #[⟨0xc2459138b2af8,0,0x53015,0x0,0x0,0x0⟩,⟨0xc2459138b29a8,0,0x55020,0x20100201,0x0,0x1⟩,⟨0xc2459138b2bb8,0,0x51020,0x20100001,0x0,0x1⟩,⟨0x91644e2cadb88,0,0x85020,0x20100210100002,0x0,0x42e04⟩,⟨0xc2459138b2978,0,0x53020,0x0,0x0,0x0⟩,⟨0xc2444e2ca7ea8,0,0x6000e,0x10200220200002,0x0,0x102201⟩,⟨0xc2459138b28c8,0,0x5301e,0x0,0x0,0x0⟩,⟨0xc2459138b2928,0,0x63020,0x0,0x0,0x0⟩] else #[⟨0xc2459138b2a58,0,0x53020,0x0,0x0,0x0⟩,⟨0xc2459138b2b18,0,0x53020,0x0,0x0,0x0⟩,⟨0xc2459138a7c18,0,0x45017,0x0,0x0,0x1a⟩,⟨0xc2458e2ca7c48,0,0x4b00e,0x0,0x0,0x1a⟩]))) : Array Ticket).getD (i % 8) default
def levm191e4k9 (i : Nat) : Ticket := ((if i < 16 then (if i < 8 then #[⟨0x1bc2459138b2809,0,0x5300e,0x0,0x0,0x0⟩,⟨0x1bc2459138b28f9,0,0x8c068,0x10100420100202,0x0,0x80204⟩,⟨0x1bc2459138b2a69,0,0x68038,0x20000120900002,0x0,0x100205⟩,⟨0x1bc2459138b2b39,0,0x68038,0x20000120900002,0x0,0x100204⟩,⟨0x1bc2459138b28d9,0,0x68027,0x10000420100202,0x0,0x200801⟩,⟨0x1bc2459138b2909,0,0x49009,0x0,0x0,0x1c0b⟩,⟨0x1bc2459138b2949,0,0x83071,0x10900320000202,0x0,0x21a0205c2811⟩,⟨0x6f091138b29c8,0,0x0,0x10000410800310000203,0x186a845de0d8178b05226118803a170401c08015,0x18c5b18a7312c6340078200702004340e6398210847108c201042108436318c730420882c631856384c⟩] else #[⟨0x1bc2459138b29c9,0,0x71053,0x10000410900302,0x0,0x801⟩,⟨0x1bc2459138b2a79,0,0x83068053,0x0,0x0,0xf876381a8746420⟩,⟨0x1bc2459138b2b49,0,0x71053,0x10900301,0x0,0x47221040223⟩,⟨0xc2459138b29d8,0,0x0,0x10100520100220100003,0x9dc39f8f63915c94441d8c84e140701c08014,0x5555559555b55555555b555415555c5c56c5e5adbcb5b5f5558055705532⟩,⟨0x1bc2459138b29d9,0,0x5300e,0x0,0x0,0x0⟩,⟨0x1bc2459138b2a89,0,0x6800e,0x20000120900002,0x0,0x25629940084d⟩,⟨0x1bc2459138b2b59,0,0x5500e,0x0,0x0,0xb859⟩,⟨0x6f091644e2d38,0,0x0,0x20000201,0x186a8270e46b34194c45f1306830014,0x11811117000001100006000000000500400000011111bb1c10030021b9b9191a1⟩]) else (if i < 24 then #[⟨0x1bc2459138b2939,0,0x8c038,0x20000201,0x11,0x0⟩,⟨0x1bc2459138b2959,0,0x6200e,0x0,0x0,0xe26e⟩,⟨0x1bc2459138b2a99,0,0x8300e,0x0,0x0,0x3d1dce85f⟩,⟨0x1bc2459138b2b69,0,0x7103800e,0x20000201,0x0,0x83401f40262⟩,⟨0xc2459138b2a18,0,0x0,0x10100510100320100003,0x141873cde0803d1c8e2180a01c08014,0x444444444644444444644444949494b44a6949316464c4448044704452⟩,⟨0x1bc2459138b2a19,0,0x5100e,0x0,0x0,0x0⟩,⟨0x1bc2459138b29e9,0,0x8c00e,0x20000201,0x0,0x90c01⟩,⟨0x6f091138b2aa8,0,0x0,0x10000220000120800003,0xc3475ec893a1c8ca4d250d43a180381408014,0x1111144c111001114331111b43a394311118444d711116f34eadd4511112e41a11⟩] else (if i < 32 then #[⟨0x1bc2459138b2aa9,0,0x5300e,0x20000120900002,0x0,0x801⟩,⟨0x1bc2459138b2b79,0,0x5300e,0x20000120900002,0x0,0x801⟩,⟨0xc2459138b2828,0,0x0,0x20000520100202,0x873d92a9247a310c721f89c08014,0x222222112322222211421111a2a2a2b2114a4232111918115017161101⟩,⟨0xc2459138b29f8,0,0x0,0x10100320100220100003,0xa84d5a4cc4da611271361a0b856298cc52180701c08015,0x842108469084310842108422c8a21181784842111024090216642457024062709645924421120210e0⟩,⟨0x1bc2459138b2829,0,0x5300e,0x0,0x0,0x0⟩,⟨0x1bc2459138b29f9,0,0x4500e,0x10100420100202,0x0,0x204⟩,⟨0xc2459138b2ab8,0,0x0,0x10100510100320100220000120100005,0x27d117e3d8f472298fc7c3b1b0b04e0d0501c08015,0x8421084a50a821084a529585295a20842129564084214b8a6814ef638ae40c210862508420⟩,⟨0x1bc2459138b2ab9,0,0x5300e,0x0,0x0,0x0⟩] else #[⟨0xc2459138b2b88,0,0x0,0x10100510100320100220000120100005,0x52a82fc7b20d007235970ae47220bc4e0d0501c08015,0x10842100401084212942c085c1094a52b0ab295a20842129544085010bca69153063caf38c2108625⟩,⟨0x1bc2459138b2b89,0,0x5300e,0x20000101,0x0,0x1⟩]))) : Array Ticket).getD (i % 8) default
def levm191e4k10 (i : Nat) : Ticket := (#[⟨0x6f091644e2ca8,0,0x0,0x10000410800320000220000120800005,0x0,0x32810c4012f810b8012c958a650020109a04250108e440381c82071f01c76041c0100e071a81c6407178b00829020981a2305080081d020680e170a01c220d070341604040100a02⟩] : Array Ticket).getD (i % 8) default
def treem191e4 : Book :=
  ⟨false,inputSet 191 [4],goalAt 191,10,7,readRule factsm191e4 recsm191e4,hintsm191e4,9,unpackState wiresm191e4 6,(fun k => match k with | 7 => 9 | 8 => 52 | 9 => 34 | 10 => 1 | _ => 0),fun k => match k with
    | 7 => levm191e4k7
    | 8 => levm191e4k8
    | 9 => levm191e4k9
    | 10 => levm191e4k10
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm191e4 : ∀ i, i < 7 → Valid false (goalAt 191) ((treem191e4).rule i) := by
  exact validateRules factsm191e4 recsm191e4 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k7i0 : bookRange treem191e4 7 0 9 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e4k7 : allGood treem191e4 7 :=
  book_level treem191e4 7 rulesm191e4 (book_empty treem191e4 6 rfl) passm191e4k7i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k8i0 : bookRange treem191e4 8 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k8i16 : bookRange treem191e4 8 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k8i32 : bookRange treem191e4 8 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k8i48 : bookRange treem191e4 8 48 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e4k8 : allGood treem191e4 8 :=
  book_level treem191e4 8 rulesm191e4 goodm191e4k7 (@book_split treem191e4 8 0 32 20 (@book_split treem191e4 8 0 16 16 passm191e4k8i0 passm191e4k8i16) (@book_split treem191e4 8 32 16 4 passm191e4k8i32 passm191e4k8i48))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k9i0 : bookRange treem191e4 9 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k9i16 : bookRange treem191e4 9 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k9i32 : bookRange treem191e4 9 32 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e4k9 : allGood treem191e4 9 :=
  book_level treem191e4 9 rulesm191e4 goodm191e4k8 (@book_split treem191e4 9 0 16 18 passm191e4k9i0 (@book_split treem191e4 9 16 16 2 passm191e4k9i16 passm191e4k9i32))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e4k10i0 : bookRange treem191e4 10 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e4k10 : allGood treem191e4 10 :=
  book_level treem191e4 10 rulesm191e4 goodm191e4k9 passm191e4k10i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm191e4 : Claim false 191 [4] 11 := by
  apply low_search (s:=false) (T:=goalAt 191) (raw:=rawSet 191) (es:=extraSet 191 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 191 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 191 [4]) (extraWord 191 4) = inputSet 191 [] := by decide +kernel
      change Low false (remove (inputSet 191 [4]) (extraWord 191 4)) (goalAt 191) 11
      rw [eq]
      exact claimm191
  · exact book_end treem191e4 goodm191e4k10 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm494e12 : Claim false 494 [12] 11 :=
  rename_rows claimm191e4 [0,4,7,10,45,48,50,24,27,29,54,2,6,9,47,26,34,37,38,55,42,0,36,0,0,0,0,0,0,0,0,0,0,0,16,19,20,53,31,0,18,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm31e12 : Claim false 31 [12] 7 :=
  rename_rows claimm31e4 [0,2,1,3,11,13,12,7,9,8,15,4,6,5,14,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm167e12 : Claim false 167 [12] 7 :=
  rename_rows claimm31e4 [0,2,1,3,16,18,17,34,36,35,41,4,6,5,19,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintsm191e12 (i : Nat) : Nat := ((if i < 80 then (if i < 32 then (if i < 16 then 0x234a920a191a539050c8949c82864464e41431929d20a18c3ce9050c6147482864463a41431831d20a18c18e5050c89eb242864464d21431831c90a18c18e3450c61e712286306389143 else 0xc61d19a18630e20d0c32298a6861913853430c61c29a186a539890c7d2b4848618c3882430c61c29218c18ea080c8d2a4c4063253a62031831d31018c94ea050c60c75028630fa24143) else (if i < 48 then 0xc8a644818630e2240c32298b2061913859030c61c2c818c3e89a30c61e74d18630a3a68c31831d34618c18e9230c3229c690618c3a34830c8a642418630e2120c32298a90618c385483 else (if i < 64 then 0x141913263250e3913188d2a4898c2a95244c6141912263253e82531861f41298c9438e41461419120a30f18e9260d48c99330618f3a69030c8a71c818644e8e40c318747206a4f589903 else 0x1e65099250f94d4c9287986a64943c635324a1e31a71250f3281492879868a4943c634524a1f4d099050f18d4c82835294c29496991414a154a942630a0c8a131929f44c98c9438e64c6))) else (if i < 128 then (if i < 96 then 0x1e51319a60f0c98cd3089ea504180cf26820c074c940a6033c9a05307cb4273143e535398a1e31a9cc50f18d3a6287986a6a143c635350a0c79b3265063cd2532831e6927143e5a1324a else (if i < 112 then 0x1460b41078f4548e8307a24c74183ca263a0c1e1931d06291923a8307864914183c3245a0c074c94466033c9a233019e49d1983d152358c0d4a541c60fa548ce307a2a467183c326338c else 0x1879ab0a8833c9585446142cd41e306166a0f4a30a6d078c2852683c61429141e28c16898f2230b42c78c1859963c6142cc71e1a53a834f0c61d41a786945a0d3c3222ac69e28c16824f)) else (if i < 144 then 0xd4a521d28a3c9a05941d32511a2329a168d1074c8b46883a644e345499446b22a4c923591521c91ac8a99648d44478c6a6a22a65905511527d11a68863cd513441d322c4220e9916151 else (if i < 160 then 0x2328b42d491945916a460c2a8b524461685291430a929486305592a43149a895218c3944a90c50aa254a91924e89549492724aa46493925525129c9286a52a139431e6d09ca1a94a44e5 else 0x12a22ad452951156929)))) >>> (37*(i % 16))) % 137438953472
def wiresm191e12 (i : Nat) : W := bandWord (((if i < 32 then (if i < 16 then (if i < 8 then 0xc60000020000000000c06000008000000000c0028000800000000006028002800000000000628001800000000000048000800000000000028000000000000000020 else 0x408000030000000280578000028000a557a04380000200008447804300000200008447001580000180006336e00180000100004226c00180000100004224c01480000080002112a) else (if i < 24 then 0x1e8000048001297aa00b8000040001087c800a8000040001087a800a0000040001087800578000038000e777e0438000030000c667c040000003000006000042000003000000600 else 0xd80001100044fa4c01c80001080042f92a00c80001000040f82800c00001000040f80005f8000078001ef7fe04b8000070001ce7fc04b00000600018c7f000b80000500014a7cc)) else (if i < 48 then (if i < 40 then 0xd30000220005f44700918000210005f224c0948000208005f112a0908000200005f00280900000200005f000005f8000138004eff7e04f8000130004cfe7c04f00001200048fc70 else 0xc0800037c000000280c0000037c000000000df8000330005ffe7c09c0000300005ff8000db8000270005fe7fc09a0000240005f87800d78000238005f777e0d38000230005f667c) else (if i < 56 then 0xcb800037c0014a7cc0ca000037c001087800d7800037c000e777e0c3800037c000c667c0c3000037c000844700c1800037c0004224c0d4800037c0002112a0c1800037c00000048 else 0xcf800037c004cfe7c0cc000037c0040f8000cb800037c001ce7fc))) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm191e12 (i : Nat) : {f : Fact // Sound false f} := (if i < 3 then (if i < 1 then ⟨item 31 [] 7,claimm31⟩ else (if i < 2 then ⟨item 31 [12] 7,claimm31e12⟩ else ⟨item 167 [] 7,claimm167⟩)) else (if i < 5 then (if i < 4 then ⟨item 167 [12] 7,claimm167e12⟩ else ⟨item 189 [] 8,claimm189⟩) else (if i < 6 then ⟨item 187 [] 7,claimm187⟩ else ⟨item 190 [] 7,claimm190⟩)))
def recsm191e12 (i : Nat) : Recipe := ((if i < 8 then #[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(5,[129])] else #[(5,[321])]) : Array Recipe).getD (i % 8) default
def levm191e12k6 (i : Nat) : Ticket := (#[⟨0x128dc317c777,0,0x0,0x0,0x0,0x9f⟩] : Array Ticket).getD (i % 8) default
def levm191e12k7 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x128dc50ec727,0,0x7e064,0x0,0x0,0x0⟩,⟨0x12ba37083967,0,0xa207e,0x200401,0x0,0x1⟩,⟨0x128dc5083b07,0,0xa007e,0x200401,0x0,0x1⟩,⟨0x4ae8dc5083b78,0,0x0,0x100501,0x0,0x14a00e1a534a⟩,⟨0x12ba370e5d87,0,0xa2083,0x0,0x0,0x0⟩,⟨0xba37142483908,0,0x0,0x100501,0x0,0x6180329⟩,⟨0x4a3714308c778,0,0x0,0x10100801,0x0,0x884053e⟩,⟨0x4ae8dc317c588,0,0x0,0x0,0x0,0x14402⟩] else (if i < 16 then #[⟨0x4a3714317c728,0,0x0,0x0,0x0,0x13e02⟩,⟨0x4a370c257c768,0,0x0,0x0,0x0,0x9602⟩,⟨0x8dc50c248c508,0,0x0,0x10100801,0x0,0x93483e4033e⟩,⟨0x4ae8dc3085f78,0,0x0,0x10100701,0x0,0x89c058f⟩,⟨0x2e70c218aa87,0,0x6e072,0x0,0x0,0x0⟩,⟨0x2370c218db47,0,0x16073,0x0,0x0,0x0⟩,⟨0x2370c232d9a7,0,0x2b098,0x0,0x0,0x0⟩,⟨0x2350c232e617,0,0x4f09b,0x0,0x0,0x0⟩] else #[⟨0xba370c2485d08,0,0x0,0x10100701,0x0,0x990092f1ecf⟩])) : Array Ticket).getD (i % 8) default
def levm191e12k8 (i : Nat) : Ticket := ((if i < 32 then (if i < 16 then (if i < 8 then #[⟨0x4ae8dc5093b18,0,0x7e06d04d,0x0,0x0,0x2⟩,⟨0x4ae8dc5083828,0,0xa207e,0x10200401,0x0,0x41005⟩,⟨0x4ae8dc5092ce8,0,0xa204e,0x0,0x0,0x0⟩,⟨0x4ae8dc5083988,0,0xa2095,0x200401,0x0,0x1ba03a880b⟩,⟨0x4ae8dc5083b28,0,0x7e04d,0x200401,0x0,0x1ea6481602⟩,⟨0x4ae8dc5093978,0,0xa2095087,0x0,0x0,0xe⟩,⟨0x12ba37142483b69,0,0x0,0x0,0x0,0xa504713d4ba02e4cde⟩,⟨0xba37142483a18,0,0xa204d,0x10100601,0x0,0x1⟩] else #[⟨0xba371424838d8,0,0xa207e,0x10200401,0x0,0x1⟩,⟨0xba37142483a88,0,0xa1055,0x10100601,0x0,0x1⟩,⟨0xba37143092138,0,0x4d032,0x0,0x0,0x0⟩,⟨0xba37143092058,0,0x58021,0x0,0x0,0x0⟩,⟨0xba37143092298,0,0x55032,0x20100001,0x0,0x1⟩,⟨0x12ba3714308c589,0,0x0,0x0,0x0,0xa8546017185117414⟩,⟨0x4a3714308c728,0,0x7e04d,0x10000110800002,0x0,0x408bd0d0b42802⟩,⟨0x12ba37143095f19,0,0x0,0x0,0x0,0x9c9c0e8682e81⟩]) else (if i < 24 then #[⟨0x128dc50c248c769,0,0x0,0x0,0x0,0x8110205f21db88528881⟩,⟨0xba371430920f8,0,0x5802c,0x0,0x0,0x0⟩,⟨0xba37143092358,0,0x58032,0x20100001,0x0,0x1⟩,⟨0xba371430920a8,0,0x6c058,0x0,0x0,0x0⟩,⟨0xba37143092158,0,0x97019,0x0,0x0,0x0⟩,⟨0xba371430921d8,0,0x5801c,0x0,0x0,0x0⟩,⟨0xba37143092248,0,0x58021,0x0,0x0,0x0⟩,⟨0xba371430922f8,0,0x58032,0x0,0x0,0x0⟩] else #[⟨0xba37143080588,0,0x9706f,0x200401,0x0,0x1⟩,⟨0xba37143080728,0,0x6f058,0x200401,0x0,0x1⟩,⟨0xba371430921b8,0,0x58032,0x20100201,0x0,0x1⟩,⟨0xba37143092228,0,0x4d032,0x20100201,0x0,0x1⟩,⟨0x4ae8dc50c2378,0,0x6c008,0x10100501,0x0,0x111d28280b⟩,⟨0x4ae8dc3085d88,0,0xa2095,0x10000310800202,0x0,0x3000817070c00223⟩,⟨0x4ae8dc3086198,0,0xa200b,0x0,0x0,0x0⟩,⟨0x4ae8dc30862a8,0,0x96008,0x0,0x0,0x26⟩])) else (if i < 48 then (if i < 40 then #[⟨0x4ae8dc3086368,0,0x6c07d008,0x0,0x0,0x29⟩,⟨0xba37143086288,0,0x95008,0x20100201,0x0,0x4c01⟩,⟨0xba37143086348,0,0x97028,0x20100201,0x0,0x5201⟩,⟨0x4a3714308cb38,0,0x7e00c,0x0,0x0,0x0⟩,⟨0x12ba37143085f29,0,0x0,0x0,0x0,0x588938a230d648002d⟩,⟨0x4a3714308cb68,0,0x9d06c008,0x0,0x0,0x2c⟩,⟨0xba3714308c9a8,0,0x58014,0x20100001,0x0,0x5801⟩,⟨0x4a3714308cb98,0,0x4f00c,0x0,0x0,0x2f⟩] else #[⟨0xba3714308ca18,0,0x4d012,0x20100001,0x0,0x5e01⟩,⟨0xba37143092038,0,0x49018,0x0,0x0,0x0⟩,⟨0x12ba370c2485f69,0,0x0,0x0,0x0,0xcf1921fa2230ee490281⟩,⟨0xba37143092068,0,0x4d032,0x20100201,0x0,0x1⟩,⟨0xba371430922b8,0,0x5802f,0x20100001,0x0,0x1⟩,⟨0xb9c50c248aa88,0,0x94081,0x20100201,0x0,0x4c01⟩,⟨0xba370c248d9a8,0,0x5402f,0x20100001,0x0,0x5801⟩,⟨0xba37143092108,0,0x6c032,0x10100520100220100003,0x0,0xc80207100456204⟩]) else (if i < 56 then #[⟨0xba37143092388,0,0x58032,0x0,0x0,0x0⟩,⟨0x8dc50c248db48,0,0x93032,0x20100201,0x0,0x5201⟩,⟨0xba37143092048,0,0x5801c,0x0,0x0,0x0⟩,⟨0xba350c248b218,0,0x4d05b,0x10100220100002,0x0,0x801⟩,⟨0xba37143092078,0,0x58032,0x20100220100002,0x0,0x801⟩,⟨0xba371430922d8,0,0x5502c,0x10100620100220100003,0x0,0x40807⟩,⟨0xb9c50c248b288,0,0x55081,0x20100210100002,0x0,0x204⟩,⟨0xba350c248e618,0,0x4d05b,0x20100001,0x0,0x5e01⟩] else #[⟨0xba37143092118,0,0x58032,0x20100001,0x0,0x1⟩,⟨0xba371430923a8,0,0x58032,0x20100201,0x0,0x1⟩]))) : Array Ticket).getD (i % 8) default
def levm191e12k9 (i : Nat) : Ticket := ((if i < 16 then (if i < 8 then #[⟨0x4ae8dc50920e8,0,0x0,0x10100401,0x6f2d75f7087434170a0441c0b0401404014,0xbbbbabc090bbbb8bbbbbbdbbe7bebbeeb6cebb5bbbbeb4bb3bc2bbbb1bbcbcb⟩,⟨0x12ba37143092009,0,0x4d02c,0x0,0x0,0x0⟩,⟨0x12ba371430920e9,0,0xa207e,0x10100401,0x0,0x800201⟩,⟨0x12ba37143092259,0,0x4d022,0x0,0x0,0x4c23⟩,⟨0x12ba37143092319,0,0x7e04d,0x20000120900002,0x0,0x11c0d408b15d0c85f41318b05202⟩,⟨0xba37143092018,0,0x0,0x20000610100510100403,0x66e950b813909a4a23910823e1d81c08014,0xaaaaaaea22dadabedd22cadaaa9aaaada8ac22222222272625242220102230⟩,⟨0xba37143092138,0,0x0,0x20100220100002,0x177903914a8137974a6501c09808014,0x66666666676651666666669666416666a6a6a6b68b9a9676c666306620⟩,⟨0x12ba37143092019,0,0x6f04d,0x10100401,0x0,0x1⟩] else #[⟨0x12ba37143092139,0,0x4d02c,0x0,0x0,0x0⟩,⟨0x12ba371430920b9,0,0x5f04d,0x0,0x0,0x20403b⟩,⟨0x4ae8dc50c2188,0,0x0,0x20000320800202,0x1e3a5468d0653117cb8592b128520c0581808015,0x426884c108210842108421084210ac2150421085210a0421084f31444140430840103847708210b9cf⟩,⟨0x12ba37143092189,0,0x9506c,0x20000320900202,0x0,0x801⟩,⟨0x12ba371430921f9,0,0x8804d,0x20000320900202,0x0,0x801⟩,⟨0x12ba37143092269,0,0x6c04d,0x20000120900002,0x0,0x801⟩,⟨0x4ae8dc50c2328,0,0x0,0x20000120800002,0x177a0b90f4773a1c4dc6b2b134580e0601808015,0x210842108400084210884d08581088421b84212c21504221084913c4708501085e27182128430111ce⟩,⟨0x12ba37143092329,0,0x6c04d,0x20000120900002,0x0,0x801⟩]) else (if i < 24 then #[⟨0x12ba37143092279,0,0x7e02c,0x20000120900002,0x0,0x100204⟩,⟨0x12ba37143092339,0,0x7e02c,0x20000120900002,0x0,0x10026b⟩,⟨0x12ba37143092179,0,0xa2095,0x20000320900202,0x0,0xba588100280371645e11281f68245⟩,⟨0x12ba37143092199,0,0x7602c,0x20000320900202,0x0,0x10025c⟩,⟨0x12ba371430922a9,0,0x9502c,0x0,0x0,0x44a19065f⟩,⟨0x12ba37143092369,0,0x6c02c,0x0,0x0,0x12a9247a310071311582b4a190528215⟩,⟨0xba371430921a8,0,0x0,0x10100620000320100220100004,0x57e830552a4918863a1a4b4500501c08014,0x55222222222221229222222225555c57c522222dbcb565e55b4355a05580⟩,⟨0x12ba371430921a9,0,0x4d02c,0x0,0x0,0x0⟩] else (if i < 32 then #[⟨0x12ba371430921e9,0,0x4d01c,0x0,0x0,0xa698⟩,⟨0x12ba37143092209,0,0xa202c,0x20000320900202,0x0,0x100204⟩,⟨0x12ba371430922c9,0,0x4d02c,0x0,0x0,0x522853c9b⟩,⟨0x12ba37143092399,0,0x4d02c,0x0,0x0,0x56aa94e77⟩,⟨0xba37143092218,0,0x0,0x10100620000320100220100004,0xb73c1c8ad53a85367a3194ca2170501c08014,0x5522b229222222222222222221215555d58d5222222eddd575f545d6355c055a0⟩,⟨0x12ba37143092219,0,0x4d02c,0x20000301,0x0,0x1⟩,⟨0xba37143092288,0,0x0,0x10100620100220000120100004,0x1bcbbd05f8a450a250c65319444c1d0501c08015,0x108401004210842c318c73196208421518c6340c6324410842108421699c6405cd684210bcc4334a3⟩,⟨0x12ba37143092289,0,0x4d02c,0x20000101,0x0,0x1⟩] else #[⟨0xba37143092348,0,0x0,0x10100620100220000120100004,0xbbd06170556aa12a92379a0ba380501c08014,0x1111101111555755b2119115555a5558211111111c5e561dac1111f55a43⟩,⟨0x12ba37143092349,0,0x4d02c,0x0,0x0,0x0⟩]))) : Array Ticket).getD (i % 8) default
def levm191e12k10 (i : Nat) : Ticket := (#[⟨0x4ae8dc50c2488,0,0x0,0x10000420000320800220000120800005,0x0,0x32810c4012f810b80102010b20a2b01ca604280109a0a250288e0a2201c82041f010140a1d828700a1a8106404178105829020981423050801a1d068682e1408838080b020200a02⟩] : Array Ticket).getD (i % 8) default
def treem191e12 : Book :=
  ⟨false,inputSet 191 [12],goalAt 191,10,9,readRule factsm191e12 recsm191e12,hintsm191e12,9,unpackState wiresm191e12 6,(fun k => match k with | 6 => 1 | 7 => 17 | 8 => 58 | 9 => 34 | 10 => 1 | _ => 0),fun k => match k with
    | 6 => levm191e12k6
    | 7 => levm191e12k7
    | 8 => levm191e12k8
    | 9 => levm191e12k9
    | 10 => levm191e12k10
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm191e12 : ∀ i, i < 9 → Valid false (goalAt 191) ((treem191e12).rule i) := by
  exact validateRules factsm191e12 recsm191e12 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k6i0 : bookRange treem191e12 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e12k6 : allGood treem191e12 6 :=
  book_level treem191e12 6 rulesm191e12 (book_empty treem191e12 5 rfl) passm191e12k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k7i0 : bookRange treem191e12 7 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k7i16 : bookRange treem191e12 7 16 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e12k7 : allGood treem191e12 7 :=
  book_level treem191e12 7 rulesm191e12 goodm191e12k6 (@book_split treem191e12 7 0 16 1 passm191e12k7i0 passm191e12k7i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k8i0 : bookRange treem191e12 8 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k8i16 : bookRange treem191e12 8 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k8i32 : bookRange treem191e12 8 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k8i48 : bookRange treem191e12 8 48 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e12k8 : allGood treem191e12 8 :=
  book_level treem191e12 8 rulesm191e12 goodm191e12k7 (@book_split treem191e12 8 0 32 26 (@book_split treem191e12 8 0 16 16 passm191e12k8i0 passm191e12k8i16) (@book_split treem191e12 8 32 16 10 passm191e12k8i32 passm191e12k8i48))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k9i0 : bookRange treem191e12 9 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k9i16 : bookRange treem191e12 9 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k9i32 : bookRange treem191e12 9 32 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e12k9 : allGood treem191e12 9 :=
  book_level treem191e12 9 rulesm191e12 goodm191e12k8 (@book_split treem191e12 9 0 16 18 passm191e12k9i0 (@book_split treem191e12 9 16 16 2 passm191e12k9i16 passm191e12k9i32))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm191e12k10i0 : bookRange treem191e12 10 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm191e12k10 : allGood treem191e12 10 :=
  book_level treem191e12 10 rulesm191e12 goodm191e12k9 passm191e12k10i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm191e12 : Claim false 191 [12] 11 := by
  apply low_search (s:=false) (T:=goalAt 191) (raw:=rawSet 191) (es:=extraSet 191 [12])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 191 12] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 191 [12]) (extraWord 191 12) = inputSet 191 [] := by decide +kernel
      change Low false (remove (inputSet 191 [12]) (extraWord 191 12)) (goalAt 191) 11
      rw [eq]
      exact claimm191
  · exact book_end treem191e12 goodm191e12k10 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm313 : Claim false 313 [] 7 :=
  rename_rows claimm31 [0,1,11,12,7,8,15,45,46,51,50,16,17,22,20,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm319 : Claim false 319 [] 11 :=
  rename_rows claimm191 [0,7,11,15,1,8,12,2,9,13,3,4,10,14,5,6,45,50,51,46,47,0,48,0,0,0,0,0,0,0,0,0,0,0,16,20,22,17,18,0,19,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm351 : Claim false 351 [] 11 :=
  rename_rows claimm191 [0,7,4,10,2,9,6,1,8,5,3,11,15,14,13,12,45,50,48,47,46,0,51,0,0,0,0,0,0,0,0,0,0,0,24,29,27,26,25,0,30,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm351e12 : Claim false 351 [12] 11 :=
  rename_rows claimm191e12 [0,7,4,10,2,9,6,1,8,5,3,11,15,14,13,12,45,50,48,47,46,0,51,0,0,0,0,0,0,0,0,0,0,0,24,29,27,26,25,0,30,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm367 : Claim false 367 [] 11 :=
  rename_rows claimm191 [0,45,24,54,2,47,26,1,46,25,3,16,53,31,18,17,7,50,29,9,8,0,20,0,0,0,0,0,0,0,0,0,0,0,4,48,27,6,5,0,19,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm367e12 : Claim false 367 [12] 11 :=
  rename_rows claimm191e4 [0,2,24,26,45,47,54,7,9,29,50,4,6,27,48,10,1,3,25,46,8,0,5,0,0,0,0,0,0,0,0,0,0,0,16,18,31,53,20,0,19,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm379 : Claim false 379 [] 11 :=
  rename_rows claimm191 [0,45,16,53,1,46,17,2,47,18,3,24,54,31,25,26,7,50,20,8,9,0,29,0,0,0,0,0,0,0,0,0,0,0,11,51,22,12,13,0,30,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm431 : Claim false 431 [] 11 :=
  rename_rows claimm191 [0,4,34,37,16,19,41,1,5,35,17,2,6,36,18,3,7,10,38,20,8,0,9,0,0,0,0,0,0,0,0,0,0,0,45,48,55,53,46,0,47,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm445 : Claim false 445 [] 11 :=
  rename_rows claimm191 [0,7,45,50,16,20,53,1,8,46,17,11,15,51,22,12,4,10,48,19,5,0,14,0,0,0,0,0,0,0,0,0,0,0,34,38,55,41,35,0,40,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm487 : Claim false 487 [] 11 :=
  rename_rows claimm191 [0,16,1,17,2,18,3,4,19,5,6,34,41,35,36,37,45,53,46,47,48,0,55,0,0,0,0,0,0,0,0,0,0,0,24,31,25,26,27,0,42,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm487e12 : Claim false 487 [12] 11 :=
  rename_rows claimm191e4 [0,2,1,3,16,18,17,34,36,35,41,4,6,5,19,37,24,26,25,31,42,0,27,0,0,0,0,0,0,0,0,0,0,0,45,47,46,53,55,0,48,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm494 : Claim false 494 [] 11 :=
  rename_rows claimm191 [0,45,7,50,4,48,10,2,47,9,6,24,54,29,27,26,16,53,20,19,18,0,31,0,0,0,0,0,0,0,0,0,0,0,34,55,38,37,36,0,42,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintsm511 (_ : Nat) : Nat := 0
def wiresm511 (i : Nat) : W := bandWord (((if i < 8 then 0x8c07801ffc0000000080c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe00000000000) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm511 (i : Nat) : {f : Fact // Sound false f} := (if i < 3 then (if i < 1 then ⟨item 191 [] 11,claimm191⟩ else (if i < 2 then ⟨item 319 [] 11,claimm319⟩ else ⟨item 351 [] 11,claimm351⟩)) else (if i < 5 then (if i < 4 then ⟨item 367 [] 11,claimm367⟩ else ⟨item 379 [] 11,claimm379⟩) else (if i < 6 then ⟨item 445 [] 11,claimm445⟩ else ⟨item 487 [] 11,claimm487⟩)))
def recsm511 (i : Nat) : Recipe := (#[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])] : Array Recipe).getD (i % 8) default
def levm511k13 (i : Nat) : Ticket := (#[⟨0x8732601549,0,0x0,0x20000620000520000420000320000220000120000007,0x4e0d51c813,0x24900000024049b6db6c00120090129002404ad9002404b692d⟩] : Array Ticket).getD (i % 8) default
def treem511 : Book :=
  ⟨false,inputSet 511 [],goalAt 511,13,7,readRule factsm511 recsm511,hintsm511,5,unpackState wiresm511 4,(fun k => match k with | 13 => 1 | _ => 0),fun k => match k with
    | 13 => levm511k13
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm511 : ∀ i, i < 7 → Valid false (goalAt 511) ((treem511).rule i) := by
  exact validateRules factsm511 recsm511 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm511k13i0 : bookRange treem511 13 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm511k13 : allGood treem511 13 :=
  book_level treem511 13 rulesm511 (book_empty treem511 12 rfl) passm511k13i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511 : Claim false 511 [] 14 := by
  apply low_search (s:=false) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end treem511 goodm511k13 (by decide) (by decide +kernel)
def hintsm511e12 (_ : Nat) : Nat := 0
def wiresm511e12 (i : Nat) : W := bandWord (((if i < 8 then 0x80c618110240c0f800863e1380b21cac667c821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc00000000) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm511e12 (i : Nat) : {f : Fact // Sound false f} := (if i < 7 then (if i < 3 then (if i < 1 then ⟨item 191 [] 11,claimm191⟩ else (if i < 2 then ⟨item 191 [12] 11,claimm191e12⟩ else ⟨item 313 [] 7,claimm313⟩)) else (if i < 5 then (if i < 4 then ⟨item 319 [] 11,claimm319⟩ else ⟨item 351 [] 11,claimm351⟩) else (if i < 6 then ⟨item 351 [12] 11,claimm351e12⟩ else ⟨item 367 [] 11,claimm367⟩))) else (if i < 11 then (if i < 9 then (if i < 8 then ⟨item 367 [12] 11,claimm367e12⟩ else ⟨item 379 [] 11,claimm379⟩) else (if i < 10 then ⟨item 431 [] 11,claimm431⟩ else ⟨item 445 [] 11,claimm445⟩)) else (if i < 13 then (if i < 12 then ⟨item 487 [] 11,claimm487⟩ else ⟨item 487 [12] 11,claimm487e12⟩) else (if i < 14 then ⟨item 494 [] 11,claimm494⟩ else ⟨item 494 [12] 11,claimm494e12⟩))))
def recsm511e12 (i : Nat) : Recipe := ((if i < 8 then #[(0,[]),(0,[133]),(1,[]),(2,[]),(3,[]),(4,[]),(4,[133]),(5,[])] else (if i < 16 then #[(6,[]),(6,[133]),(7,[]),(8,[]),(9,[133]),(10,[]),(11,[]),(11,[133])] else #[(12,[]),(13,[]),(13,[65]),(14,[])])) : Array Recipe).getD (i % 8) default
def levm511e12k13 (i : Nat) : Ticket := (#[⟨0x6983270154a,0,0x0,0x20001320a01120001020000f20a00e20000d20000b20000a20000920a00820000720000620a00520a00450000320000220000120a00012,0x0,0x710704a29634710705629642e2aea0710711329628410710711f29f6471162871164df71f29f29f7071071164c710a28710758a88a1c428a5871162a52ae2b42b4c471162871164eeae22b494a⟩] : Array Ticket).getD (i % 8) default
def treem511e12 : Book :=
  ⟨false,inputSet 511 [12],goalAt 511,13,20,readRule factsm511e12 recsm511e12,hintsm511e12,6,unpackState wiresm511e12 4,(fun k => match k with | 13 => 1 | _ => 0),fun k => match k with
    | 13 => levm511e12k13
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm511e12 : ∀ i, i < 20 → Valid false (goalAt 511) ((treem511e12).rule i) := by
  exact validateRules factsm511e12 recsm511e12 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm511e12k13i0 : bookRange treem511e12 13 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm511e12k13 : allGood treem511e12 13 :=
  book_level treem511e12 13 rulesm511e12 (book_empty treem511e12 12 rfl) passm511e12k13i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e12 : Claim false 511 [12] 14 := by
  apply low_search (s:=false) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [12])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 12] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 511 [12]) (extraWord 511 12) = inputSet 511 [] := by decide +kernel
      change Low false (remove (inputSet 511 [12]) (extraWord 511 12)) (goalAt 511) 14
      rw [eq]
      exact claimm511
  · exact book_end treem511e12 goodm511e12k13 (by decide) (by decide +kernel)
def hintsm511e4 (_ : Nat) : Nat := 0
def wiresm511e4 (i : Nat) : W := bandWord (((if i < 8 then 0x81cf1a590a52c2f92a80c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc00000000) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm511e4 (i : Nat) : {f : Fact // Sound false f} := ⟨item 494 [] 11,claimm494⟩
def recsm511e4 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levm511e4k13 (i : Nat) : Ticket := (#[⟨0x7983260154a,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def treem511e4 : Book :=
  ⟨false,inputSet 511 [4],goalAt 511,13,1,readRule factsm511e4 recsm511e4,hintsm511e4,3,unpackState wiresm511e4 4,(fun k => match k with | 13 => 1 | _ => 0),fun k => match k with
    | 13 => levm511e4k13
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm511e4 : ∀ i, i < 1 → Valid false (goalAt 511) ((treem511e4).rule i) := by
  exact validateRules factsm511e4 recsm511e4 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm511e4k13i0 : bookRange treem511e4 13 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm511e4k13 : allGood treem511e4 13 :=
  book_level treem511e4 13 rulesm511e4 (book_empty treem511e4 12 rfl) passm511e4k13i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4 : Claim false 511 [4] 14 := by
  apply low_search (s:=false) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 511 [4]) (extraWord 511 4) = inputSet 511 [] := by decide +kernel
      change Low false (remove (inputSet 511 [4]) (extraWord 511 4)) (goalAt 511) 14
      rw [eq]
      exact claimm511
  · exact book_end treem511e4 goodm511e4k13 (by decide) (by decide +kernel)
def hintsm511e4e12 (_ : Nat) : Nat := 0
def wiresm511e4e12 (i : Nat) : W := bandWord (((if i < 8 then 0x80c618110240c0f800863e1380b21cac667c821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc0000000081cf1a590a52c2f92a) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm511e4e12 (i : Nat) : {f : Fact // Sound false f} := ⟨item 494 [12] 11,claimm494e12⟩
def recsm511e4e12 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levm511e4e12k13 (i : Nat) : Ticket := (#[⟨0x68a93270154b,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def treem511e4e12 : Book :=
  ⟨false,inputSet 511 [4,12],goalAt 511,13,1,readRule factsm511e4e12 recsm511e4e12,hintsm511e4e12,3,unpackState wiresm511e4e12 4,(fun k => match k with | 13 => 1 | _ => 0),fun k => match k with
    | 13 => levm511e4e12k13
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm511e4e12 : ∀ i, i < 1 → Valid false (goalAt 511) ((treem511e4e12).rule i) := by
  exact validateRules factsm511e4e12 recsm511e4e12 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm511e4e12k13i0 : bookRange treem511e4e12 13 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm511e4e12k13 : allGood treem511e4e12 13 :=
  book_level treem511e4e12 13 rulesm511e4e12 (book_empty treem511e4e12 12 rfl) passm511e4e12k13i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4e12 : Claim false 511 [4,12] 14 := by
  apply low_search (s:=false) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4,12])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4,extraWord 511 12] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · have eq : remove (inputSet 511 [4,12]) (extraWord 511 4) = inputSet 511 [12] := by decide +kernel
      change Low false (remove (inputSet 511 [4,12]) (extraWord 511 4)) (goalAt 511) 14
      rw [eq]
      exact claimm511e12
    · have eq : remove (inputSet 511 [4,12]) (extraWord 511 12) = inputSet 511 [4] := by decide +kernel
      change Low false (remove (inputSet 511 [4,12]) (extraWord 511 12)) (goalAt 511) 14
      rw [eq]
      exact claimm511e4
  · exact book_end treem511e4e12 goodm511e4e12k13 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm313e4 : Claim false 313 [4] 7 :=
  rename_rows claimm31e4 [0,11,7,15,45,51,50,16,22,20,53,1,12,8,46,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm428 : Claim false 428 [] 7 :=
  rename_rows claimm31 [0,4,7,10,45,48,50,16,19,20,53,34,37,38,55,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm413 : Claim false 413 [] 7 :=
  rename_rows claimm187 [0,7,45,50,0,0,0,1,8,46,0,11,15,51,0,12,4,10,48,0,5,0,14,0,0,0,0,0,0,0,0,0,0,0,34,38,55,0,35,0,40,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm437 : Claim false 437 [] 7 :=
  rename_rows claimm187 [0,16,45,53,0,0,0,4,19,48,0,34,41,55,0,37,1,17,46,0,5,0,35,0,0,0,0,0,0,0,0,0,0,0,11,22,51,0,14,0,40,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintsm445e4 (i : Nat) : Nat := ((if i < 64 then (if i < 32 then (if i < 16 then 0x4a6513265253282132929f44c71494fa0838a1f2d199050fd56cc82994bbe04143e9a3020a1f2d181050fd56c082864b42c414ca5dd320a1f2d07105329771482866b9a6294329a1314a else 0x1f2d1bcc50fd56de6287cb467314ca5df098a652d184c50f968c26287cb4273143e5a0e98a1f2d02cc532963166287cb466a14ca5df050a1f2d182850fd56c1429299410a1494fa264ca) else (if i < 48 then 0x1928b31c78c28598e3c66429071e30a14838f65ae19907b232ecc83c5222e641ec8c17320f1460b99078a305a083c5222ac41e28c14e20f1e8a9766625cb79b02929f44d81494fa08c0a else 0x6b2ef72888c9685944464b42c422332ba6ccf1850b36678c2855333c66571199e332148ccf1850a46678cca32283c5222e731e28c17398f4a60ab4c78c9459963c614290b1e32516650f)) else (if i < 96 then (if i < 80 then 0x154a9ba728ac88dd39456aa6e74a2a95373a515911b9d28ac88dc59466b9ad722329a16b91194d0b468b5cb7b9645a999dcb22a4fa2e5916a65172c8a9328b9645499446b22a4ca05591 else 0x4a88ab6f48c2859a8a52eb82d45228c1689a94a88ab4d4a53055a6a48ca2eeb5294c1565292328bba74a9294c3795494a0bbca2a9537c25148a9be128a3d4df094552a5184aa4a5309a5) else (if i < 112 then 0x147919e1ab23c85b0d48e446eb6a94c3aedf26a8ad36f9352939b7c9a9e74dbe44695b7bb21929dbdd90fd56de6c856a9e73642b54f75321faadb9190ad53dc8c85529ee464975c16de9 else 0xca9996df565490b6fab24485b7d47944619ea94c8f3c35))) >>> (37*(i % 16))) % 137438953472
def wiresm445e4 (i : Nat) : W := bandWord (((if i < 16 then (if i < 8 then 0x14a00500600018c5b011e0044048001295a210a00400400010858004200100200008443001400040080012112201400040080002112201c000000000129000000000000000100000 else 0x2900200200005b000015e00d4168005addb211e00c41480052dda205e0094128004add3201c00841080052d92201c00841080042d92200c00801000050d80000c00801000040d800) else (if i < 24 then 0x1ca084036c001085800c0080036c0000000039e02c4348005bdda22de0294328005bdd3229c0284308005bd92229c0280300005bd80039a0240240005b85802d20210220005b4430 else (if i < 32 then 0x31c0ad61080042d92230a0ad6040001085803420ad6020000844303000ad6000000000002dc0a8436c005bd9222d00a0036c005b00001de08c436c0052dda20dc088436c0042d922 else 0x3dc0ad636c0042d9223c00ad636c0000000039c0ad6308005bd9223900ad6200005b000031e0ad61480052dda235e0ad6128004add32))) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm445e4 (i : Nat) : {f : Fact // Sound false f} := (if i < 3 then (if i < 1 then ⟨item 189 [4] 8,claimm189e4⟩ else (if i < 2 then ⟨item 313 [] 7,claimm313⟩ else ⟨item 313 [4] 7,claimm313e4⟩)) else (if i < 5 then (if i < 4 then ⟨item 428 [] 7,claimm428⟩ else ⟨item 189 [] 8,claimm189⟩) else (if i < 6 then ⟨item 413 [] 7,claimm413⟩ else ⟨item 437 [] 7,claimm437⟩)))
def recsm445e4 (i : Nat) : Recipe := ((if i < 8 then #[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(5,[129])] else #[(6,[197]),(6,[201]),(5,[265])]) : Array Recipe).getD (i % 8) default
def levm445e4k7 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x29c5881064118,0,0x0,0x0,0x0,0xf⟩,⟨0x7163c814640c8,0,0x0,0x0,0x0,0xa683c66ba⟩,⟨0xa7161064527,0,0x1005d,0x0,0x0,0x0⟩,⟨0xa7163c51017,0,0x6101d,0x10100301,0x0,0x1⟩,⟨0x7163c51063128,0,0x0,0x0,0x0,0x11aa9c800d02⟩,⟨0x7163c51064988,0,0x0,0x0,0x0,0x1358d150a917⟩,⟨0x1c3c81065d87,0,0x74068,0x0,0x0,0x0⟩,⟨0x1c5850903127,0,0x6a070,0x0,0x0,0x0⟩] else #[⟨0x29c5840915d28,0,0x0,0x0,0x0,0x99⟩,⟨0x70f1440974988,0,0x0,0x0,0x0,0x4cd112108⟩]) : Array Ticket).getD (i % 8) default
def levm445e4k8 (i : Nat) : Ticket := ((if i < 16 then (if i < 8 then #[⟨0xa7163c81441909,0,0x0,0x0,0x0,0xb3e6033e9402⟩,⟨0x29c58f2041918,0,0x57010,0x0,0x0,0xa81002⟩,⟨0x29c58f1441928,0,0x57,0x10000301,0x0,0x88380201a0822940b⟩,⟨0x29c58f2041978,0,0x7306c045,0x0,0x0,0x14⟩,⟨0x7163c814418c8,0,0x60043,0x10100601,0x0,0xe150160401⟩,⟨0x7163c81441988,0,0x60043,0x10100710100602,0x0,0x14088b40801⟩,⟨0x7163c814419f8,0,0x57043,0x10100601,0x0,0x1⟩,⟨0x7163c814408e8,0,0x2401b,0x0,0x0,0x0⟩] else #[⟨0xa7162051024119,0,0x0,0x0,0x0,0x2dc04d8⟩,⟨0x29c5851024128,0,0x6a06f02a,0x0,0x0,0x17⟩,⟨0x7163c81440948,0,0x24014,0x20100101,0x0,0x1⟩,⟨0x7163c814240c8,0,0x38008,0x10100820200302,0x0,0x175b8140801⟩,⟨0x7163c81440a08,0,0x43008,0x10100601,0x0,0x1⟩,⟨0x7163c814274c8,0,0x4300c,0x20200301,0x0,0x1⟩,⟨0x58f20510275f8,0,0x43064,0x20100101,0x0,0x1⟩,⟨0x29c58f2051038,0,0x4301b,0x28100101,0x0,0x1⟩]) else (if i < 24 then #[⟨0x29c58f1440898,0,0x43028,0x28100101,0x0,0x1⟩,⟨0x7163c814408b8,0,0x2401b,0x0,0x0,0x0⟩,⟨0x29c5851024528,0,0x5705b,0x0,0x0,0x4383408⟩,⟨0xa7163c81024579,0,0x0,0x0,0x0,0x2583463⟩,⟨0x7163c81440958,0,0x2401a,0x10100401,0x0,0x1⟩,⟨0x1c58f2051023119,0,0x0,0x10200601,0x0,0x561cb7150042a0c⟩,⟨0x1c58f2051024589,0,0x0,0x10100501,0x0,0x12d2d0e168049654⟩,⟨0x7163c81440a18,0,0x2401b,0x0,0x0,0x0⟩] else (if i < 32 then #[⟨0xa7163c51025d29,0,0x0,0x0,0x0,0x3a72ae068fd41⟩,⟨0x7163c51023128,0,0x8028,0x10200910200502,0x0,0x10e0b8380801⟩,⟨0x7163c51024988,0,0x1b035,0x10100501,0x0,0x1d87044a801⟩,⟨0x7163c510249f8,0,0x57028,0x10100501,0x0,0x1⟩,⟨0x7163c81440a38,0,0x2401b,0x0,0x0,0x0⟩,⟨0x7163c81440998,0,0x24019,0x20100101,0x0,0x1⟩,⟨0x70f2051025d88,0,0x4305a,0x10100a20200302,0x0,0x1d4b0500801⟩,⟨0x7163c814409b8,0,0x2401b,0x0,0x0,0x0⟩] else #[⟨0x7163c81440a58,0,0x4301b,0x10100501,0x0,0x1⟩,⟨0x70f2051029188,0,0x5a01b,0x20200301,0x0,0x1⟩,⟨0x58f20510291f8,0,0x44064,0x20100101,0x0,0x1⟩]))) : Array Ticket).getD (i % 8) default
def levm445e4k9 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x29c58f2051068,0,0x0,0x20000301,0x7fbc19ec30a0441c0b0401404014,0x700600000005000008889884b89800000030000000088a8288881888a8a8aa⟩,⟨0xa7163c81440879,0,0x4302d,0x30100301,0x0,0x2e01⟩,⟨0xa7163c81440909,0,0x6b038,0x30100320000202,0x0,0x34cf84620020043a1a49aac0202⟩,⟨0xa7163c814409d9,0,0x43038,0x30100301,0x0,0x160a44c01⟩,⟨0xa7163c81440809,0,0x4301b,0x0,0x0,0xd4642f⟩,⟨0xa7163c81440919,0,0x57,0x30100310100002,0x0,0x110d241348f808011d92c96380d24d5605⟩,⟨0xa7163c814409e9,0,0x4301d,0x30100301,0x0,0x8e01⟩,⟨0x29c58f1440928,0,0x0,0x20000301,0x2047e36150a6502692c94391c07410014,0x900800000007000004444544444a4d436ab46bb42bc4400000000010000044⟩] else (if i < 16 then #[⟨0xa7163c81440a29,0,0x4601b,0x30100301,0x0,0xac01⟩,⟨0xa7163c81440979,0,0x73043,0x30100320000202,0x0,0x2e1a6b85902004943b0082c9645⟩,⟨0xa7163c814409a9,0,0x4201b,0x30100301,0x0,0xbe01⟩,⟨0xa7163c81440a49,0,0x4301b,0x30100301,0x0,0x34194c401⟩,⟨0x7163c814408c8,0,0x0,0x10100610100510100420000220100105,0x11d632ac9a411489846200b8381a0a0481c08015,0x210842118c630846368de10846e1b0610ac210852108c6108c701982118d420842018d041bce5⟩,⟨0x7163c814408d8,0,0x0,0x10100510100420100103,0x8131962692c9208e3e0b81c08014,0x6666866670666666666aa6668686866886886830666666b69666516642⟩,⟨0x7163c81440938,0,0x0,0x10100610100420100103,0x204c6571a4be562a1207c391001c08014,0x4444a444904444444467c44474a46752a46aa4aa4430444444d4b44481⟩,⟨0x7163c81440988,0,0x0,0x10100610100510100420000220100105,0x8e994c45f2e164a85024110220d0501c08014,0x11e1111b7777117787911179767111111111110771177f751177d277c379a4⟩] else #[⟨0x7163c814409f8,0,0x0,0x10100610100520100103,0x204c655a10d0622b150a648238b04c150a01c08015,0x84690902108c0108422c24210842250a8108451224240e2710c87388e79085010842109120dc4⟩])) : Array Ticket).getD (i % 8) default
def levm445e4k10 (i : Nat) : Ticket := (#[⟨0x29c58f2051028,0,0x0,0x30000320000220800110000004,0x32178b05226118803a1a0b850220e0582810070281004015,0x181401893118d2318d13189013c0e2348c01806218cb318c43280941c042148321806218c6304c4⟩] : Array Ticket).getD (i % 8) default
def treem445e4 : Book :=
  ⟨false,inputSet 445 [4],goalAt 445,10,11,readRule factsm445e4 recsm445e4,hintsm445e4,9,unpackState wiresm445e4 6,(fun k => match k with | 7 => 10 | 8 => 35 | 9 => 17 | 10 => 1 | _ => 0),fun k => match k with
    | 7 => levm445e4k7
    | 8 => levm445e4k8
    | 9 => levm445e4k9
    | 10 => levm445e4k10
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm445e4 : ∀ i, i < 11 → Valid false (goalAt 445) ((treem445e4).rule i) := by
  exact validateRules factsm445e4 recsm445e4 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm445e4k7i0 : bookRange treem445e4 7 0 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm445e4k7 : allGood treem445e4 7 :=
  book_level treem445e4 7 rulesm445e4 (book_empty treem445e4 6 rfl) passm445e4k7i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm445e4k8i0 : bookRange treem445e4 8 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm445e4k8i16 : bookRange treem445e4 8 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm445e4k8i32 : bookRange treem445e4 8 32 3 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm445e4k8 : allGood treem445e4 8 :=
  book_level treem445e4 8 rulesm445e4 goodm445e4k7 (@book_split treem445e4 8 0 16 19 passm445e4k8i0 (@book_split treem445e4 8 16 16 3 passm445e4k8i16 passm445e4k8i32))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm445e4k9i0 : bookRange treem445e4 9 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm445e4k9i16 : bookRange treem445e4 9 16 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm445e4k9 : allGood treem445e4 9 :=
  book_level treem445e4 9 rulesm445e4 goodm445e4k8 (@book_split treem445e4 9 0 16 1 passm445e4k9i0 passm445e4k9i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm445e4k10i0 : bookRange treem445e4 10 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm445e4k10 : allGood treem445e4 10 :=
  book_level treem445e4 10 rulesm445e4 goodm445e4k9 passm445e4k10i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm445e4 : Claim false 445 [4] 11 := by
  apply low_search (s:=false) (T:=goalAt 445) (raw:=rawSet 445) (es:=extraSet 445 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 445 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 445 [4]) (extraWord 445 4) = inputSet 445 [] := by decide +kernel
      change Low false (remove (inputSet 445 [4]) (extraWord 445 4)) (goalAt 445) 11
      rw [eq]
      exact claimm445
  · exact book_end treem445e4 goodm445e4k10 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e16 : Claim false 511 [16] 14 :=
  rename_rows claimm511e4 [0,2,1,3,16,18,17,45,47,46,53,24,26,25,31,54,4,6,5,19,48,49,27,28,11,13,12,22,23,51,30,14,52,33,34,36,35,41,55,56,42,37,40,57,44,7,9,8,20,21,50,29,32,10,15,38,39,43,58] (by decide +kernel)
def hintsm511e4e16 (_ : Nat) : Nat := 0
def wiresm511e4e16 (i : Nat) : W := bandWord (((if i < 8 then 0xc21e409c93ffa4224c80c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc0000000081cf1a590a52c2f92a) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm511e4e16 (i : Nat) : {f : Fact // Sound false f} := ⟨item 445 [4] 11,claimm445e4⟩
def recsm511e4e16 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levm511e4e16k13 (i : Nat) : Ticket := (#[⟨0x78a93260154b,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def treem511e4e16 : Book :=
  ⟨false,inputSet 511 [4,16],goalAt 511,13,1,readRule factsm511e4e16 recsm511e4e16,hintsm511e4e16,3,unpackState wiresm511e4e16 4,(fun k => match k with | 13 => 1 | _ => 0),fun k => match k with
    | 13 => levm511e4e16k13
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm511e4e16 : ∀ i, i < 1 → Valid false (goalAt 511) ((treem511e4e16).rule i) := by
  exact validateRules factsm511e4e16 recsm511e4e16 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm511e4e16k13i0 : bookRange treem511e4e16 13 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm511e4e16k13 : allGood treem511e4e16 13 :=
  book_level treem511e4e16 13 rulesm511e4e16 (book_empty treem511e4e16 12 rfl) passm511e4e16k13i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4e16 : Claim false 511 [4,16] 14 := by
  apply low_search (s:=false) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4,16])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4,extraWord 511 16] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · have eq : remove (inputSet 511 [4,16]) (extraWord 511 4) = inputSet 511 [16] := by decide +kernel
      change Low false (remove (inputSet 511 [4,16]) (extraWord 511 4)) (goalAt 511) 14
      rw [eq]
      exact claimm511e16
    · have eq : remove (inputSet 511 [4,16]) (extraWord 511 16) = inputSet 511 [4] := by decide +kernel
      change Low false (remove (inputSet 511 [4,16]) (extraWord 511 16)) (goalAt 511) 14
      rw [eq]
      exact claimm511e4
  · exact book_end treem511e4e16 goodm511e4e16k13 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm494e23 : Claim false 494 [23] 11 :=
  rename_rows claimm191e12 [0,45,7,50,4,48,10,34,55,38,37,16,53,20,19,41,24,54,29,27,42,0,31,0,0,0,0,0,0,0,0,0,0,0,2,47,9,6,36,0,18,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e23 : Claim false 511 [23] 14 :=
  rename_rows claimm511e12 [0,45,7,50,4,48,10,2,47,9,6,24,54,29,27,26,16,53,20,19,18,21,31,32,11,51,15,14,52,13,30,22,23,33,34,55,38,37,36,39,42,41,40,57,44,1,46,8,5,49,3,25,28,17,12,35,56,43,58] (by decide +kernel)
def hintsm511e4e23 (_ : Nat) : Nat := 0
def wiresm511e4e23 (i : Nat) : W := bandWord (((if i < 8 then 0x80c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000094b41708e33838c7f084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc0000000081cf1a590a52c2f92a) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm511e4e23 (i : Nat) : {f : Fact // Sound false f} := ⟨item 494 [23] 11,claimm494e23⟩
def recsm511e4e23 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levm511e4e23k13 (i : Nat) : Ticket := (#[⟨0x28a94370165b,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def treem511e4e23 : Book :=
  ⟨false,inputSet 511 [4,23],goalAt 511,13,1,readRule factsm511e4e23 recsm511e4e23,hintsm511e4e23,3,unpackState wiresm511e4e23 4,(fun k => match k with | 13 => 1 | _ => 0),fun k => match k with
    | 13 => levm511e4e23k13
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm511e4e23 : ∀ i, i < 1 → Valid false (goalAt 511) ((treem511e4e23).rule i) := by
  exact validateRules factsm511e4e23 recsm511e4e23 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm511e4e23k13i0 : bookRange treem511e4e23 13 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm511e4e23k13 : allGood treem511e4e23 13 :=
  book_level treem511e4e23 13 rulesm511e4e23 (book_empty treem511e4e23 12 rfl) passm511e4e23k13i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4e23 : Claim false 511 [4,23] 14 := by
  apply low_search (s:=false) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4,23])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4,extraWord 511 23] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · have eq : remove (inputSet 511 [4,23]) (extraWord 511 4) = inputSet 511 [23] := by decide +kernel
      change Low false (remove (inputSet 511 [4,23]) (extraWord 511 4)) (goalAt 511) 14
      rw [eq]
      exact claimm511e23
    · have eq : remove (inputSet 511 [4,23]) (extraWord 511 23) = inputSet 511 [4] := by decide +kernel
      change Low false (remove (inputSet 511 [4,23]) (extraWord 511 23)) (goalAt 511) 14
      rw [eq]
      exact claimm511e4
  · exact book_end treem511e4e23 goodm511e4e23k13 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm379e4 : Claim false 379 [4] 11 :=
  rename_rows claimm191e4 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,0,13,0,0,0,0,0,0,0,0,0,0,0,24,25,31,54,29,0,30,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e27 : Claim false 511 [27] 14 :=
  rename_rows claimm511e4 [0,4,7,10,45,48,50,16,19,20,53,34,37,38,55,41,2,6,9,47,18,21,36,39,11,14,15,51,52,22,40,13,23,57,24,27,29,54,31,32,42,26,30,33,44,1,5,8,46,49,17,35,56,3,12,25,28,43,58] (by decide +kernel)
def hintsm511e4e27 (_ : Nat) : Nat := 0
def wiresm511e4e27 (i : Nat) : W := bandWord (((if i < 8 then 0x81cf1a590a52c2f92a80c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c37931ffe180844708c07801ffc00000000) >>> (72*(i % 8))) % 4722366482869645213696)
def factsm511e4e27 (i : Nat) : {f : Fact // Sound false f} := ⟨item 379 [4] 11,claimm379e4⟩
def recsm511e4e27 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levm511e4e27k13 (i : Nat) : Ticket := (#[⟨0x97a83260154b,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def treem511e4e27 : Book :=
  ⟨false,inputSet 511 [4,27],goalAt 511,13,1,readRule factsm511e4e27 recsm511e4e27,hintsm511e4e27,3,unpackState wiresm511e4e27 4,(fun k => match k with | 13 => 1 | _ => 0),fun k => match k with
    | 13 => levm511e4e27k13
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rulesm511e4e27 : ∀ i, i < 1 → Valid false (goalAt 511) ((treem511e4e27).rule i) := by
  exact validateRules factsm511e4e27 recsm511e4e27 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passm511e4e27k13i0 : bookRange treem511e4e27 13 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goodm511e4e27k13 : allGood treem511e4e27 13 :=
  book_level treem511e4e27 13 rulesm511e4e27 (book_empty treem511e4e27 12 rfl) passm511e4e27k13i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4e27 : Claim false 511 [4,27] 14 := by
  apply low_search (s:=false) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4,27])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4,extraWord 511 27] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · have eq : remove (inputSet 511 [4,27]) (extraWord 511 4) = inputSet 511 [27] := by decide +kernel
      change Low false (remove (inputSet 511 [4,27]) (extraWord 511 4)) (goalAt 511) 14
      rw [eq]
      exact claimm511e27
    · have eq : remove (inputSet 511 [4,27]) (extraWord 511 27) = inputSet 511 [4] := by decide +kernel
      change Low false (remove (inputSet 511 [4,27]) (extraWord 511 27)) (goalAt 511) 14
      rw [eq]
      exact claimm511e4
  · exact book_end treem511e4e27 goodm511e4e27k13 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4e38 : Claim false 511 [4,38] 14 :=
  rename_rows claimm511e4e23 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4e57 : Claim false 511 [4,57] 14 :=
  rename_rows claimm511e4e16 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4e58 : Claim false 511 [4,58] 14 :=
  rename_rows claimm511e4e12 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claimm511e4e68 : Claim false 511 [4,68] 14 :=
  rename_rows claimm511e4e27 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
def hintss15 (_ : Nat) : Nat := 0
def wiress15 (i : Nat) : W := bandWord ((0x200000000000078000300000000000047000180000000000024c00080000000000012a >>> (72*(i % 8))) % 4722366482869645213696)
def levs15k3 (i : Nat) : Ticket := (#[⟨0xe44,0,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def trees15 : Book :=
  ⟨true,inputSet 15 [],goalAt 15,3,0,(fun _ => default),hintss15,3,unpackState wiress15 2,(fun k => match k with | 3 => 1 | _ => 0),fun k => match k with
    | 3 => levs15k3
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless15 : ∀ i, i < 0 → Valid true (goalAt 15) ((trees15).rule i) := by
  intro i hi
  omega
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs15k3i0 : bookRange trees15 3 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods15k3 : allGood trees15 3 :=
  book_level trees15 3 ruless15 (book_empty trees15 2 rfl) passs15k3i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims15 : Claim true 15 [] 4 := by
  apply low_search (s:=true) (T:=goalAt 15) (raw:=rawSet 15) (es:=extraSet 15 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end trees15 goods15k3 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims23 : Claim true 23 [] 4 :=
  rename_rows claims15 [0,4,2,6,1,5,3,11,14,13,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims27 : Claim true 27 [] 4 :=
  rename_rows claims15 [0,2,1,3,11,13,12,7,9,8,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims29 : Claim true 29 [] 4 :=
  rename_rows claims15 [0,1,11,12,7,8,15,4,5,14,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims30 : Claim true 30 [] 4 :=
  rename_rows claims15 [0,2,4,6,7,9,10,11,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintss31 (i : Nat) : Nat := ((if i < 16 then 0x8001279c30a3c734e1879438870c3030423868000a61a30a3c73841819809c10c0ca0440868000a5121862842090c50c2044863cc2c12438001a79018c3cb2480c31421210630f2c9043 else (if i < 32 then 0x1478e59c64000828e303061027183ca1ce2cc1e1840966031823853200068c2980c608e04c8001c61050c3cb1c82879858a4140c608420a1e61640e5400090c52830611021418f08710a else 0x660259a7862841cd3e00040669e30304d2cf185023967c000e1893c50c21a39e28c04b1cf)) >>> (37*(i % 16))) % 137438953472
def wiress31 (i : Nat) : W := bandWord (((if i < 16 then (if i < 8 then 0x180000000000204c00780000000000157a00480000000000112a00480000000000110a00480000000000102a0028000000000007aa00300000000000047000180000000000024c else 0x380000000000667c00780000000000557a00600000000000553200780000000000547a00300000000000447000300000000000445000580000000000336e00180000000000224c) else (if i < 24 then 0xe8000000000097aa00e80000000000978a00e8000000000095aa00b8000000000087cc00a00000000000878000a00000000000868000a000000000008580005000000000007870 else (if i < 32 then 0xf00000000000dc7000c00000000000d80000b00000000000c7f000d80000000000ba4c00c00000000000b80000b80000000000a7cc00b80000000000a6cc00880000000000a38c else 0xe00000000000ff8000f00000000000fc7000f00000000000fc5000d80000000000fa4c00c80000000000f92a00d80000000000f84c00c00000000000f80000900000000000ea44))) >>> (72*(i % 8))) % 4722366482869645213696)
def factss31 (i : Nat) : {f : Fact // Sound true f} := (if i < 2 then (if i < 1 then ⟨item 15 [] 4,claims15⟩ else ⟨item 23 [] 4,claims23⟩) else (if i < 3 then ⟨item 27 [] 4,claims27⟩ else (if i < 4 then ⟨item 29 [] 4,claims29⟩ else ⟨item 30 [] 4,claims30⟩)))
def recss31 (i : Nat) : Recipe := (#[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])] : Array Recipe).getD (i % 8) default
def levs31k4 (i : Nat) : Ticket := ((if i < 24 then (if i < 8 then #[⟨0x212c80da5,0,0x0,0x0,0x0,0x75⟩,⟨0x214cb0c05,0,0x0,0x0,0x0,0x0⟩,⟨0x132c80de5,0,0x0,0x0,0x0,0x6c⟩,⟨0x214cb20c5,0,0x0,0x0,0x0,0x5d⟩,⟨0x214c80c15,0,0x0,0x0,0x0,0x3f⟩,⟨0x132c80db5,0,0x0,0x0,0x0,0x54⟩,⟨0x212c81595,0,0x0,0x0,0x0,0x75⟩,⟨0x212c54805,0,0x0,0x0,0x0,0x6⟩] else (if i < 16 then #[⟨0xb20549e5,0,0x0,0x0,0x0,0x6c⟩,⟨0x212c83925,0,0x0,0x0,0x0,0x60⟩,⟨0x212054815,0,0x0,0x0,0x0,0x39⟩,⟨0xb20549b5,0,0x0,0x0,0x0,0x54⟩,⟨0x212c55c75,0,0x0,0x0,0x0,0x18⟩,⟨0x214c82975,0,0x0,0x0,0x0,0xf⟩,⟨0x132c81425,0,0x0,0x0,0x0,0x0⟩,⟨0x214cb1625,0,0x0,0x0,0x0,0x27⟩] else #[⟨0x214c52875,0,0x0,0x0,0x0,0x3⟩,⟨0x214cb1075,0,0x0,0x0,0x0,0x3⟩,⟨0x214c51c15,0,0x0,0x0,0x0,0x1e⟩,⟨0x132c51db5,0,0x0,0x0,0x0,0x2a⟩,⟨0x212c81555,0,0x0,0x0,0x0,0x3c⟩,⟨0x212c54645,0,0x0,0x0,0x0,0x27⟩,⟨0x212052915,0,0x0,0x0,0x0,0x33⟩,⟨0x212c81115,0,0x0,0x0,0x0,0x12⟩])) else (if i < 32 then #[⟨0x212054415,0,0x0,0x0,0x0,0x1e⟩,⟨0xb20545b5,0,0x0,0x0,0x0,0x63⟩,⟨0x132c569e5,0,0x0,0x0,0x0,0x51⟩,⟨0x214c81585,0,0x0,0x0,0x0,0x0⟩,⟨0x214cb1545,0,0x0,0x0,0x0,0xc⟩,⟨0x214c52805,0,0x0,0x0,0x0,0x1b⟩,⟨0x214cb1005,0,0x0,0x0,0x0,0x1b⟩,⟨0x132c50265,0,0x0,0x0,0x0,0x57⟩] else (if i < 40 then #[⟨0x132c815f5,0,0x0,0x0,0x0,0x57⟩,⟨0x1320529e5,0,0x0,0x0,0x0,0x4e⟩,⟨0x132c811e5,0,0x0,0x0,0x0,0x48⟩,⟨0x214cb2205,0,0x0,0x0,0x0,0x0⟩,⟨0x132059015,0,0x0,0x0,0x0,0x30⟩,⟨0x214c81655,0,0x0,0x0,0x0,0x24⟩,⟨0x214cb2165,0,0x0,0x0,0x0,0xf⟩,⟨0x214c81265,0,0x0,0x0,0x0,0x24⟩] else #[⟨0x214cb14d5,0,0x0,0x0,0x0,0x0⟩,⟨0x1320539b5,0,0x0,0x0,0x0,0x69⟩,⟨0x214c81465,0,0x0,0x0,0x0,0x42⟩,⟨0x132c815c5,0,0x0,0x0,0x0,0x72⟩,⟨0x212c81505,0,0x0,0x0,0x0,0x0⟩]))) : Array Ticket).getD (i % 8) default
def levs31k5 (i : Nat) : Ticket := ((if i < 16 then (if i < 8 then #[⟨0x214cb2175,0,0x13,0x10000101,0x11,0x0⟩,⟨0x214cb2035,0,0x0,0x10000410000102,0x0,0x11210e21040b0404082d052d010201010401⟩,⟨0x212c81575,0,0x8,0x10000400000102,0x0,0x40401⟩,⟨0x212c81525,0,0x0,0x10000410000102,0x0,0x23212021041d04041a2d172d011401010401⟩,⟨0x8532c81576,0,0x0,0x10100001,0x0,0x2c0129261515⟩,⟨0x8532c81636,0,0x0,0x10100201,0x0,0x15a6615⟩,⟨0x8532c81496,0,0x0,0x10100101,0x0,0x5a2d0115⟩,⟨0x8532c814f6,0,0x0,0x10100001,0x0,0x4509012d⟩] else #[⟨0x214cb15a5,0,0x26,0x10000101,0x11,0x0⟩,⟨0x214cb1475,0,0x0,0x10000310000102,0x0,0x3b21382135453245012601010404042f0401⟩,⟨0x212c815a5,0,0x4,0x10000300000102,0x0,0x40401⟩,⟨0x212c81515,0,0x0,0x10000310000102,0x0,0x4d214a2147454445040404410401013e0101⟩,⟨0x8532c815a6,0,0x0,0x10100201,0x0,0x530150090902⟩,⟨0x214cb1645,0,0x23,0x10000001,0x11,0x0⟩,⟨0x214cb1405,0,0x0,0x10000310000002,0x0,0x15f01015c45594517150515040104040456⟩,⟨0x132c81645,0,0x10,0x10000300000002,0x0,0x40401⟩]) else (if i < 24 then #[⟨0x132c815e5,0,0x0,0x10000310000002,0x0,0x68456545016201010404045004011a150815⟩,⟨0x8532c81646,0,0x0,0x10100401,0x0,0x6e2d2d416b01⟩,⟨0x214c814e5,0,0x1f,0x10000400000202,0x0,0x40401⟩,⟨0x214c814a5,0,0x0,0x10000410000202,0x0,0x652d592d4409320904040429010101710104⟩,⟨0x214cb20e5,0,0x18,0x10000201,0x11,0x0⟩,⟨0x214cb2045,0,0x0,0x10000410000202,0x0,0x10101770104682d5c2d4709350904040474⟩,⟨0x8532c814e6,0,0x0,0x10100301,0x0,0x7d45457a011d⟩,⟨0x8532c815d6,0,0x0,0x10100401,0x0,0x216f0145⟩] else #[⟨0x214c81665,0,0x1a,0x10000001,0x11,0x0⟩,⟨0x214c81415,0,0x0,0x10000210000002,0x0,0x16e01014a09380920150e15040104040480⟩,⟨0x132c81665,0,0xc,0x10000200000002,0x0,0x40401⟩,⟨0x132c815b5,0,0x0,0x10000210000002,0x0,0x404047d04014d093b090183010123151115⟩,⟨0x8532c81666,0,0x0,0x10100101,0x0,0x86012121775f⟩,⟨0x8532c81676,0,0x0,0x10100301,0x0,0x4b016f36⟩])) : Array Ticket).getD (i % 8) default
def levs31k6 (i : Nat) : Ticket := (#[⟨0x214cb2055,0,0x0,0x10000410000310000210000110000005,0x0,0x10459010107560153504d4a040747040d074407413e3b38010a3501322f2c29040a260423201d1a070a17070d0a140a010d1101040d0e040b080502⟩] : Array Ticket).getD (i % 8) default
def trees31 : Book :=
  ⟨true,inputSet 31 [],goalAt 31,6,5,readRule factss31 recss31,hintss31,8,unpackState wiress31 6,(fun k => match k with | 4 => 45 | 5 => 30 | 6 => 1 | _ => 0),fun k => match k with
    | 4 => levs31k4
    | 5 => levs31k5
    | 6 => levs31k6
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless31 : ∀ i, i < 5 → Valid true (goalAt 31) ((trees31).rule i) := by
  exact validateRules factss31 recss31 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31k4i0 : bookRange trees31 4 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31k4i16 : bookRange trees31 4 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31k4i32 : bookRange trees31 4 32 13 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods31k4 : allGood trees31 4 :=
  book_level trees31 4 ruless31 (book_empty trees31 3 rfl) (@book_split trees31 4 0 16 29 passs31k4i0 (@book_split trees31 4 16 16 13 passs31k4i16 passs31k4i32))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31k5i0 : bookRange trees31 5 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31k5i16 : bookRange trees31 5 16 14 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods31k5 : allGood trees31 5 :=
  book_level trees31 5 ruless31 goods31k4 (@book_split trees31 5 0 16 14 passs31k5i0 passs31k5i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31k6i0 : bookRange trees31 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods31k6 : allGood trees31 6 :=
  book_level trees31 6 ruless31 goods31k5 passs31k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims31 : Claim true 31 [] 7 := by
  apply low_search (s:=true) (T:=goalAt 31) (raw:=rawSet 31) (es:=extraSet 31 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end trees31 goods31k6 (by decide) (by decide +kernel)
def hintss31e4 (i : Nat) : Nat := ((if i < 32 then (if i < 16 then 0x67822043033011021819408810d0003830868001a18430628420e0e00041e68618a1083438000a5121c000e1890e00069e40628610e203143086901c000d3080e00041410700034c043 else 0x1e61640e50f30b1072a00048629418308910a0c1844085063c21c42a00049e70c3ca1c43861818211c34000530d1851e39c20c2830421060660270434000e3021a00041810d00014c086) else (if i < 48 then 0x143086907c000d0c83e00041471818a10538c8000219a6400083cb3200021441900034620c8001a1906031823853200068c29900034304c8001c61050c3cb1c82879858a4140c608420a else 0x200040669f00038624f)) >>> (37*(i % 16))) % 137438953472
def wiress31e4 (i : Nat) : W := bandWord (((if i < 16 then (if i < 8 then 0x780000000000157a00480000000000112a00480000000000110a00480000000000102a0028000000000007aa00300000000000047000300000000000045000180000000000024c else 0xa00000000000858000580000000000787a00480000000000782a00780000000000557a00300000000000447000300000000000445000180000000000224c00180000000000204c) else (if i < 24 then 0xd80000000000ba4c00c80000000000b90a00c00000000000b80000e8000000000097aa00e80000000000978a00e8000000000095aa00a00000000000878000a000000000008680 else (if i < 32 then 0xd80000000000fa4c00c80000000000f92a00d80000000000f84c00c00000000000f80000900000000000ea4400e00000000000dd3200c00000000000d92200c00000000000d800 else 0xe80000000000ffaa00f80000000000fd7a00f00000000000fc7000f00000000000fc5000d80000000000fb6e))) >>> (72*(i % 8))) % 4722366482869645213696)
def factss31e4 (i : Nat) : {f : Fact // Sound true f} := (if i < 2 then (if i < 1 then ⟨item 15 [] 4,claims15⟩ else ⟨item 23 [] 4,claims23⟩) else (if i < 3 then ⟨item 27 [] 4,claims27⟩ else (if i < 4 then ⟨item 29 [] 4,claims29⟩ else ⟨item 30 [] 4,claims30⟩)))
def recss31e4 (i : Nat) : Recipe := (#[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])] : Array Recipe).getD (i % 8) default
def levs31e4k4 (i : Nat) : Ticket := ((if i < 16 then (if i < 8 then #[⟨0x78b51f4,0,0x4007,0x0,0x0,0x0⟩,⟨0x1e7095235,0,0x0,0x0,0x0,0x330c⟩,⟨0x1e7095015,0,0x0,0x0,0x0,0xc2d⟩,⟨0x1e70b5085,0,0x0,0x0,0x0,0x2709⟩,⟨0x1c4495015,0,0x0,0x0,0x0,0x3c⟩,⟨0x1c4491015,0,0x0,0x0,0x0,0x63⟩,⟨0x1e7093145,0,0x0,0x0,0x0,0xc33⟩,⟨0x1e7092945,0,0x0,0x0,0x0,0x92d⟩] else #[⟨0x1c2465015,0,0x0,0x0,0x0,0x0⟩,⟨0x1c2464015,0,0x0,0x0,0x0,0x5d⟩,⟨0x1e44b19d5,0,0x0,0x0,0x0,0x4818⟩,⟨0x1c4462015,0,0x0,0x0,0x0,0x543f⟩,⟨0x1e70b2525,0,0x0,0x0,0x0,0x6009⟩,⟨0x1e2c63df5,0,0x0,0x0,0x0,0x4818⟩,⟨0x1c2463c15,0,0x0,0x0,0x0,0x3f51⟩,⟨0x1e4467e35,0,0x0,0x0,0x0,0x1e24⟩]) else (if i < 24 then #[⟨0x1e4467c15,0,0x0,0x0,0x0,0x1e5a⟩,⟨0x1e4467e25,0,0x0,0x0,0x0,0x8424⟩,⟨0x1e4467c25,0,0x0,0x0,0x0,0x1e5a⟩,⟨0x1c4467c15,0,0x0,0x0,0x0,0x0⟩,⟨0x1c4460015,0,0x0,0x0,0x0,0x39⟩,⟨0x112467c15,0,0x0,0x0,0x0,0x4e⟩,⟨0x112466015,0,0x0,0x0,0x0,0x72⟩,⟨0x1c44b25b5,0,0x0,0x0,0x0,0x0⟩] else #[⟨0x1e70b2535,0,0x0,0x0,0x0,0x2d09⟩,⟨0x1e44b1975,0,0x0,0x0,0x0,0x5a18⟩,⟨0x1c4491875,0,0x0,0x0,0x0,0x66⟩,⟨0x1c4491a15,0,0x0,0x0,0x0,0x45⟩,⟨0x1c44b19a5,0,0x0,0x0,0x0,0x0⟩,⟨0x1c2c918e5,0,0x0,0x0,0x0,0x0⟩,⟨0x112c91835,0,0x0,0x0,0x0,0x0⟩])) : Array Ticket).getD (i % 8) default
def levs31e4k5 (i : Nat) : Ticket := ((if i < 16 then (if i < 8 then #[⟨0x1e70b2545,0,0x8,0x401,0x0,0x1080502⟩,⟨0x79c44b2546,0,0x0,0x10100001,0x0,0x115150e900b⟩,⟨0x79c44b2446,0,0x0,0x0,0x0,0x118d15⟩,⟨0x79c2c91946,0,0x0,0x10000401,0x0,0x1a7817149001⟩,⟨0x79c2c91906,0,0x0,0x0,0x0,0x1d789015⟩,⟨0x79c44b1886,0,0x0,0x0,0x0,0x23870b20⟩,⟨0x79c2c918f6,0,0x0,0x0,0x0,0x2c872926⟩,⟨0x1e44b19f5,0,0x31,0x1,0x0,0x322f0102⟩] else #[⟨0x79c44b19f6,0,0x0,0x10000001,0x0,0x3b8738350115⟩,⟨0x79c44b1806,0,0x0,0x0,0x0,0x3e871590⟩,⟨0x7912c919f6,0,0x0,0x10600301,0x0,0x1414b012915⟩,⟨0x7912c91986,0,0x0,0x0,0x0,0x449018⟩,⟨0x7112c91a06,0,0x0,0x0,0x0,0x47⟩,⟨0x7112c91996,0,0x0,0x10100210100002,0x0,0x403909301⟩,⟨0x79c44918c6,0,0x0,0x600201,0x0,0x901b14018730⟩,⟨0x79c44918a6,0,0x0,0x10600201,0x0,0x901701872a⟩]) else (if i < 24 then #[⟨0x79c44b24c6,0,0x0,0x0,0x0,0x5a5a903636⟩,⟨0x79c44b2456,0,0x0,0x10600201,0x0,0x1872a904a⟩,⟨0x79c4491a26,0,0x0,0x600201,0x0,0x18735211536⟩,⟨0x79c4491826,0,0x0,0x10600201,0x0,0x381501875a⟩,⟨0x7912c91a26,0,0x0,0x0,0x0,0x307b2a2a15⟩,⟨0x7912c91956,0,0x0,0x10600201,0x0,0x16f5a4d15⟩,⟨0x1c4491a35,0,0x2602e,0x0,0x0,0x0⟩,⟨0x1c4491815,0,0x0,0x10000201,0x0,0x44413e3b2c0f230f1d1a110e01530150⟩] else #[⟨0x79c4491a36,0,0x0,0x6100201,0x0,0x1302f0536⟩,⟨0x79c4491816,0,0x0,0x0,0x0,0x3208872a5a⟩,⟨0x7112c91a36,0,0x0,0x10100310100102,0x0,0x59016f875604⟩,⟨0x7112c91966,0,0x0,0x10100210100002,0x0,0x16f876f04⟩,⟨0x7112c91a46,0,0x0,0x0,0x0,0x5c⟩,⟨0x7112c918d6,0,0x0,0x10100210100102,0x0,0x46f0f1501⟩])) : Array Ticket).getD (i % 8) default
def levs31e4k6 (i : Nat) : Ticket := (#[⟨0x79c44b2466,0,0x0,0x10000410600310600210600110000005,0x0,0xd0d590456047e7e530750074d4a4744413e3b3835322f2c290a260a23201d1a17140f110f6c0001010d0d01010e0b080502⟩] : Array Ticket).getD (i % 8) default
def trees31e4 : Book :=
  ⟨true,inputSet 31 [4],goalAt 31,6,5,readRule factss31e4 recss31e4,hintss31e4,8,unpackState wiress31e4 6,(fun k => match k with | 4 => 31 | 5 => 30 | 6 => 1 | _ => 0),fun k => match k with
    | 4 => levs31e4k4
    | 5 => levs31e4k5
    | 6 => levs31e4k6
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless31e4 : ∀ i, i < 5 → Valid true (goalAt 31) ((trees31e4).rule i) := by
  exact validateRules factss31e4 recss31e4 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31e4k4i0 : bookRange trees31e4 4 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31e4k4i16 : bookRange trees31e4 4 16 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods31e4k4 : allGood trees31e4 4 :=
  book_level trees31e4 4 ruless31e4 (book_empty trees31e4 3 rfl) (@book_split trees31e4 4 0 16 15 passs31e4k4i0 passs31e4k4i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31e4k5i0 : bookRange trees31e4 5 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31e4k5i16 : bookRange trees31e4 5 16 14 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods31e4k5 : allGood trees31e4 5 :=
  book_level trees31e4 5 ruless31e4 goods31e4k4 (@book_split trees31e4 5 0 16 14 passs31e4k5i0 passs31e4k5i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs31e4k6i0 : bookRange trees31e4 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods31e4k6 : allGood trees31e4 6 :=
  book_level trees31e4 6 ruless31e4 goods31e4k5 passs31e4k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims31e4 : Claim true 31 [4] 7 := by
  apply low_search (s:=true) (T:=goalAt 31) (raw:=rawSet 31) (es:=extraSet 31 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 31 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 31 [4]) (extraWord 31 4) = inputSet 31 [] := by decide +kernel
      change Low true (remove (inputSet 31 [4]) (extraWord 31 4)) (goalAt 31) 7
      rw [eq]
      exact claims31
  · exact book_end trees31e4 goods31e4k6 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims166 : Claim true 166 [] 4 :=
  rename_rows claims15 [0,2,4,6,34,36,37,16,18,19,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims167 : Claim true 167 [] 7 :=
  rename_rows claims31 [0,1,2,3,4,5,6,34,35,36,37,16,17,18,19,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims172 : Claim true 172 [] 4 :=
  rename_rows claims15 [0,7,4,10,34,38,37,16,20,19,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims57 : Claim true 57 [] 4 :=
  rename_rows claims15 [0,7,11,15,1,8,12,16,20,22,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims163 : Claim true 163 [] 4 :=
  rename_rows claims15 [0,2,1,3,16,18,17,34,36,35,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintss187 (i : Nat) : Nat := (0x800287d14c0023316a600141ea530008c34a98002c7908c0014a683e000422b1f000a2950f8001019a7c0016a633200095318700034f203 >>> (37*(i % 16))) % 137438953472
def wiress187 (i : Nat) : W := bandWord (((if i < 8 then 0x80000035c0000000009000002000057000000c00001000040b80001c80000480012938a00800000400010838000080000100004220c01480000080002110a014000000800021102 else 0x94800035c0002110a) >>> (72*(i % 8))) % 4722366482869645213696)
def factss187 (i : Nat) : {f : Fact // Sound true f} := (if i < 1 then ⟨item 27 [] 4,claims27⟩ else (if i < 2 then ⟨item 57 [] 4,claims57⟩ else ⟨item 163 [] 4,claims163⟩))
def recss187 (i : Nat) : Recipe := (#[(0,[]),(1,[]),(2,[])] : Array Recipe).getD (i % 8) default
def levs187k4 (i : Nat) : Ticket := (#[⟨0x652485,0,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def levs187k5 (i : Nat) : Ticket := (#[⟨0x6532186,0,0x0,0x10000001,0x0,0x1098⟩,⟨0x7653106,0,0x0,0x0,0x0,0x258⟩,⟨0x7652146,0,0x0,0x10000201,0x0,0x1242⟩] : Array Ticket).getD (i % 8) default
def levs187k6 (i : Nat) : Ticket := (#[⟨0x7653216,0,0x0,0x20000220000120000003,0x2071440813,0x10010010010092494200201251251a040⟩] : Array Ticket).getD (i % 8) default
def trees187 : Book :=
  ⟨true,inputSet 187 [],goalAt 187,6,3,readRule factss187 recss187,hintss187,6,unpackState wiress187 4,(fun k => match k with | 4 => 1 | 5 => 3 | 6 => 1 | _ => 0),fun k => match k with
    | 4 => levs187k4
    | 5 => levs187k5
    | 6 => levs187k6
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless187 : ∀ i, i < 3 → Valid true (goalAt 187) ((trees187).rule i) := by
  exact validateRules factss187 recss187 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs187k4i0 : bookRange trees187 4 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods187k4 : allGood trees187 4 :=
  book_level trees187 4 ruless187 (book_empty trees187 3 rfl) passs187k4i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs187k5i0 : bookRange trees187 5 0 3 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods187k5 : allGood trees187 5 :=
  book_level trees187 5 ruless187 goods187k4 passs187k5i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs187k6i0 : bookRange trees187 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods187k6 : allGood trees187 6 :=
  book_level trees187 6 ruless187 goods187k5 passs187k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims187 : Claim true 187 [] 7 := by
  apply low_search (s:=true) (T:=goalAt 187) (raw:=rawSet 187) (es:=extraSet 187 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end trees187 goods187k6 (by decide) (by decide +kernel)
def hintss187e4 (i : Nat) : Nat := (0x1000a0f529800461a54c0028a543e000086a1f0005a998c8002d4c66400080cd320000866990002cf20c8002d4cc1c0016a630e00145248700034f203 >>> (37*(i % 16))) % 137438953472
def wiress187e4 (i : Nat) : W := bandWord (((if i < 8 then 0x1c80001080042b90a01c00001080042990201480001080042380a00c00001000040b80001c80000480012938a00800000400010838000080000100004220c01480000080002110a else 0x80000035c0000000009000002000057000000c80001100044ba0c) >>> (72*(i % 8))) % 4722366482869645213696)
def factss187e4 (i : Nat) : {f : Fact // Sound true f} := (if i < 1 then ⟨item 27 [] 4,claims27⟩ else (if i < 2 then ⟨item 57 [] 4,claims57⟩ else ⟨item 163 [] 4,claims163⟩))
def recss187e4 (i : Nat) : Recipe := (#[(0,[]),(1,[]),(2,[])] : Array Recipe).getD (i % 8) default
def levs187e4k4 (i : Nat) : Ticket := (#[⟨0x7a9385,0,0x0,0x201,0x0,0x241⟩] : Array Ticket).getD (i % 8) default
def levs187e4k5 (i : Nat) : Ticket := (#[⟨0x7a92086,0,0x0,0x10000210600102,0x0,0x6102001⟩,⟨0xa942066,0,0x0,0x0,0x0,0x1b321⟩,⟨0x7a94136,0,0x0,0x10000201,0x0,0x180c2481⟩,⟨0xa941056,0,0x0,0x0,0x0,0x3e4⟩] : Array Ticket).getD (i % 8) default
def levs187e4k6 (i : Nat) : Ticket := (#[⟨0x7a942107,0,0x0,0x20000220700120700003,0x0,0x155e2c730814408f⟩] : Array Ticket).getD (i % 8) default
def trees187e4 : Book :=
  ⟨true,inputSet 187 [4],goalAt 187,6,3,readRule factss187e4 recss187e4,hintss187e4,6,unpackState wiress187e4 4,(fun k => match k with | 4 => 1 | 5 => 4 | 6 => 1 | _ => 0),fun k => match k with
    | 4 => levs187e4k4
    | 5 => levs187e4k5
    | 6 => levs187e4k6
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless187e4 : ∀ i, i < 3 → Valid true (goalAt 187) ((trees187e4).rule i) := by
  exact validateRules factss187e4 recss187e4 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs187e4k4i0 : bookRange trees187e4 4 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods187e4k4 : allGood trees187e4 4 :=
  book_level trees187e4 4 ruless187e4 (book_empty trees187e4 3 rfl) passs187e4k4i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs187e4k5i0 : bookRange trees187e4 5 0 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods187e4k5 : allGood trees187e4 5 :=
  book_level trees187e4 5 ruless187e4 goods187e4k4 passs187e4k5i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs187e4k6i0 : bookRange trees187e4 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods187e4k6 : allGood trees187e4 6 :=
  book_level trees187e4 6 ruless187e4 goods187e4k5 passs187e4k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims187e4 : Claim true 187 [4] 7 := by
  apply low_search (s:=true) (T:=goalAt 187) (raw:=rawSet 187) (es:=extraSet 187 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 187 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 187 [4]) (extraWord 187 4) = inputSet 187 [] := by decide +kernel
      change Low true (remove (inputSet 187 [4]) (extraWord 187 4)) (goalAt 187) 7
      rw [eq]
      exact claims187
  · exact book_end trees187e4 goods187e4k6 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims156 : Claim true 156 [] 4 :=
  rename_rows claims15 [0,11,7,15,4,14,10,34,40,38,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims165 : Claim true 165 [] 4 :=
  rename_rows claims15 [0,1,16,17,34,35,41,4,5,19,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims177 : Claim true 177 [] 4 :=
  rename_rows claims15 [0,11,1,12,16,22,17,34,40,35,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintss189 (i : Nat) : Nat := ((if i < 32 then (if i < 16 then 0x800285026400054542a0013529950001654ca800108a65400283132a001418715000a2920a800268905400143c82a000718415000a291ca8002878e5400144452a0002ca215000a0c10a else 0x800108ac7c0028a543e00141871f00050a20f8000b2d0640016a633200074b19900050a8cc8002949c64002394e3200141e71900020a38c800294966400283cb32000a14419000a2514c) else (if i < 48 then 0x8000a6512c000e323960002949cb00098f3a58004661d2c0028305960002991a300014a511800105268c00163c8460002984230004ca2118002850a8c000530146000a5341f0003a598f else 0x2000a1f4530004ca9a9800512c74c0023316a600141ea530005114e9)) >>> (37*(i % 16))) % 137438953472
def wiress189 (i : Nat) : W := bandWord (((if i < 16 then (if i < 8 then 0x420000020000044300140000008000211220140000008000211020140000008000210220120000000005b443000c00000000040d80000a000000000108580014000000000021122 else 0x120000048001205a200a00000400010858000a00000400010848000a0000040000085800560000028000a5532042000002000084430042000002000084410042000002000080430) else (if i < 24 then 0x900000200001b0000044000016c0000112204e00001200048dc3004400001200048583000c00001000040d80000c00001000040980000c00001000000d80001e0000048001295a2 else (if i < 32 then 0x9c0000300005bd80008800003000059c8000c0000026c0000000009a0000240005b85800d20000220005b44300900000200005b00000900000200005300000900000200004b0000 else 0xcc000036c0040d8000ca000036c001085800d4000036c000211220c0000036c000000000c0000036400000000088000034c001081800c0000032c00000000))) >>> (72*(i % 8))) % 4722366482869645213696)
def factss189 (i : Nat) : {f : Fact // Sound true f} := (if i < 3 then (if i < 1 then ⟨item 29 [] 4,claims29⟩ else (if i < 2 then ⟨item 57 [] 4,claims57⟩ else ⟨item 156 [] 4,claims156⟩)) else (if i < 4 then ⟨item 165 [] 4,claims165⟩ else (if i < 5 then ⟨item 172 [] 4,claims172⟩ else ⟨item 177 [] 4,claims177⟩)))
def recss189 (i : Nat) : Recipe := (#[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])] : Array Recipe).getD (i % 8) default
def levs189k5 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x1a4ca9255,0,0x13001,0x0,0x0,0x0⟩,⟨0x1a4ca4245,0,0x2029,0x0,0x0,0x0⟩,⟨0x8d338a1966,0,0x0,0x0,0x0,0x21⟩,⟨0x233866df5,0,0x4010,0x0,0x0,0x0⟩,⟨0x2338655b5,0,0xf023,0x0,0x0,0x0⟩,⟨0x69338a1836,0,0x0,0x0,0x0,0x4b⟩,⟨0x1a4ca4255,0,0x14003,0x0,0x0,0x0⟩,⟨0x8da38a18f6,0,0x0,0x0,0x0,0x81⟩] else #[⟨0x8da4ce1a16,0,0x0,0x0,0x0,0x3c⟩,⟨0x2338655f5,0,0x5011,0x0,0x0,0x0⟩,⟨0x8da4ca1946,0,0x0,0x0,0x0,0x6c⟩,⟨0x8da4ce29e6,0,0x0,0x0,0x0,0xf⟩]) : Array Ticket).getD (i % 8) default
def levs189k6 (i : Nat) : Ticket := ((if i < 24 then (if i < 8 then #[⟨0x8da4ce28b6,0,0x6,0x20000101,0x11,0x0⟩,⟨0x8da4ce2856,0,0x0,0x20000520000420000220000104,0xa0704012,0x20652030757501104⟩,⟨0x8da4ce18b6,0,0x15,0x20000210000102,0x4011,0x1e⟩,⟨0x8da4ce1896,0,0x0,0x20000520000420000220000104,0xa0704012,0x20652030757510401⟩,⟨0x2369338a18b7,0,0x0,0x0,0x8a750f2,0x600⟩,⟨0x8da4ce2a46,0,0x2b,0x20000001,0x2011,0x1⟩,⟨0x8da4ce2806,0,0x0,0x20000220000120000003,0x63605a3021070604014,0x700060015110800040032330100301311⟩,⟨0x69338a1a46,0,0x1c,0x20000210000002,0x504012,0x594⟩] else (if i < 16 then #[⟨0x69338a1a26,0,0x0,0x20000220000120000003,0x63605a3021070604014,0x600151107000400323308000100131130⟩,⟨0x2369338a1a47,0,0x0,0x20000420100320000120000004,0x0,0x8010a519351780778010a04⟩,⟨0x8da4ce19b6,0,0x24,0x20000001,0xb011,0x4⟩,⟨0x8da4ce1876,0,0x0,0x20000220000120000003,0x635d5a4b30070604014,0x500060014110800070032330300131110⟩,⟨0x8d338a19b6,0,0xf,0x20000110000002,0xe04012,0x585⟩,⟨0x8d338a1996,0,0x0,0x20000220000120000003,0x635d5a4b30070604014,0x500141106000800323307001003001311⟩,⟨0x2369338a19b7,0,0x0,0x20000520100320000220000004,0x0,0x11012a9f2a8d078d0a010a04⟩,⟨0x8da4ca1906,0,0x29,0x20000201,0x5011,0x8⟩] else #[⟨0x8da4ca18d6,0,0x0,0x20000320000202,0x63514b42302a04013,0x93410092c20001801093c1008⟩,⟨0x8da4ce2906,0,0x3,0x20000310000202,0x1404012,0x594⟩,⟨0x8da4ce2846,0,0x0,0x20000320000202,0x63514b42302a04013,0x93410092c93c1008080006004⟩,⟨0x2369338a1907,0,0x0,0x20000520000320000220100004,0x0,0x1707066304040706510a0151⟩,⟨0x8da4ca19c6,0,0x25,0x20000001,0x11,0x0⟩,⟨0x8da4ca18c6,0,0x0,0x20000520000320000220000004,0xa0704012,0x2020ab30105720865⟩,⟨0x8d338a19c6,0,0xc,0x20000310000002,0x4011,0x1e⟩,⟨0x8d338a1986,0,0x0,0x20000520000320000220000004,0xa0704012,0x20ab2020658301057⟩])) else (if i < 32 then #[⟨0x2369338a19c7,0,0x0,0x0,0x9c5d212,0x9⟩,⟨0x8da4ca1a56,0,0x32,0x20000001,0x2011,0x1⟩,⟨0x8da4ca1816,0,0x0,0x20000320000120000003,0x510f070604013,0x300300b24100500c2580c06da⟩,⟨0x69338a1a56,0,0x22,0x20000310000002,0x1404012,0x558⟩,⟨0x69338a1a06,0,0x0,0x20000320000120000003,0x510f070604013,0x300b24300301b698040309140⟩,⟨0x2369338a1a57,0,0x0,0x20000320100220000120000004,0x0,0xa010a0163061a04637e0706⟩,⟨0x8da38a1956,0,0x30,0x20000101,0xe011,0x8⟩,⟨0x8da38a1926,0,0x0,0x20000320000102,0x5a512a21150604013,0x10093092801460030010093c8⟩] else (if i < 40 then #[⟨0x8da4ce1956,0,0x11,0x20000310000102,0x1d04012,0x558⟩,⟨0x8da4ce1886,0,0x0,0x20000320000102,0x5a512a21150604013,0x10093c804024c24a1800c0005⟩,⟨0x2369338a1957,0,0x0,0x20000420000320000120100004,0x0,0x4305a04072007302a0a012a⟩,⟨0x8da38a19f6,0,0x36,0x20000001,0xb011,0x1⟩,⟨0x8da38a1916,0,0x0,0x20000320000220000003,0x302a0f0704013,0x200200a2440010092c2010495⟩,⟨0x8d338a19f6,0,0x1f,0x20000310000002,0x1d04012,0x558⟩,⟨0x8d338a1976,0,0x0,0x20000320000220000003,0x302a0f0704013,0x201255008028908010004024b⟩,⟨0x2369338a19f7,0,0x0,0x20000320000220100120000004,0x0,0x1010a5a300a5a6904302307⟩] else #[⟨0x8da38a1a66,0,0x2c,0x20000001,0x11,0x0⟩,⟨0x8da38a1826,0,0x0,0x20000420000320000120000004,0xa0704012,0x2020ab10307582065⟩,⟨0x69338a1a66,0,0x1a,0x20000310000002,0x4011,0x1e⟩,⟨0x69338a19d6,0,0x0,0x20000420000320000120000004,0xa0704012,0x2065820ab20107530⟩,⟨0x2369338a1a67,0,0x0,0x0,0x96604b2,0x21⟩]))) : Array Ticket).getD (i % 8) default
def levs189k7 (i : Nat) : Ticket := (#[⟨0x8da4ce2866,0,0x0,0x20000520000420000320000220000120000006,0x0,0x1010101010a860183807d7a010a770174716e6b040a680465625f5c070a0d07010a59015653504d010a4a014744413e0a0a0a0a040a1004070a3b073835322f0104040101042c012926232001071d011a1714110107070104070e040b080502⟩] : Array Ticket).getD (i % 8) default
def trees189 : Book :=
  ⟨true,inputSet 189 [],goalAt 189,7,6,readRule factss189 recss189,hintss189,8,unpackState wiress189 6,(fun k => match k with | 5 => 12 | 6 => 45 | 7 => 1 | _ => 0),fun k => match k with
    | 5 => levs189k5
    | 6 => levs189k6
    | 7 => levs189k7
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless189 : ∀ i, i < 6 → Valid true (goalAt 189) ((trees189).rule i) := by
  exact validateRules factss189 recss189 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189k5i0 : bookRange trees189 5 0 12 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods189k5 : allGood trees189 5 :=
  book_level trees189 5 ruless189 (book_empty trees189 4 rfl) passs189k5i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189k6i0 : bookRange trees189 6 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189k6i16 : bookRange trees189 6 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189k6i32 : bookRange trees189 6 32 13 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods189k6 : allGood trees189 6 :=
  book_level trees189 6 ruless189 goods189k5 (@book_split trees189 6 0 16 29 passs189k6i0 (@book_split trees189 6 16 16 13 passs189k6i16 passs189k6i32))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189k7i0 : bookRange trees189 7 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods189k7 : allGood trees189 7 :=
  book_level trees189 7 ruless189 goods189k6 passs189k7i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims189 : Claim true 189 [] 8 := by
  apply low_search (s:=true) (T:=goalAt 189) (raw:=rawSet 189) (es:=extraSet 189 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end trees189 goods189k7 (by decide) (by decide +kernel)
def hintss189e4 (i : Nat) : Nat := ((if i < 32 then (if i < 16 then 0x80028502640028a542a0002a2a1500014c50a8000b2a65400084532a0009a241500058c20a8001c610540028a472a00071839500014c1ca1e61620e5400144452a0002ca215000a0c10a else 0x8001d2c66400014563200041eb1900020a58c800514a8640005294320011ca71900020a38c800294966400083cb3200144a41900059120c8000851064002894532000a1429900059104c) else (if i < 48 then 0x800107ac8c0005294460004149a30004ca2118002850a8c000530146000a5341f0003a598f800514a87c00164483e000a534190008e5a0c8000b2d06400082a832000b53199000a258cc else 0x2000a1f4530008cc5a9800507a94c0028314a48980c485300014ca258000a5272c00263ce9600131874b0008cc3a58005060b2c00283049600119824b00014a125)) >>> (37*(i % 16))) % 137438953472
def wiress189e4 (i : Nat) : W := bandWord (((if i < 16 then (if i < 8 then 0xa00000400010858000a0000040000085800560000028000a553204200000200008443004200000200008041004200000200000443001400000080002112200a000000000108580 else 0x5e0000128004add320540000128004a583204e00001200048dc3001c00001080042d92200c00001000040d80001e0000048001295a20120000048001205a201e0000048000295a2) else (if i < 24 then 0xca0000264001085800c00000264000000000d20000220005b04100900000200005b00000900000200005300000900000200004b000004c000016c0000d92201e00001480052dda2 else (if i < 32 then 0xcc000036c0040d8000d4000036c000211220c0000036c000000000c0000032c0000000009c0000308005bd92209c0000300005bd80008800003000059c80009c0000300004bd800 else 0xdc000036c0042d922))) >>> (72*(i % 8))) % 4722366482869645213696)
def factss189e4 (i : Nat) : {f : Fact // Sound true f} := (if i < 3 then (if i < 1 then ⟨item 29 [] 4,claims29⟩ else (if i < 2 then ⟨item 57 [] 4,claims57⟩ else ⟨item 156 [] 4,claims156⟩)) else (if i < 4 then ⟨item 165 [] 4,claims165⟩ else (if i < 5 then ⟨item 172 [] 4,claims172⟩ else ⟨item 177 [] 4,claims177⟩)))
def recss189e4 (i : Nat) : Recipe := (#[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])] : Array Recipe).getD (i % 8) default
def levs189e4k4 (i : Nat) : Ticket := (#[⟨0xc7442985,0,0x0,0x0,0x0,0x0⟩,⟨0xc74421a5,0,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def levs189e4k5 (i : Nat) : Ticket := ((if i < 8 then #[⟨0xc74429a5,0,0x1b,0x10000401,0x11,0x0⟩,⟨0x142c42a05,0,0x202f,0x0,0x0,0x0⟩,⟨0x31d2c42926,0,0x0,0x10600501,0x0,0x900102⟩,⟨0x31d50b1086,0,0x0,0x10600501,0x0,0x900105⟩,⟨0x31d10119a6,0,0x0,0x10600001,0x0,0x11205⟩,⟨0x31d1c40586,0,0x0,0x10600001,0x0,0x12a02⟩,⟨0x7541c40496,0,0x0,0x0,0x0,0x9c⟩,⟨0x1d1c13da5,0,0x7013,0x0,0x0,0x0⟩] else #[⟨0x7542c70556,0,0x0,0x10000501,0x0,0x3301⟩,⟨0x7542c404e6,0,0x0,0x0,0x0,0x0⟩,⟨0x7542c71196,0,0x0,0x0,0x0,0x15⟩,⟨0x50b1c40576,0,0x0,0x10000001,0x0,0x16f⟩,⟨0x74b1c40516,0,0x0,0x0,0x0,0x0⟩]) : Array Ticket).getD (i % 8) default
def levs189e4k6 (i : Nat) : Ticket := ((if i < 8 then #[⟨0xc7542c71057,0,0x0,0x0,0x0,0x15090f7509⟩,⟨0xc7542c711e7,0,0x0,0x20000420700102,0x0,0x401015a047500ae⟩,⟨0xc7542c70427,0,0x0,0x20700120700002,0x0,0x1690448758a⟩,⟨0xc74b1c40537,0,0x0,0x20700120700002,0x0,0x1690448758a⟩,⟨0x31d50b10a6,0,0x2f,0x20000410000202,0x0,0x4040504040102⟩,⟨0xc7542c710a7,0,0x0,0x20700520000302,0x0,0x6690401750601064508⟩,⟨0xc7542c40467,0,0x0,0x20700520700002,0x0,0x16904480e0b⟩,⟨0xc74b1c40527,0,0x0,0x20700520700002,0x0,0x16904481108⟩] else (if i < 16 then #[⟨0xc7542c40407,0,0x0,0x20700120700002,0x0,0x1690448758a⟩,⟨0xc50b1c405c7,0,0x0,0x20700120700002,0x0,0x4480169758a⟩,⟨0x1d50b1c40507,0,0x0,0x20100001,0x0,0x140169⟩,⟨0xc7541c404d7,0,0x0,0x20000420700102,0x0,0x104018a0c7e0424⟩,⟨0x31d1c405a6,0,0x28,0x20000410000302,0x0,0x4040404170201⟩,⟨0xc7541c405a7,0,0x0,0x20700001,0x0,0x101757536010e8a752d⟩,⟨0xc7541c405f7,0,0x0,0x0,0x0,0x5db4938aab⟩,⟨0x7542c704f6,0,0x13019,0x0,0x0,0x17⟩] else #[⟨0x7542c70436,0,0x0,0x20000520000420000103,0x751e1a0704013,0x4024d20201250a241008003⟩,⟨0x1d50b1c404f7,0,0x0,0x20100301,0x0,0x75361d013648⟩,⟨0x1d50b1c405b7,0,0x0,0x20100101,0x0,0x14820⟩,⟨0x50b1c40606,0,0x20024,0x0,0x0,0x5⟩,⟨0x50b1c40566,0,0x0,0x20000420000120000003,0x231e070604013,0xc02c960401a6c500100b258⟩,⟨0x1d50b1c40607,0,0x0,0x20100001,0x0,0x26015d5d8a69⟩])) : Array Ticket).getD (i % 8) default
def levs189e4k7 (i : Nat) : Ticket := (#[⟨0xc7542c71017,0,0x0,0x30000420000320000220700120700005,0x0,0xd0d010d41013e3b010d38010d0d040d3504322f07070d0d0d2c0d0d0d29260d0d0d230a0a07070d0a200a1d7b1a7b171e141e0d420d110d0d0e0b2708270a0a0d0d0d050d300d0d0d02⟩] : Array Ticket).getD (i % 8) default
def trees189e4 : Book :=
  ⟨true,inputSet 189 [4],goalAt 189,7,6,readRule factss189e4 recss189e4,hintss189e4,8,unpackState wiress189e4 6,(fun k => match k with | 4 => 2 | 5 => 13 | 6 => 22 | 7 => 1 | _ => 0),fun k => match k with
    | 4 => levs189e4k4
    | 5 => levs189e4k5
    | 6 => levs189e4k6
    | 7 => levs189e4k7
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless189e4 : ∀ i, i < 6 → Valid true (goalAt 189) ((trees189e4).rule i) := by
  exact validateRules factss189e4 recss189e4 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189e4k4i0 : bookRange trees189e4 4 0 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods189e4k4 : allGood trees189e4 4 :=
  book_level trees189e4 4 ruless189e4 (book_empty trees189e4 3 rfl) passs189e4k4i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189e4k5i0 : bookRange trees189e4 5 0 13 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods189e4k5 : allGood trees189e4 5 :=
  book_level trees189e4 5 ruless189e4 goods189e4k4 passs189e4k5i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189e4k6i0 : bookRange trees189e4 6 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189e4k6i16 : bookRange trees189e4 6 16 6 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods189e4k6 : allGood trees189e4 6 :=
  book_level trees189e4 6 ruless189e4 goods189e4k5 (@book_split trees189e4 6 0 16 6 passs189e4k6i0 passs189e4k6i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs189e4k7i0 : bookRange trees189e4 7 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods189e4k7 : allGood trees189e4 7 :=
  book_level trees189e4 7 ruless189e4 goods189e4k6 passs189e4k7i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims189e4 : Claim true 189 [4] 8 := by
  apply low_search (s:=true) (T:=goalAt 189) (raw:=rawSet 189) (es:=extraSet 189 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 189 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 189 [4]) (extraWord 189 4) = inputSet 189 [] := by decide +kernel
      change Low true (remove (inputSet 189 [4]) (extraWord 189 4)) (goalAt 189) 8
      rw [eq]
      exact claims189
  · exact book_end trees189e4 goods189e4k7 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims190 : Claim true 190 [] 7 :=
  rename_rows claims187 [0,4,2,6,0,0,0,11,14,13,0,7,10,9,0,15,34,37,36,0,40,0,38,0,0,0,0,0,0,0,0,0,0,0,16,19,18,0,22,0,20,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintss191 (i : Nat) : Nat := ((if i < 48 then (if i < 16 then 0x8002d29a34000530d1a00145210d00050f0868001c6043400059640e0002952070004a98c38000a5241c000528d0e00132248700014a2438001a7901c0014a420e00141e10700020a083 else (if i < 32 then 0x800108a65400240d32a00041871500090338a8000a1925400010c92a0009a241500038c20a8002888a5400090c52a00141821500090310a8000a8c8340024a531a0002a290d00024f386 else 0x8000b2d06400139633200074b1990004868cc8004729c64000828e3200028c69900004334c8001c5106400121883200144a29900034614c80028502640012181320002a2a150008d14ca)) else (if i < 64 then 0x8000a5288c0008293460000869230004ca2118002430a8c000530146000a5341f00052998f800514ac7c0028a543e00130669f00020334f800294967c00161893e00070c49f000a291cf else (if i < 80 then 0x8004c1a54c00230d2a600141e85300014ca258000a1c92c00010e4960007191cb0008d14e5800466272c00052939600119874b0009031658000a5092c0013963460002991a30004ca8d1 else 0x400143e8a600141f353000586929800263494c00143e2a6000a1eb53000a0f529))) >>> (37*(i % 16))) % 137438953472
def wiress191 (i : Nat) : W := bandWord (((if i < 16 then (if i < 8 then 0x4300000200008447004300000200008445000180000100004224c01480000080002112a01480000080002110a01f0000000005ffc700130000000005f447000e000000000009420 else 0x4500001200048787001f0000100005ffc7000c00001000040f80001e8000048001297aa0128000048001207aa00a0000040001087800578000028000a557a0560000028000a5532) else (if i < 24 then 0xd2800027c001207aa0d30000220005f44700d00000220000200200900000200005f000004e800017c001097aa04e800017c000097aa044800017c0000112a04f00001200048fc70 else (if i < 32 then 0xd2800037c001207aa0d4800037c0002112a0c0000037c000000000ca0000374001086800df0000320005ffc700d50000320005f78700d50000320004f787009c00003000057b800 else 0xde800037c001297aa))) >>> (72*(i % 8))) % 4722366482869645213696)
def factss191 (i : Nat) : {f : Fact // Sound true f} := (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then ⟨item 31 [] 7,claims31⟩ else ⟨item 167 [] 7,claims167⟩) else (if i < 3 then ⟨item 187 [] 7,claims187⟩ else ⟨item 189 [] 8,claims189⟩)) else (if i < 6 then (if i < 5 then ⟨item 190 [] 7,claims190⟩ else ⟨item 30 [] 4,claims30⟩) else (if i < 7 then ⟨item 156 [] 4,claims156⟩ else ⟨item 166 [] 4,claims166⟩))) else (if i < 12 then (if i < 10 then (if i < 9 then ⟨item 27 [] 4,claims27⟩ else ⟨item 57 [] 4,claims57⟩) else (if i < 11 then ⟨item 163 [] 4,claims163⟩ else ⟨item 15 [] 4,claims15⟩)) else (if i < 14 then (if i < 13 then ⟨item 23 [] 4,claims23⟩ else ⟨item 29 [] 4,claims29⟩) else (if i < 15 then ⟨item 172 [] 4,claims172⟩ else ⟨item 177 [] 4,claims177⟩))))
def recss191 (i : Nat) : Recipe := ((if i < 24 then (if i < 8 then #[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(0,[129]),(6,[])] else (if i < 16 then #[(7,[]),(1,[129]),(3,[65]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[])] else #[(13,[]),(0,[130]),(1,[130]),(14,[]),(15,[]),(3,[66]),(0,[131]),(1,[131])])) else (if i < 32 then #[(3,[67]),(0,[193]),(2,[129]),(3,[129]),(1,[257]),(2,[321]),(3,[321]),(0,[265])] else (if i < 40 then #[(3,[197]),(1,[201]),(3,[261]),(2,[66]),(4,[6]),(0,[129,86]),(1,[129,86]),(3,[129,321])] else #[(3,[197,261])]))) : Array Recipe).getD (i % 8) default
def levs191k5 (i : Nat) : Ticket := (#[⟨0x531e4165,0,0x1200f,0x0,0x0,0x0⟩,⟨0x1c530b7916,0,0x0,0x0,0x0,0x0⟩,⟨0x14440f5816,0,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def levs191k6 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x34a1c51156,0,0x1400b,0x0,0x0,0x0⟩,⟨0x34714c7966,0,0xb005,0x0,0x0,0x2⟩,⟨0x28511e4166,0,0x1200f,0x0,0x0,0x2⟩,⟨0x50d1c579c6,0,0x2015,0x0,0x0,0x0⟩,⟨0x3471447926,0,0x51021,0x0,0x0,0x0⟩,⟨0x50714c2de6,0,0x5,0x0,0x0,0xa0c⟩,⟨0x50714c7906,0,0xb005,0x0,0x0,0x2⟩,⟨0x34714c7916,0,0xb,0x0,0x0,0xa1e⟩] else (if i < 16 then #[⟨0x3471447936,0,0x4e021,0x0,0x0,0x0⟩,⟨0x74510c4166,0,0x1200f,0x0,0x0,0x2⟩,⟨0x74a1445986,0,0xd023,0x0,0x0,0x0⟩,⟨0x2871445826,0,0x5702f,0x0,0x0,0x0⟩,⟨0x7451103d66,0,0xf,0x0,0x0,0x102a⟩,⟨0x2851105816,0,0x12,0x0,0x0,0x1033⟩,⟨0x28714458e6,0,0x5302f,0x0,0x0,0x0⟩,⟨0x50d1c531c6,0,0x3017,0x0,0x0,0x0⟩] else #[⟨0x5071443176,0,0x3a046,0x0,0x0,0x0⟩,⟨0x50714431f6,0,0x34046,0x0,0x0,0x0⟩,⟨0x7541c51006,0,0xf007,0x0,0x0,0x0⟩,⟨0x74a1444186,0,0xe025,0x0,0x0,0x0⟩,⟨0x7471444196,0,0x3703d,0x0,0x0,0x0⟩,⟨0x74714441a6,0,0x3103d,0x0,0x0,0x0⟩])) : Array Ticket).getD (i % 8) default
def levs191k7 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x1d50d2872487,0,0x19,0x10002301,0x11,0x0⟩,⟨0x1d50d2842487,0,0x2b,0x10002400002302,0x8011,0x1e⟩,⟨0x1d50d2871087,0,0x0,0x20002620002510002303,0x843c0c0381002003,0x4d24d26d96db4d24d26db71b49148855248a2b1492⟩,⟨0x75434a1c42488,0,0x0,0x22101001,0x6dae890012,0x2d54⟩,⟨0xd2871447967,0,0x1200b,0x0,0x0,0x200a02⟩,⟨0x143471447a07,0,0xb051,0x0,0x0,0x1c0b⟩,⟨0x50d1c531e6,0,0x0,0x10002710001c10001920000504,0x3c170a044180a0381408014,0x810110131133333337333363033033011012110990011014113333343344444444044001101155550310⟩,⟨0x142871447907,0,0xf00b,0x0,0x0,0x2808⟩] else (if i < 16 then #[⟨0xd2871447917,0,0xb,0x30000501,0x682e012,0x180⟩,⟨0x1d3471443167,0,0x12005,0x0,0x0,0x3a05⟩,⟨0x1d28714459b7,0,0x12057,0x0,0x0,0x4620⟩,⟨0x74a1444166,0,0x0,0x10002810002110001f20000b04,0x662a148983a0a0401c08014,0x710110121122222225222262022022011014112222242244444444044001101311888809900110110210⟩,⟨0xd2871445817,0,0x12,0x30000b01,0xb052012,0x180⟩,⟨0x143471443207,0,0x503a,0x0,0x0,0x642f⟩,⟨0x1d50714430b7,0,0x5,0x30000801,0xd422012,0x102⟩,⟨0x1d5071443107,0,0xf005,0x0,0x0,0x742838⟩] else #[⟨0x1d28714441b7,0,0xf037,0x0,0x0,0x7c3b⟩,⟨0x1d50714440f7,0,0xf,0x30000d01,0x1044c012,0x102⟩])) : Array Ticket).getD (i % 8) default
def levs191k8 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x1d50d2871497,0,0x0,0x30000d30000c30000b10000a20000920000600000410000208,0x16098401a0a0381004014,0x6666633634336336343368864048486336343363363433888868864848446666666630002633635336336353387474544874745446776055757156336336336⟩,⟨0x1d50d2871437,0,0x0,0x10001520001220001130000d30000c30000b3000083000073000051000041000020b,0x7c38190b04c200d0501c08014,0x555558858988588589885775999027425885898858858988777757752742999155555555808858858a8858858a8876969a9976969a9956652632522581885225010⟩,⟨0x1d50d2851097,0,0x0,0x10000a20000930000830000720000630000510000400000208,0x16098401a0a0381408014,0x3333344347443443474436637676773443474434434744666636637176763443484434434844657578776575787735538885852833334133330003443344344⟩,⟨0x1d50d2851067,0,0x0,0x10001820001720001630000d30000c30000b3000083000073000051000041000020b,0x7c38190b04c200d0501c08014,0x555558858988588589882742577599905885898858858988777727429991577558858a8858858a8876969a9976969a9926325665522581885225010555555558088⟩,⟨0x75434a1c51098,0,0x0,0x30101030100f30100e30000b10000a2000092000063000051000041010031000020b,0x1f0e0642c1308034160a0401c08014,0x67666766777770777777a7a67666766777777777277b7b46646046646446866686678777877088088888c8c5831629669696690449090299a66aa66a⟩,⟨0x1434a1c511e7,0,0x0,0x10001e10001d20001c30000830000730000510000410000008,0x3c1a0b8582813088401c0d0501c08014,0x2222c0200206006464666b24422462662002060044446464244266619246266672002050028d220020a0043636a6643636a6683a3233223a2aa222200821211200⟩,⟨0x1d34a1c51167,0,0x0,0x10002220002130000d30000c30000b10000210000007,0x331308c401d098401c0d0501c08014,0x2222b02002060024426661a64642462666920020600444424426464666824626622220020020020700436367664363676623327373237277200205002112112cc2⟩,⟨0x1d50d1c510c7,0,0x0,0x10001b10001a20001930000830000730000510000410000108,0x5e2c148742c14098401a0c0501c08014,0x222226626066266260660505000d2552005555c0266226626a6626626966266269665303090073932332539399222261668222272121150026626b662662667545⟩] else #[⟨0x1d50a1c51107,0,0x0,0x10002020001f30000d30000c30000b10000210000107,0x35190bc54230b84c200d0501c08014,0x222225525055255250552442000404000a4444c0222222225155840025525655255256554303060023326363436366255257552552211211499425525525525b55⟩]) : Array Ticket).getD (i % 8) default
def levs191k9 (i : Nat) : Ticket := (#[⟨0x1d50d2871447,0,0x0,0x10000410000310000220000120000005,0x34170a0441c0d0582810070281004014,0x200000002002222222d22220000020000000200222222222222222c000000000b00000006000000060022222622222226224664666600000a00000048947531⟩] : Array Ticket).getD (i % 8) default
def trees191 : Book :=
  ⟨true,inputSet 191 [],goalAt 191,9,41,readRule factss191 recss191,hintss191,9,unpackState wiress191 6,(fun k => match k with | 5 => 3 | 6 => 22 | 7 => 18 | 8 => 9 | 9 => 1 | _ => 0),fun k => match k with
    | 5 => levs191k5
    | 6 => levs191k6
    | 7 => levs191k7
    | 8 => levs191k8
    | 9 => levs191k9
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless191 : ∀ i, i < 41 → Valid true (goalAt 191) ((trees191).rule i) := by
  exact validateRules factss191 recss191 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191k5i0 : bookRange trees191 5 0 3 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191k5 : allGood trees191 5 :=
  book_level trees191 5 ruless191 (book_empty trees191 4 rfl) passs191k5i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191k6i0 : bookRange trees191 6 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191k6i16 : bookRange trees191 6 16 6 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191k6 : allGood trees191 6 :=
  book_level trees191 6 ruless191 goods191k5 (@book_split trees191 6 0 16 6 passs191k6i0 passs191k6i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191k7i0 : bookRange trees191 7 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191k7i16 : bookRange trees191 7 16 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191k7 : allGood trees191 7 :=
  book_level trees191 7 ruless191 goods191k6 (@book_split trees191 7 0 16 2 passs191k7i0 passs191k7i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191k8i0 : bookRange trees191 8 0 9 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191k8 : allGood trees191 8 :=
  book_level trees191 8 ruless191 goods191k7 passs191k8i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191k9i0 : bookRange trees191 9 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191k9 : allGood trees191 9 :=
  book_level trees191 9 ruless191 goods191k8 passs191k9i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims191 : Claim true 191 [] 10 := by
  apply low_search (s:=true) (T:=goalAt 191) (raw:=rawSet 191) (es:=extraSet 191 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end trees191 goods191k9 (by decide) (by decide +kernel)
def hintss191e4 (i : Nat) : Nat := ((if i < 208 then (if i < 96 then (if i < 48 then (if i < 16 then 0x8001a6101c00289450e000b2228700058c1438001a60a1c0028a420e000a521070003a5083800105041c00161820e00070c107000346083800254821c00164410e000b1808700034c043 else (if i < 32 then 0x8004c8921c000d3c90e0013184870008cc243800265121c00052890e0002144870003862438001a31218a184a080e00144a4062861162038002c8901c000d3c80c50c21c40628610d203 else 0x8001079c1c000828e0c3142107061a51283430d28919a1862848cd0e00041e6870008cc3438001061a1c000530d0e00009868618a1083438005149218a944a090c34a24c4862a5124243)) else (if i < 64 then 0x8001d2c61c00164630e00069f18694610e8c31430874618a1843630e00141918700034c8c3800494ac1c00084560c314210b070004c6583800085241c000e1900e0011ca7061a5123383 else (if i < 80 then 0xc5091d01c00083e80e00119940694a109a038002d4cc1c000e9660d28c213307000a299030c5093481c00059640e00021520694a1099038002d4c61c0012a630c50c251187000a258c3 else 0x800506043400233021a000b1810d00038c086800106043400053021a00009810c0cf044086066022043400280c21a000b0610d0003830868001a184340014a680e0011cb407000165a03))) else (if i < 144 then (if i < 112 then 0x8001a19234000da441a000b2220c28f20e1061478270830a0c13441a00068620c3c304210618182108340028a421819e0a610c0cc0530868002c8843400143c21a00041e10c0cc04e086 else (if i < 128 then 0x8002019c34002330d1a00041868d00014c3468000261a340028a491a000a1e48d00038f2468002c61234000e3091a00041848d00014c246800265123400042891819808848d000383246 else 0x8002c8a63400280d31a000b0698d000a294868002c8a43400054521a000b1890d00038c486800106243400053121819e08890c0cc0444868002c1a434000d0d21a00049e70c3ca044386)) else (if i < 176 then (if i < 160 then 0xc7964085113cb1c42861e58e215000a299068000a8c83400143e41a000b1920d00038c906800106483400053241819e08920c0cc044906800501c8340024a561a00145298d0009294c6 else 0x1e89698e5400163072a00071839500020c1ca8000a60e50f30b147287a25883943cc2c41ca8001c18e5400144452a000a1829500024314a800472885400233042a00041821418334810a) else (if i < 192 then 0x8002c61254000e3092a00041849500014c24a1e61621254000e0c92a00040649500014324a800021925400134482a00141841500058c20a8002661054000e3082a000398415000a291ca else 0x8001a30260318210132000b0609900034304c1e61624c5400054542a000298a143cc2c450a800472a65400234532a0004229950008cc4ca800106265113cb1d32a00145249500020f24a)))) else (if i < 320 then (if i < 256 then (if i < 224 then 0x8001a31064000d0c83200041439900014a1cc8005128a625a6258532000b2229900050a14c8002430a64000d1853018c10829900034314c80051282625a6258132000b2209900048604c else (if i < 240 then 0xc18409c6400230cd3200040669900004334c8002949664002394b3200041e59900020a2cc8001051264002894832000b224190002cf20c8002651064000e2883200021441900048620c else 0x8001a1c6640014a563200041eb1900020a58c532c42ac6400010d632001452a1900099150c80010528640005294320004149990008e538c4b4c4b1c6400083ce3051e39671900020a38c)) else (if i < 288 then (if i < 272 then 0x800107d06400082a832001187419000043a0c8002d4cc64000e96632000b531989698a88cc800512c664000e96332000b231990004ca8cc800085466400121a33200068d199000a038cc else 0x1430871078a1843483e00141841f00058c20f800166107c00280c83e000b0641f00034320f8005148e7c00239473e00041439f000529a0c800472d0640005968314cb1474183ca1e3a0c) else (if i < 304 then 0x800101a87c00050d43e000086a1f00020334f8001061678a944a093c34a24c49f0008d124f800105127c000e1893e00140649f00014324f8000219278a184a083c50c22c41f00059120f else 0x8002c6028c0005301460014060a3000583051800294d07a52842683e00074b31f000a2950f800472a87c00059543e0011a2a1f00058c50f800465287c00082943e000294a1f0008c350f))) else (if i < 368 then (if i < 336 then 0x800503288c000e194460011ca9a300020a4d18001c3268c0005192460000869230008cc3918002c7908c0005308460009944230004862118002c60a8c00142854600090c2a3000583151 else (if i < 352 then 0x8001c3092c00280c49600068624b00014c8d1800265468c00121a3460014071a300020f5918004662c8c000831646001318a230008cc511800465288c000829446000294a2300010a511 else 0x8000a5272c00281939600070c9cb000a034e58004c61d2c002330e9600029474b000a0c1658005018b2c00240c59600119e24b000a0c125800466092c00232849600029424b000a06125)) else (if i < 400 then (if i < 384 then 0x8000a1c92c00010e4960014191cb00038c8e5800085472c00280e3960007071cb000a0c8a58001c6452c00053229600070714b0008d14e5800467a72c0028313960011989cb0008ca4e5 else 0x800507a94c00243d4a6001418a530008cc529800501a94c00280d2a60013069530008c34a9800506214c0023310a6000b0c853000a03429800466512c00053289600118744b00010a9a5) else (if i < 416 then 0x800263514c00020e8a41a20d1353000a0f9a98001a1cd4c00161a4a600098d253000a039298002c1c94a5441a22a600144b15300058c8a98002c3454c000d1a2a6001318b530008cc5a9 else 0x100050fa29))))) >>> (37*(i % 16))) % 137438953472
def wiress191e4 (i : Nat) : W := bandWord (((if i < 32 then (if i < 16 then (if i < 8 then 0x4300000200008445004300000200008045004300000200000047000180000100004224c01480000080002112a01480000080002110a014000000000021000004800000000001008 else 0xa0000040001087800578000028000a557a0560000028000a55320578000028000a157a0538000028000a057a0520000028000a053205780000280002157a043000002000084470) else (if i < 24 then 0x1c80001080042b90a00c00001000040f800040800007c0000012a01e8000048001297aa01e80000480012978a0128000048001207aa01e00000400012978000e800004000109788 else 0x4f00001200048fc5004b00001200048ec5004500001200048787004500001200048785004100001200048685000d80001100044fa4c00900001100044ea4401c80001080042f92a)) else (if i < 48 then (if i < 40 then 0x900000200005f000004c800017c0000f92a044800017c0000112a05f8000128004afd7a05e0000128004add320558000128004a787a05f80001280042fd7a04f00001200048fc70 else 0x9c00003000057b8000d2800027c001207aa0d0800027c0002012a0c20000274001006800c10000274000402440d30000220005f44700d00000220004240200c30000220001d0450) else (if i < 56 then 0xcb0000320005dec700cb0000320005dec500d50000320004f787009d8000310005ffa4c0990000310005fea440898000310005dea4c09c0000300005ff8000880000300005de800 else (if i < 64 then 0xd2800037c001207aa0d4800037c0002112a0c0000037c000000000c900003740044ea440c800003740040e8000df0000320005ffc700df0000320005ffc500d50000320005f7870 else 0xcd800037c0044fa4c0c9000037c0044ea440dc800037c0042f92a0dc800037c0042b90a0de800037c001297aa)))) >>> (72*(i % 8))) % 4722366482869645213696)
def factss191e4 (i : Nat) : {f : Fact // Sound true f} := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then ⟨item 31 [] 7,claims31⟩ else ⟨item 31 [4] 7,claims31e4⟩) else (if i < 3 then ⟨item 166 [] 4,claims166⟩ else ⟨item 167 [] 7,claims167⟩)) else (if i < 6 then (if i < 5 then ⟨item 172 [] 4,claims172⟩ else ⟨item 187 [] 7,claims187⟩) else (if i < 7 then ⟨item 187 [4] 7,claims187e4⟩ else (if i < 8 then ⟨item 189 [] 8,claims189⟩ else ⟨item 189 [4] 8,claims189e4⟩)))) else (if i < 13 then (if i < 11 then (if i < 10 then ⟨item 190 [] 7,claims190⟩ else ⟨item 30 [] 4,claims30⟩) else (if i < 12 then ⟨item 27 [] 4,claims27⟩ else ⟨item 15 [] 4,claims15⟩)) else (if i < 15 then (if i < 14 then ⟨item 57 [] 4,claims57⟩ else ⟨item 163 [] 4,claims163⟩) else (if i < 16 then ⟨item 23 [] 4,claims23⟩ else (if i < 17 then ⟨item 29 [] 4,claims29⟩ else ⟨item 177 [] 4,claims177⟩)))))
def recss191e4 (i : Nat) : Recipe := ((if i < 40 then (if i < 16 then (if i < 8 then #[(0,[]),(0,[257]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])] else #[(7,[]),(8,[]),(9,[]),(10,[]),(0,[129]),(1,[129]),(3,[129]),(11,[])]) else (if i < 24 then #[(8,[65]),(12,[]),(0,[130]),(1,[130]),(13,[]),(14,[]),(0,[131]),(1,[131])] else (if i < 32 then #[(3,[131]),(1,[193]),(6,[129]),(8,[129]),(0,[193]),(5,[129]),(3,[257]),(5,[321])] else #[(1,[261]),(6,[197]),(0,[265]),(1,[265]),(8,[197]),(1,[329]),(3,[9]),(8,[389])]))) else (if i < 56 then (if i < 48 then #[(15,[]),(16,[]),(9,[197]),(1,[330]),(3,[10]),(17,[]),(8,[390]),(1,[331])] else #[(3,[11]),(8,[269]),(3,[17]),(8,[405]),(5,[66]),(1,[129,193]),(0,[129,86]),(1,[130,217])]) else (if i < 64 then #[(1,[131,193]),(1,[193,261]),(1,[193,329]),(1,[193,330]),(8,[129,269]),(8,[129,405]),(1,[261,329]),(1,[261,330])] else (if i < 72 then #[(8,[389,269]),(1,[329,90]),(3,[9,86]),(6,[90]),(1,[329,218]),(6,[154]),(8,[389,158]),(1,[146])] else #[(1,[147])])))) : Array Recipe).getD (i % 8) default
def levs191e4k5 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x271c50d425,0,0x40127,0x0,0x0,0x0⟩,⟨0x270e50d425,0,0x4b019,0x0,0x0,0x0⟩,⟨0x428f92315,0,0x67102,0x0,0x0,0x0⟩,⟨0x82869a425,0,0x92019,0x0,0x0,0x0⟩,⟨0x828695425,0,0x4b019,0x0,0x0,0x0⟩,⟨0x2728692425,0,0x41161,0x0,0x0,0x0⟩,⟨0x2728683425,0,0x2304c,0x0,0x0,0x0⟩,⟨0x8286a1265,0,0x5104b,0x0,0x0,0x0⟩] else (if i < 16 then #[⟨0x808516315,0,0xa0a5,0x0,0x0,0x0⟩,⟨0xc3d08518a16,0,0x0,0x0,0x0,0x426⟩,⟨0xc0428c42c26,0,0x0,0x0,0x0,0x132⟩,⟨0xc3d085122f6,0,0x0,0x0,0x0,0x0⟩,⟨0xc0808517c26,0,0x0,0x0,0x0,0x0⟩,⟨0xc3d0890db16,0,0x0,0x0,0x0,0x21322b⟩,⟨0xc3d28911b16,0,0x0,0x0,0x0,0x213156⟩,⟨0x428918c25,0,0x108163,0x0,0x0,0x0⟩] else #[⟨0xc0808521156,0,0x0,0x0,0x0,0x1a4⟩,⟨0x808516a65,0,0x1560f9,0x0,0x0,0x0⟩,⟨0x3d08791315,0,0x1a0d7,0x0,0x0,0x0⟩,⟨0x3d068d1315,0,0x730d7,0x0,0x0,0x0⟩])) : Array Ticket).getD (i % 8) default
def levs191e4k6 (i : Nat) : Ticket := ((if i < 72 then (if i < 32 then (if i < 16 then (if i < 8 then #[⟨0xc3d1e206b16,0,0xfb0ce,0x0,0x0,0x0⟩,⟨0x6138f1038d427,0,0x0,0x0,0x0,0xf0⟩,⟨0xc3d1e1072f6,0,0xf4133,0x0,0x0,0x0⟩,⟨0x1e8f0838bb16,0,0xd30f6,0x0,0x0,0x0⟩,⟨0x6078808398c27,0,0x0,0x0,0x0,0x18c327⟩,⟨0xc3d4e2099a6,0,0x11019,0x0,0x0,0x0⟩,⟨0xc3d4e109a06,0,0x59018,0x0,0x0,0x0⟩,⟨0xc3d10109b16,0,0x24,0x20000301,0x11,0x0⟩] else #[⟨0x61e8f080903a7,0,0x0,0x0,0x0,0x115e799b⟩,⟨0x61ea7080901d7,0,0x0,0x0,0x0,0x11422bcf⟩,⟨0x1e8f08092316,0,0x670d0,0x0,0x0,0x0⟩,⟨0x613961e386be7,0,0x0,0x0,0x0,0xe94738b4⟩,⟨0xc271e39f1a6,0,0x3d127,0x0,0x0,0x0⟩,⟨0xc0f0839f316,0,0x109138,0x0,0x0,0x0⟩,⟨0x60b0f0839f257,0,0x0,0x0,0x0,0x7b0c6129372⟩,⟨0x61ea72c386947,0,0x0,0x0,0x0,0x84ce5888833⟩]) else (if i < 24 then #[⟨0xc3d4e38a1a6,0,0x12127,0x0,0x0,0x2⟩,⟨0x138f0638d426,0,0x40127,0x0,0x0,0x2⟩,⟨0xc3d4e105946,0,0xde05c,0x0,0x0,0x0⟩,⟨0xc3d0838a316,0,0x133,0x20000301,0x11,0x0⟩,⟨0x13960838a426,0,0xa4163,0x0,0x0,0x2⟩,⟨0x61ea71e0c58a7,0,0x0,0x0,0x0,0x15ab75⟩,⟨0xc3d4e1ca1a6,0,0x11019,0x0,0x0,0x5⟩,⟨0x138f061cd426,0,0x40127,0x0,0x0,0x5⟩] else #[⟨0xc3d4e10f946,0,0x59018,0x0,0x0,0x0⟩,⟨0xc3d081ca316,0,0x24,0x20000301,0x11,0x0⟩,⟨0x1396081ca426,0,0x2110b,0x0,0x0,0x5⟩,⟨0x61e8f080cfb97,0,0x0,0x0,0x0,0x115e799b⟩,⟨0x61ea7080cf9c7,0,0x0,0x0,0x0,0x11422bcf⟩,⟨0x1e8f080d2316,0,0x670d7,0x0,0x0,0x0⟩,⟨0xc271051f1a6,0,0x42127,0x1e01,0x0,0x1⟩,⟨0xc271010a2d6,0,0x164,0x20000b01,0x11,0x0⟩])) else (if i < 48 then (if i < 40 then #[⟨0x613880851f207,0,0x0,0x0,0x0,0x2820c105042192⟩,⟨0xc080851f316,0,0x139,0x20000301,0x40011,0x4⟩,⟨0x60b080851f257,0,0x0,0x0,0x0,0x6aa551a5249d40c3⟩,⟨0x13960851f246,0,0xa4163,0x0,0x0,0x8⟩,⟨0x13960851f066,0,0x48022021,0x0,0x0,0x0⟩,⟨0x78406f92316,0,0x67102,0x0,0x0,0x8⟩,⟨0x5878406f92867,0,0x0,0x0,0x0,0x6aa52⟩,⟨0xc3d4e20d106,0,0x19014,0x0,0x0,0x0⟩] else #[⟨0xc3d1e20d336,0,0x313d,0x0,0x0,0x0⟩,⟨0xc271e20d436,0,0x415f,0x0,0x0,0x0⟩,⟨0xc3d1e20cb46,0,0x3308e,0x0,0x0,0x0⟩,⟨0xc3d1050d346,0,0x19091,0x0,0x0,0xb⟩,⟨0x7880669a426,0,0x92127,0x0,0x0,0xb⟩,⟨0xc271e20d3c6,0,0x4315f,0x0,0x0,0x0⟩,⟨0xc271050d446,0,0x19043,0x0,0x0,0x0⟩,⟨0x138f100cd2b6,0,0x43082,0x0,0x0,0x0⟩]) else (if i < 56 then #[⟨0xc3d1050d2a6,0,0x1108b,0x0,0x0,0xe⟩,⟨0x78806695426,0,0x40127,0x0,0x0,0xe⟩,⟨0xc27105201a6,0,0x19053,0x0,0x0,0x0⟩,⟨0xc3d4e50d246,0,0xa006c012,0x0,0x0,0x11⟩,⟨0xc3d4e50d066,0,0x12,0x10001520000302,0x0,0x1400800400801066318199b0⟩,⟨0x271050d425,0,0x0,0x10003901,0x7e63782704802e038058013,0x18000080db600002492eb800019249249a7⟩,⟨0xc271050d426,0,0x42,0x0,0x7e66c0648c309c1200a0113,0x22b75b557992⟩,⟨0x13880650d426,0,0x40127,0x0,0x0,0x2802⟩] else (if i < 64 then #[⟨0x61ea71e0d20a7,0,0x0,0x0,0x0,0x84021cab0fc⟩,⟨0xc3d4e3cd1e6,0,0x6055,0x0,0x0,0x0⟩,⟨0x61ea71e6921e7,0,0x0,0x0,0x0,0x1080fa8fc10e3f0fabc0⟩,⟨0x61ea706692227,0,0x0,0x0,0x0,0x8407d443a28⟩,⟨0x138f06692426,0,0x41161,0x0,0x0,0x11⟩,⟨0xc3d4e3cd0c6,0,0xa9128,0x0,0x0,0x0⟩,⟨0x138f06683426,0,0x12b044,0x0,0x0,0x14⟩,⟨0x138f106a13b6,0,0x40168,0x0,0x0,0x0⟩] else #[⟨0x138f100cd3b6,0,0x40127,0x0,0x0,0x0⟩,⟨0x788066a1266,0,0x51040,0x0,0x0,0x17⟩,⟨0xc271e20d3b6,0,0x15f,0x0,0x0,0x6e50d5b049e⟩,⟨0x6138f106a13b7,0,0x0,0x0,0x0,0xc91e032646444⟩,⟨0x60788066a1267,0,0x0,0x0,0x0,0xc991edc876c8c⟩,⟨0xc3d1010a3a6,0,0x1b087,0x0,0x0,0x0⟩,⟨0xc3d085102a6,0,0x8b147,0x0,0x0,0x0⟩,⟨0xb0808515426,0,0x4701b,0x0,0x0,0xe⟩])))) else (if i < 104 then (if i < 88 then (if i < 80 then #[⟨0xc3d10101b56,0,0xfe0e4,0x0,0x0,0x0⟩,⟨0xb0f10101a96,0,0x9c047,0x0,0x0,0x0⟩,⟨0xc271010a2e6,0,0x115164,0x0,0x0,0x0⟩,⟨0xc0808520316,0,0x1b115,0x0,0x0,0x1a⟩,⟨0x13961010a2c6,0,0xa0a5,0x0,0x0,0x1a⟩,⟨0xc271010a3f6,0,0xec164,0x0,0x0,0x0⟩,⟨0x6138808510427,0,0x0,0x0,0x0,0xc7a0a192⟩,⟨0xc3d10518b46,0,0x1b19a,0x0,0x0,0x0⟩] else #[⟨0xc3d08518ba6,0,0x1b0d8,0x0,0x0,0x0⟩,⟨0xc3d08518856,0,0x1b,0x0,0x0,0x9c0803481d⟩,⟨0xc3d1010a2f6,0,0x1b,0x0,0x0,0x9c09834823⟩,⟨0xc3d08512316,0,0x0,0x20000520000302,0x678b95501b02643183482f0580a4020014,0x7400050701111601311118000b20a9⟩,⟨0xc3d08503316,0,0x24,0x20000301,0x11,0x0⟩,⟨0x61e8808512317,0,0x0,0x20000301,0x0,0x108c3482309cb8827001⟩,⟨0xc0808518c26,0,0x0,0x1920000520000303,0x2119b03240c81782604001c020014,0x95002222473701011118110062⟩,⟨0x61ea72c1121b7,0,0x0,0x0,0x0,0x2130294080cd15bcf⟩]) else (if i < 96 then #[⟨0x61ea72c512237,0,0x0,0x0,0x0,0x42605844419956⟩,⟨0x61ea7085120b7,0,0x0,0x0,0x0,0x2131114080cd02111⟩,⟨0x139608512426,0,0xa4163,0x0,0x0,0x17811⟩,⟨0x139608503426,0,0x2110c,0x0,0x0,0x14⟩,⟨0x1388085212d6,0,0x4716c,0x0,0x0,0x35⟩,⟨0xb0808521266,0,0x10b047,0x0,0x0,0x1a817⟩,⟨0x61388085212d7,0,0x0,0x0,0x0,0x259c8963d24a29832⟩,⟨0x60b0808521267,0,0x0,0x0,0x0,0xd54ab248190c3⟩] else #[⟨0x1e8406512316,0,0x670e0,0x0,0x0,0x8⟩,⟨0x61e8f080d02f7,0,0x0,0x0,0x0,0x5044c827117⟩,⟨0xc3d10101b86,0,0xfe0e4,0x0,0x0,0x0⟩,⟨0xc3d10118916,0,0xb0df,0x0,0x0,0x0⟩,⟨0xc3d1e218b26,0,0xce002,0x0,0x0,0x0⟩,⟨0xc3d1e218346,0,0xb198,0x0,0x0,0x0⟩,⟨0xc3d1e118b76,0,0xd105e,0x0,0x0,0x0⟩,⟨0x61e8f08918b07,0,0x0,0x0,0x0,0x2f498a090872f1⟩])) else (if i < 120 then (if i < 112 then #[⟨0x1e8f06918b46,0,0x6719b,0x0,0x0,0x0⟩,⟨0xc3d1e118b66,0,0xd805e,0x0,0x0,0x0⟩,⟨0x1e8f080d8a86,0,0xd8063,0x0,0x0,0x0⟩,⟨0xc3d1e118896,0,0xfc133,0x0,0x0,0x0⟩,⟨0x1e8f080d8a16,0,0xd7067,0x0,0x0,0x0⟩,⟨0x61e8f080d8a17,0,0x0,0x0,0x0,0x6064c80e917⟩,⟨0x6078406c42c27,0,0x0,0x0,0x0,0x26408199c2c⟩,⟨0x1e8f080d22f6,0,0x670d7,0x0,0x0,0x0⟩] else #[⟨0x61e8f080d22f7,0,0x0,0x0,0x0,0xc0c11917⟩,⟨0x60788080d7c27,0,0x0,0x0,0x0,0x9999c56⟩,⟨0x1e8f0890f316,0,0xb50d7,0x0,0x0,0x38⟩,⟨0x1e8f080cf316,0,0x670d7,0x0,0x0,0x0⟩,⟨0x1e8f06911b16,0,0xfd0d7,0x0,0x0,0x3b⟩,⟨0x1e8406911316,0,0xfd0d7,0x0,0x0,0x1d838⟩,⟨0x1e8f100d1b16,0,0x12e,0x0,0x0,0x71b35d12a79⟩,⟨0xf478806911b17,0,0x0,0x0,0x0,0x70f35d412f4⟩]) else (if i < 128 then #[⟨0xf440406911317,0,0x0,0x0,0x0,0x504e1d7a39c⟩,⟨0xc3d1e10f316,0,0x5e,0x20001501,0x11,0x0⟩,⟨0x61e8f0890f317,0,0x0,0x0,0x0,0x5e8c557a20a22e0a48ba0a⟩,⟨0x61e8f06911b17,0,0x0,0x0,0x0,0x181b157140b0ab117⟩,⟨0x61e8406911317,0,0x0,0x0,0x0,0x30362a8a105029⟩,⟨0x78406918c26,0,0x67108,0x0,0x0,0x2f⟩,⟨0xc3d1e106316,0,0xdb0f6,0x0,0x0,0x0⟩,⟨0x61e8f100d1b17,0,0x0,0x0,0x0,0x720e294104e⟩] else (if i < 136 then #[⟨0x61e88080d1317,0,0x0,0x0,0x0,0x624a082704e⟩,⟨0x60788080e1157,0,0x0,0x0,0x0,0x3480c926495⟩,⟨0xc0f10118bb6,0,0xb165,0x0,0x0,0x0⟩,⟨0x6078808c613b7,0,0x0,0x0,0x0,0x2642ae4ac56⟩,⟨0x1ea72c10f226,0,0xb301a,0x0,0x0,0x38⟩,⟨0x1ea72c0d1a26,0,0xb9073,0x0,0x0,0x3b⟩,⟨0x1ea71e0d18b6,0,0x12507d,0x0,0x0,0x0⟩,⟨0xf5396100d1a27,0,0x0,0x0,0x0,0x70ea08acad0⟩] else #[⟨0x61ea71e10f0b7,0,0x0,0x0,0x0,0x8107e3c9⟩,⟨0x788080d6a66,0,0x16b136,0x0,0x0,0x35⟩,⟨0x6138f1011dad7,0,0x0,0x0,0x0,0x1254f30ab⟩]))))) : Array Ticket).getD (i % 8) default
def levs191e4k7 (i : Nat) : Ticket := ((if i < 56 then (if i < 24 then (if i < 8 then #[⟨0x61ea72c3c40d7,0,0x5d0ed,0x0,0x0,0x2⟩,⟨0x30f53961e2070d8,0,0x0,0x0,0x0,0x42c85837914750f9037b72⟩,⟨0x61ea71e2071a7,0,0x127,0x0,0x0,0xc18053f07e07e0fc⟩,⟨0x30f538f101070b8,0,0x0,0x0,0x0,0x10b216216cfd62372⟩,⟨0x61e8f10107317,0,0x139,0x10000d01,0x0,0x101c7ecfd80b22845004002⟩,⟨0xf53961e107177,0,0xab0f1,0x0,0x0,0xb⟩,⟨0x309cb0f10107428,0,0x0,0x0,0x0,0x3490b00e3f10a4028d2⟩,⟨0x61ea71e2011a7,0,0x127,0x20001530000302,0x44020012,0x9⟩] else (if i < 16 then #[⟨0x61ea72c202137,0,0x0,0x20003710001a20001520000b30000530000306,0x170280440800d01401c020014,0x50550004302250555055800047005455515551550100601505555⟩,⟨0x61ea71e101207,0,0x58,0x20001520700f02,0x0,0x10080500e90520a318829b020a0d80600c0080108281a⟩,⟨0x61e8f10101317,0,0x139,0x20001530000302,0x4005c020012,0x39⟩,⟨0xf53961e101247,0,0xd00f1,0x0,0x0,0x20⟩,⟨0x613961e1073e7,0,0x0,0x701f10000d20000b30000530000305,0xec5a102c0520981180d01401c020014,0x334022832230337902200303300000a013133010060100511133⟩,⟨0x30f53961e0c70d8,0,0x0,0x803401,0x0,0xb416e0015a0ea1ba90e6e40bc11914⟩,⟨0x61ea71e0c71a7,0,0x127,0x30000301,0x6a0c8130012,0xc21⟩,⟨0x61ea72c107147,0,0x0,0x20003500701d20000b30000530000305,0xcfc1f03b0700c81780d01401c020014,0x40449440030002240444044800a0700014144414401006510144404444⟩] else #[⟨0x61ea71e1018b7,0,0x5b,0x0,0x0,0xb40ba0380828d03db3f⟩,⟨0x30f538f080c70b8,0,0x0,0x0,0x0,0x10e2e8b419f90e468dc9a107b⟩,⟨0x61e8f080c7317,0,0x139,0x10000e30000302,0x760a4020012,0x72⟩,⟨0x9cb0f080c7427,0,0x1070f5,0x0,0x0,0x1f035⟩,⟨0x61ea71e0c39a7,0,0x127,0x20001530000302,0x8e110020012,0x309⟩,⟨0x61ea72c103947,0,0x0,0x20003810001a20001520000b30000530000306,0x2804d0941100800d01401c020014,0x505590004302250555055800047005155515501006015455505555⟩,⟨0x61ea71e1019f7,0,0x58,0x20001520700f02,0x0,0x10081282b10520a318829b020a0d80600c00801082853⟩,⟨0x61e8f080c3b17,0,0x139,0x20001530000302,0xb2134020012,0x39⟩])) else (if i < 40 then (if i < 32 then #[⟨0xf53961e101a47,0,0xd70f1,0x0,0x0,0x59⟩,⟨0x9cb0f080c3c27,0,0x107,0x20000b30000302,0xa011c020012,0x1c2⟩,⟨0x309cb0f101073e8,0,0x0,0x10801f10000d30000303,0x0,0x3801008e8800801852011b90d2⟩,⟨0x30f53961e2018d8,0,0x0,0x20803610803402,0x0,0x834800ad07501bdb906f09c1bc6906f⟩,⟨0x30f539610107148,0,0x0,0x20003510801d30000303,0x0,0x211804002e4c00a9400edc8273f3⟩,⟨0x30f538f101018b8,0,0x0,0x20101101,0x0,0x2165d000a9421642db910b⟩,⟨0x6138f100df1a7,0,0x127,0x10001e30000302,0xb8098020012,0x72⟩,⟨0x613961010a3e7,0,0x0,0x10001920000b30000530000304,0x21199e0dc1ac340650c41802f85c01401c020014,0x23320060d0ba00003320323932230338000700032253c33011031330100401113333⟩] else #[⟨0x6138f10101ad7,0,0x164,0x30000b01,0x2f8011,0x10⟩,⟨0x309c788080df208,0,0x0,0x0,0x0,0x1052e8438313098284143d992⟩,⟨0x60788080df317,0,0x139,0x30000301,0xe2194148012,0xc21⟩,⟨0x3058788080df258,0,0x0,0x30000b01,0x0,0xe8ce4008d2002004008684a4dc816495⟩,⟨0x9cb0f080df247,0,0x102114,0x0,0x0,0x3886b⟩,⟨0x9cb0f080df067,0,0x0,0x10002b10001f20000f30000530000305,0x7621d03700d01401c020013,0x1a412081c1200050078640400402644838e4⟩,⟨0x61ea71e20d007,0,0x12706e,0x0,0x0,0x77⟩,⟨0x61ea71e20d197,0,0x127,0x20101130000502,0x800fa1e8020013,0x405a⟩]) else (if i < 48 then #[⟨0x61e8f100cd347,0,0x127091,0x0,0x0,0x21841880⟩,⟨0x6138f100cd447,0,0x127043,0x0,0x0,0x23c46089⟩,⟨0x61e8f100cd2a7,0,0x12708b,0x0,0x0,0x4a892⟩,⟨0xc3d4e20a1a6,0,0x0,0x20003920000302,0x3f31482844f09b130248460830900c0020014,0x11111b11a1111202098000011111111111116111111171111111130300c30111115111111141133330330⟩,⟨0x61ea7100ca1a7,0,0x127,0x20003930000302,0x5385c0880c8020013,0x8a0031a⟩,⟨0x61ea71e0cd247,0,0x0,0x20003e00002130000530000304,0x5b0b31602b45509b01401c020014,0x3033933020030333033000040080003033330761031333133105133⟩,⟨0x61ea71e0cd067,0,0x0,0x20003f10002120001520701430000530000306,0xbc1722780800d01401c020014,0x50558550433505550550000600335055550472051555155105455⟩,⟨0x30f538f100cd248,0,0x0,0x20003e10002130000530000304,0x0,0x10740386c6e40040522200203db9004⟩] else #[⟨0x138f100cd426,0,0x0,0x10003210002002,0x1b90f018a3085f8bd14e2844a88608e0d4020014,0xb0000001001111111111176111111110000050088880000008888328a9000004ccccddddc88c⟩,⟨0x6138f100cd427,0,0x0,0x10002030000530000303,0x19e19c32c648c817a2f05b0a400e014020014,0x33330090706533b3000030330000400003c33003300020a8011031331011⟩,⟨0x61e961010a2a7,0,0x1b08b,0x0,0x0,0x1ae35068892⟩,⟨0x61e8f10101ba7,0,0x139087,0x0,0x0,0x688da⟩,⟨0x61e8f080d02a7,0,0x8b13f,0x10702201,0x0,0x8d4⟩,⟨0x58788080d5427,0,0x8b047,0x0,0x0,0x35c4a8dd⟩,⟨0x613961010a407,0,0x1b115,0x0,0x0,0x1cc38c70098⟩,⟨0x61ea71010a127,0,0x1b,0x20100b00000430000303,0x1d201c020012,0x4b⟩]))) else (if i < 88 then (if i < 72 then (if i < 64 then #[⟨0x61ea71010a207,0,0x1b,0x0,0x0,0x9c3b08404521c4386a0d1⟩,⟨0xc3d1010a316,0,0x0,0x10003c10001920000520000304,0x2084047f0fb1f03d4790ef1c63443484e01401c020014,0x22222f50e0dc0000202222224444b6a901102222232231310130333131333822222722404040402222⟩,⟨0x61ea72c10a247,0,0x0,0x20003a00001a30000530000304,0x4408690a20e3ec4d83801401c020014,0x3033a330002003033303360009401313331330100501813033337033⟩,⟨0x61ea72c10a067,0,0x0,0x20003b10001a20001530000530000305,0x1131fc2782500d01401c020014,0x40448200300404440447000354144414401006014044444344⟩,⟨0x30f53961010a248,0,0x0,0x20003a00002a10001a30000304,0x0,0x84601003901002a500503009cfcc27001⟩,⟨0x13961010a426,0,0x0,0x10003d10003210001903,0x11922c35c690a109c01c020014,0x8000000111111111111170000060055550000020011111211422222222222200000033333111⟩,⟨0x613961010a427,0,0x0,0x10001930000530000303,0x18919e23e470899102083b0520600be01c020014,0x22220040d098000022b200202270006000a32c22011021220100501112200⟩,⟨0x30f5388080ca208,0,0x0,0x0,0x0,0x2728221cf482706221043887192⟩] else #[⟨0x61e88080ca317,0,0x139,0x10001930000302,0x9106509a0ec020013,0x802831a⟩,⟨0xf5396080ca247,0,0xe0,0x30000301,0x488358012,0x2001⟩,⟨0xf5396080ca067,0,0x0,0x20003b10001d20001530000530000305,0x3700d01401c020013,0x10490482001c3243202003049520e09248e4⟩,⟨0x7a9cb08080ca248,0,0x0,0x10002a10001a30000303,0x0,0x1d400100ea74273f384601027001⟩,⟨0x9cb08080ca427,0,0x107,0x20000b30000302,0xa70a00f8020013,0x811a⟩,⟨0x30f4788080d03a8,0,0x0,0x30001501,0x0,0x5d0ba1740021392d99279e4940d001⟩,⟨0x61ea7101019d7,0,0xea0e2,0x0,0x0,0x128⟩,⟨0x30f5388080d01d8,0,0x0,0x0,0x0,0x5d0ba174402f480eb5109c8052dbcf⟩]) else (if i < 80 then #[⟨0xf538f080d0177,0,0x610d7,0x0,0x0,0x0⟩,⟨0x309c788080d0428,0,0x0,0x0,0x0,0x6245d07630982841616192⟩,⟨0x61e8f10118817,0,0xb119,0x0,0x0,0x12b⟩,⟨0x61e8f10118b07,0,0xb,0x30001101,0x0,0x46901e26eea000ba80024d09892e⟩,⟨0x61e8f100d8b47,0,0x13919a,0x0,0x0,0x4e877931⟩,⟨0x61e8f080d8ba7,0,0x1390d8,0x0,0x0,0x5007913d⟩,⟨0x61e8f080d8857,0,0x139,0x10004820001102,0x0,0x8531d414928c3d400943⟩,⟨0x61e8f10101af7,0,0x139,0x10004720001102,0x0,0x8555d415229e3e000808⟩] else #[⟨0x1e8f080d2316,0,0x0,0x10004010002610002503,0x2f4504584af15b2b04e8991220e201c020014,0x1001111141111a11111110000020011111211222222222292222226000003b87550500000c000000⟩,⟨0xf4788080d2317,0,0x139,0x10002620001520000303,0x0,0x16a00e004a796775059010004⟩,⟨0xf4788080cbb17,0,0x139,0x20001530000302,0xb202c020012,0x2403⟩,⟨0x61e8f080d2317,0,0x0,0x10002530000530000303,0x7506c0bc9762e65c0b69371f601c020014,0x202222290b2022000020220000380000110212201000171111a00202206540b2⟩,⟨0x61e8f080c3317,0,0x139,0x20001530000302,0x0,0x4008010b23f80217c⟩,⟨0x30f4788080d2318,0,0x0,0x10002520001530000303,0x0,0x3b1275000400901304004a917f75001000804⟩,⟨0x60788080d8c27,0,0x0,0x30000530000300000200000104,0x6246c0c918b310614bc9552984106900e01401c020014,0x222f90100222222622228d7d23232223333e33222224522cba1⟩,⟨0xf53961e1121e7,0,0xd70b3,0x0,0x0,0xac18e⟩])) else (if i < 104 then (if i < 96 then #[⟨0xf53961e1019e7,0,0xd7,0x30001520100f02,0x56c020012,0x156515⟩,⟨0xf53961e0d2237,0,0xd70f1,0x0,0x0,0x578ca191⟩,⟨0xf5396080d2227,0,0xd70f1,0x0,0x0,0x584c898e⟩,⟨0xf538f080d20b7,0,0xf107d,0x10002601,0x0,0x994⟩,⟨0xf53961e1018c7,0,0x14d,0x20000f30000302,0x20011,0x1⟩,⟨0xf53961e201a37,0,0x0,0x10004320004220004103,0x1c23726d25906904e02a01c020014,0x100010061112711181010001001111111411910002002305000021210000⟩,⟨0x7a9cb0f100d2238,0,0x0,0x20004222102902,0x0,0x2ce011b4997008a0968001⟩,⟨0xf539610101a27,0,0x0,0x10004610004520004410002604,0xcd82703601401c020013,0x20920900200928900b24b2430136db8ce249410a28249⟩] else #[⟨0x7a9cb08080d2228,0,0x0,0x10004622102802,0x0,0x2d4a0941197008b4025801⟩,⟨0x7a9c788080d20b8,0,0x0,0x10002622101102,0x0,0x10ba10b008da568001⟩,⟨0x9cb0f10101c17,0,0x10a,0x20100b30000302,0x20011,0x8⟩,⟨0x61ea72c3c21e7,0,0x5d,0x30001501,0x5b4568012,0x8010⟩,⟨0x30f53961e1121e8,0,0x0,0x0,0x0,0x43f1dd6817033481c8a10716045103bc9⟩,⟨0x30f53961e0d2238,0,0x0,0x4301,0x0,0x32a672004b990e154428ab114⟩,⟨0x30f5396080d2228,0,0x0,0x4501,0x0,0x32a672004bb2011668a103907⟩,⟨0x30f538f080d20b8,0,0x0,0x0,0x0,0xbd4895044350090e21c8045519a⟩]) else (if i < 112 then #[⟨0x9cb0f080d2427,0,0x108114,0x0,0x0,0x5e4880b6⟩,⟨0x61ea72c3c20c7,0,0xa914d,0x0,0x0,0xbe0b9⟩,⟨0x9cb0f080c3427,0,0x10a,0x30000301,0x44c5e0012,0x81⟩,⟨0x30f53961e201a38,0,0x0,0x10004320004102,0x0,0x2348020016d25fdb904e⟩,⟨0x30f539610101a28,0,0x0,0x10004520004402,0x0,0x2cd802001304dc82704e⟩,⟨0x9cb0f101213b7,0,0x107167,0x0,0x0,0xbf⟩,⟨0x9cb0f10101bb7,0,0x107,0x30001101,0x610011,0x1⟩,⟨0x9c788080e12d7,0,0x4716b,0x0,0x0,0xce916⟩] else #[⟨0x58788080e1267,0,0x107047,0x0,0x0,0x6748c8c5⟩,⟨0x613961e2023b7,0,0x165,0x30001101,0x620640012,0x810⟩,⟨0x309cb0f101213b8,0,0x0,0x0,0x0,0x31b8ee34a4ac56316680658ab⟩,⟨0x309c788080e12d8,0,0x0,0x0,0x0,0x4b0624c4a4945330a470f31a0⟩,⟨0x3058788080e1268,0,0x0,0x101,0x0,0x636ce400c9230a47c67495⟩])))) : Array Ticket).getD (i % 8) default
def levs191e4k8 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x30f53961e2020e8,0,0x0,0x10001030800f20000e20000d20800c00000a10000720100430000309,0x320580a0130220400700d0160280400700a010010014,0xadeaae8eaae00e4ceb00eccc2c6acaaacaa900c4c007cccccacaaacaaccccccaaa4aa00ffffafaaafaacfcc5cfcc4fff3f1aaaa⟩,⟨0x30f53961e202028,0,0x0,0x30001530801420001320801230101130800f30000b1000071080064000054000030b,0x460800f81d0380680c81702c04c0800d01401c020014,0x905995759950050352f4490999099e0003c66440d0d90999099000000a93990b1b9199919901008010001dd90999903⟩,⟨0x30f53961e1018e8,0,0x0,0x20000e20000d20800c30000b00000700800640000540000308,0x760e01a83205e0b01482602c04c0800d01401c020014,0x6046645f4664002070274460666066e0044700d0c000060666066000000b0110616661660100a010001910060668660366⟩,⟨0x30f53961e101878,0,0x0,0x20001820001720801630001530801430800f30000b1000074000054000030a,0x9a128238440820f80e01902c04c0800d01401c020014,0x8048847f48840040249e3380888088d66330002c060680888088000000b0515818881880100a01000166808888028288⟩,⟨0x187a9cb0f101018e9,0,0x0,0x30101130900f20000e20000d20900c10000a1000071090064000054000030a,0x0,0x41890070020580081903805800ba80020340b0590020582b0136e414c0201602614005001⟩,⟨0x309cb0f10101be8,0,0x0,0x10801f20001e30000b40000540000310000210000110800008,0x3b166c6783886e0d61a0328620be1702802602c04c0800d01401c020015,0xa21146338e638c02228c45009e229443109c318da3194a6188a560c631886210c6318c6b18c741484219083110421906350c8318c8420c6210c634a021⟩,⟨0x61ea71e2019a7,0,0x0,0x10002120002000700830000510000430000306,0x6e42544908f118224430831001f43d0770e81701f02c02e0400680a01001c020015,0x5294a5b14b5294a5294c0a0272294a500000294a5284a5294a5284a50802000000084318040100425294a5294a5794a0084a5294aa294a5294a5302e04a0e300840210a5294ae294a5294ad294c2b88021018b⟩,⟨0x30f4b0f10101aa8,0,0x8b,0x30800f10000710000110800004,0x0,0x45080a00e01c0500700e2784d89800820003807⟩] else (if i < 16 then #[⟨0x61ea72c202147,0,0x0,0x10001b10001a20001900000a30000510000430000307,0x2f05c8b61662c0568aa14e2904c08309c04c0800d01401c020015,0x2108424884890842141003dc00000109084200232108420484210842048468401004216000002c2421084210844908010804210843108421084310800840130428288c2008c0318842108a2108421084280e0⟩,⟨0x30f539610101948,0,0x0,0x10801d20801c10001a20001930000b10000a40000540000308,0x33c338658c818a3085f8860be1582082f02c04c0800d01401c020015,0x2006420cd219083000e08820f0000018c8021080211c0001a00006310004990800840409084090800800c0042000400200842108b21084000a0501280008021084⟩,⟨0x30f538f10101a08,0,0x0,0x10002420002320802230001530800f10000710800610000430000309,0x1741ba3686b8d41a22fc5509e1361940e81902c04c0800d01401c020015,0x3cc87390c439c80010632480025065104a129c2739c2738421085cd0862181ce719cec00108420e839ce839c280846842108294ea39ce7000634800529ce779ceb⟩,⟨0x61e8f10101b17,0,0x0,0x10003130000510000430000310000210000110700007,0x3a82084047f0fb1f03d4790ef1d83a4730e31c03085689b0d011c1c0200260400700d01401c020015,0x110822df07a1e717b54231080018c63088411104220c8318c632108e69064190811083ce739464e433186738442088e210c84190e421cc730cc619ce731cc739e23210221044b10b83e0d494178310e0f08841⟩,⟨0xf53961e101a47,0,0x0,0x10002720002620002530000304,0x2822264408690a20e3c86286e01401c020014,0x1111111112111112116001022b11111211111112110000220000252020a21111131111111311022022022023220330333333931111141111c871111111111⟩,⟨0xf53961e101867,0,0x0,0x10002e20002c20002b30001530001430000f10000630000530000309,0x22c3203881902c04c0800d01401c020014,0x333336636766366367660565572366367663663676655550505777a355336636866366368665474787754747877041434433663696636632b2333333336266⟩,⟨0x7a9cb0f10101a48,0,0x0,0x10002a3010293010281000272000262000253000153010111010081000072010043000030c,0x33624a4888f91c2323d46582304407c0e01902c04c0800d01401c020015,0xc7318c7319c701c0711ca559cf331cc631cc639ce0380e73b4e93a647884c6318c2318c630006418c6418c741ce741ce242048421485410f19a86318c201c023b0a5218c4218c4⟩,⟨0x7a9cb0f10101978,0,0x0,0x20003020002f30102930102830001530101130100f30100b1000074000052010044000032010000d,0x940f81b41281282203e0700c8160260440800d01401c020015,0x18163181632010848f4a4212a0280844c0b18c0b18108421085415308c6306c6306c60461084610846158d6c0b18c6042121907095216b028631008a18c4048e⟩] else #[⟨0x30f53961e101a48,0,0x0,0x20002500000708100640000540000305,0x4e89b9342624b8958fb1602241900d01401c020014,0x4044444e44440320040444044800000d50000404440440000007c001104144414401006010001b1004044440a944⟩,⟨0x30f53961e101868,0,0x0,0x20002b30001530801430800f10000740000540000307,0xa013d1fc2cc4604a08804c0800d01401c020014,0x6036636d36630280060666066b5500027050560666066000000a041461666166010090100015560666602c6266⟩,⟨0x187a9cb0f10101a49,0,0x0,0x10002a20002530001539100f10000740000540000307,0x0,0x20cd803801002028099010021645b146002040479430080340080d⟩,⟨0x9cb0f10101c27,0,0x0,0x10003320003230000310000204,0x624548a794c292348670b91422482683b01401c020014,0xe0000002212122110122d000002001111212111112229821212200000700aaaa000003001221232261221232233331331333333000000f1f154fcb⟩,⟨0x309cb0f10101c28,0,0x0,0x40000540000310000210000118100005,0x66cc6ccf15e2b6560aa9402744106e8bc12a1880a00d01401c020015,0x884118e4398d8b0841010c621884a18c6918c631bcc318c621884318c631a0631444219083110421906338c8318c8420c6210c6328dcd⟩])) : Array Ticket).getD (i % 8) default
def levs191e4k9 (i : Nat) : Ticket := (#[⟨0x30f53961e202038,0,0x0,0x10000a1000091080081000071080064000052000044000032000022000012080000b,0x7c0ec1c0350640bc1602904c08c1001f03a0700d01902e0580a0130220400700d0160280400700a010010015,0x442089f010800784420804201c6e9b9b66b2cc5c42108c8a08841110420884111042590641908454c632114418c63210840884111042088411104218c632108320c6318c842271110821108223c8432946942501108224884110822488432106449086990832248439525194a34a46420442088b21044208847192639461⟩] : Array Ticket).getD (i % 8) default
def trees191e4 : Book :=
  ⟨true,inputSet 191 [4],goalAt 191,9,73,readRule factss191e4 recss191e4,hintss191e4,11,unpackState wiress191e4 7,(fun k => match k with | 5 => 20 | 6 => 139 | 7 => 117 | 8 => 21 | 9 => 1 | _ => 0),fun k => match k with
    | 5 => levs191e4k5
    | 6 => levs191e4k6
    | 7 => levs191e4k7
    | 8 => levs191e4k8
    | 9 => levs191e4k9
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless191e4 : ∀ i, i < 73 → Valid true (goalAt 191) ((trees191e4).rule i) := by
  exact validateRules factss191e4 recss191e4 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k5i0 : bookRange trees191e4 5 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k5i16 : bookRange trees191e4 5 16 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e4k5 : allGood trees191e4 5 :=
  book_level trees191e4 5 ruless191e4 (book_empty trees191e4 4 rfl) (@book_split trees191e4 5 0 16 4 passs191e4k5i0 passs191e4k5i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i0 : bookRange trees191e4 6 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i16 : bookRange trees191e4 6 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i32 : bookRange trees191e4 6 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i48 : bookRange trees191e4 6 48 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i64 : bookRange trees191e4 6 64 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i80 : bookRange trees191e4 6 80 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i96 : bookRange trees191e4 6 96 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i112 : bookRange trees191e4 6 112 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k6i128 : bookRange trees191e4 6 128 11 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e4k6 : allGood trees191e4 6 :=
  book_level trees191e4 6 ruless191e4 goods191e4k5 (@book_split trees191e4 6 0 64 75 (@book_split trees191e4 6 0 32 32 (@book_split trees191e4 6 0 16 16 passs191e4k6i0 passs191e4k6i16) (@book_split trees191e4 6 32 16 16 passs191e4k6i32 passs191e4k6i48)) (@book_split trees191e4 6 64 32 43 (@book_split trees191e4 6 64 16 16 passs191e4k6i64 passs191e4k6i80) (@book_split trees191e4 6 96 16 27 passs191e4k6i96 (@book_split trees191e4 6 112 16 11 passs191e4k6i112 passs191e4k6i128))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k7i0 : bookRange trees191e4 7 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k7i16 : bookRange trees191e4 7 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k7i32 : bookRange trees191e4 7 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k7i48 : bookRange trees191e4 7 48 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k7i64 : bookRange trees191e4 7 64 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k7i80 : bookRange trees191e4 7 80 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k7i96 : bookRange trees191e4 7 96 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k7i112 : bookRange trees191e4 7 112 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e4k7 : allGood trees191e4 7 :=
  book_level trees191e4 7 ruless191e4 goods191e4k6 (@book_split trees191e4 7 0 64 53 (@book_split trees191e4 7 0 32 32 (@book_split trees191e4 7 0 16 16 passs191e4k7i0 passs191e4k7i16) (@book_split trees191e4 7 32 16 16 passs191e4k7i32 passs191e4k7i48)) (@book_split trees191e4 7 64 32 21 (@book_split trees191e4 7 64 16 16 passs191e4k7i64 passs191e4k7i80) (@book_split trees191e4 7 96 16 5 passs191e4k7i96 passs191e4k7i112)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k8i0 : bookRange trees191e4 8 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k8i16 : bookRange trees191e4 8 16 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e4k8 : allGood trees191e4 8 :=
  book_level trees191e4 8 ruless191e4 goods191e4k7 (@book_split trees191e4 8 0 16 5 passs191e4k8i0 passs191e4k8i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e4k9i0 : bookRange trees191e4 9 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e4k9 : allGood trees191e4 9 :=
  book_level trees191e4 9 ruless191e4 goods191e4k8 passs191e4k9i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims191e4 : Claim true 191 [4] 10 := by
  apply low_search (s:=true) (T:=goalAt 191) (raw:=rawSet 191) (es:=extraSet 191 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 191 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 191 [4]) (extraWord 191 4) = inputSet 191 [] := by decide +kernel
      change Low true (remove (inputSet 191 [4]) (extraWord 191 4)) (goalAt 191) 10
      rw [eq]
      exact claims191
  · exact book_end trees191e4 goods191e4k9 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims494e12 : Claim true 494 [12] 10 :=
  rename_rows claims191e4 [0,4,7,10,45,48,50,24,27,29,54,2,6,9,47,26,34,37,38,55,42,0,36,0,0,0,0,0,0,0,0,0,0,0,16,19,20,53,31,0,18,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims313 : Claim true 313 [] 7 :=
  rename_rows claims31 [0,1,11,12,7,8,15,45,46,51,50,16,17,22,20,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims313e38 : Claim true 313 [38] 7 :=
  rename_rows claims31e4 [0,7,11,15,1,8,12,16,20,22,17,45,50,51,46,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims319 : Claim true 319 [] 10 :=
  rename_rows claims191 [0,7,11,15,1,8,12,2,9,13,3,4,10,14,5,6,45,50,51,46,47,0,48,0,0,0,0,0,0,0,0,0,0,0,16,20,22,17,18,0,19,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims334 : Claim true 334 [] 7 :=
  rename_rows claims31 [0,2,4,6,7,9,10,45,47,48,50,24,26,27,29,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims334e38 : Claim true 334 [38] 7 :=
  rename_rows claims31e4 [0,7,4,10,2,9,6,24,29,27,26,45,50,48,47,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims347e38 : Claim true 347 [38] 8 :=
  rename_rows claims189e4 [0,45,0,0,1,46,0,11,51,0,12,7,50,0,8,15,24,54,0,25,30,0,29,0,0,0,0,0,0,0,0,0,0,0,2,47,0,3,13,0,9,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims351e38 : Claim true 351 [38] 10 :=
  rename_rows claims191e4 [0,7,4,10,2,9,6,24,29,27,26,45,50,48,47,54,11,15,14,13,30,0,51,0,0,0,0,0,0,0,0,0,0,0,1,8,5,3,25,0,46,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims355 : Claim true 355 [] 7 :=
  rename_rows claims31 [0,1,2,3,24,25,26,45,46,47,54,16,17,18,31,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims379e38 : Claim true 379 [38] 10 :=
  rename_rows claims191e4 [0,45,16,53,1,46,17,11,51,22,12,7,50,20,8,15,24,54,31,25,30,0,29,0,0,0,0,0,0,0,0,0,0,0,2,47,18,3,13,0,9,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims428e38 : Claim true 428 [38] 7 :=
  rename_rows claims31e4 [0,7,4,10,34,38,37,16,20,19,41,45,50,48,55,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims445 : Claim true 445 [] 10 :=
  rename_rows claims191 [0,7,45,50,16,20,53,1,8,46,17,11,15,51,22,12,4,10,48,19,5,0,14,0,0,0,0,0,0,0,0,0,0,0,34,38,55,41,35,0,40,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims31e12 : Claim true 31 [12] 7 :=
  rename_rows claims31e4 [0,2,1,3,11,13,12,7,9,8,15,4,6,5,14,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims167e12 : Claim true 167 [12] 7 :=
  rename_rows claims31e4 [0,2,1,3,16,18,17,34,36,35,41,4,6,5,19,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintss190e12 (i : Nat) : Nat := (0x200098d25300034f8a98001c3127c0012a473e00125298d00024f386 >>> (37*(i % 16))) % 137438953472
def wiress190e12 (i : Nat) : W := bandWord (((if i < 8 then 0x800000200005d000000800001000040e80000b00000500014a6c400a0000040001086800430000030000c6654043000002000084450042000002000084410001000001000042244 else 0xc10000374000422440c0000037400000000) >>> (72*(i % 8))) % 4722366482869645213696)
def factss190e12 (i : Nat) : {f : Fact // Sound true f} := (if i < 1 then ⟨item 30 [] 4,claims30⟩ else ⟨item 166 [] 4,claims166⟩)
def recss190e12 (i : Nat) : Recipe := (#[(0,[]),(1,[])] : Array Recipe).getD (i % 8) default
def levs190e12k5 (i : Nat) : Ticket := (#[⟨0x3876256,0,0x0,0x10600101,0x0,0x181⟩,⟨0x3764296,0,0x0,0x10600001,0x0,0x26⟩,⟨0x8764216,0,0x0,0x0,0x0,0x12f⟩] : Array Ticket).getD (i % 8) default
def levs190e12k6 (i : Nat) : Ticket := (#[⟨0x38764207,0,0x0,0x20700120700002,0x0,0x464020a2⟩] : Array Ticket).getD (i % 8) default
def trees190e12 : Book :=
  ⟨true,inputSet 190 [12],goalAt 190,6,2,readRule factss190e12 recss190e12,hintss190e12,5,unpackState wiress190e12 4,(fun k => match k with | 5 => 3 | 6 => 1 | _ => 0),fun k => match k with
    | 5 => levs190e12k5
    | 6 => levs190e12k6
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless190e12 : ∀ i, i < 2 → Valid true (goalAt 190) ((trees190e12).rule i) := by
  exact validateRules factss190e12 recss190e12 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs190e12k5i0 : bookRange trees190e12 5 0 3 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods190e12k5 : allGood trees190e12 5 :=
  book_level trees190e12 5 ruless190e12 (book_empty trees190e12 4 rfl) passs190e12k5i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs190e12k6i0 : bookRange trees190e12 6 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods190e12k6 : allGood trees190e12 6 :=
  book_level trees190e12 6 ruless190e12 goods190e12k5 passs190e12k6i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims190e12 : Claim true 190 [12] 7 := by
  apply low_search (s:=true) (T:=goalAt 190) (raw:=rawSet 190) (es:=extraSet 190 [12])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 190 12] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 190 [12]) (extraWord 190 12) = inputSet 190 [] := by decide +kernel
      change Low true (remove (inputSet 190 [12]) (extraWord 190 12)) (goalAt 190) 7
      rw [eq]
      exact claims190
  · exact book_end trees190e12 goods190e12k6 (by decide) (by decide +kernel)
def hintss191e12 (i : Nat) : Nat := ((if i < 192 then (if i < 96 then (if i < 48 then (if i < 16 then 0x800105041c00051820e001452087000929043800492821c00134410e0009220870002110438000a8821c00143c10e00049e0870008cc0438001c6021c000d3010e00029808700024a043 else (if i < 32 then 0x1879720a18c3cb4850e00049e28630f2cd1438001250a18c3cb2450e00140c2870009061438002830a1c00121850e00068c2870002461438000430a1c00239420e0009a210700038c083 else 0x800272901c00134480e000a1e40700034f203800127901c00133080e00071840700014c203800265101c000e2880e000a0c407000486203800123101c0024a450e00124a286469424143)) else (if i < 64 then 0x8004929c191a5090e0c61e5c870630f2d23838001279c18c3cb34e0e00119870700024a3831e61671a1c000528d0e00028c68700014a2438000a31218f30b1490e001452407000929203 else (if i < 80 then 0x8001c6461c00053230e000715187000a068c3800483461c00051940e0012529870009254c3234a122618c3cb9130c61e5a49870002114c38001252618f30b4d20e000294907000146483 else 0x8000b2c81a94504e40d4a281d20700014a9038000a3481a94501640c79858b207000a298c3800494c61c0012a630e0009cb1870004d18c38000a8c61c00143e30e00069f18700024f8c3))) else (if i < 144 then (if i < 112 then 0x8002818a3400120c51a00068628d0002431468000418a340024944188d284820d0002111068004660834000d3041a00121420d00024a1061879648834000e3021a00028610d000146a03 else (if i < 128 then 0x528a071a30f30b38d1a00029868d0001433468000a1923400143c81a00071840d00050f1c68001a78e340024945188d284828d00034c1468001250a30c3cb2451a00140628d000903146 else 0x1e6169a43033014d21a0002a290c44c04d4868000a6243400050d21a00124a70d00098f3868001279c311a5034e1861e59a70d0008cc3868001251c34001694d181a20a668c311052346)) else (if i < 160 then 0x8001c646340028a621a00125310d0001515068000a1a8340026a531a00125298d0009254c6234a092630c3cb4931a00042298d00024f4c6234a06a630c3cb3531a00049498ca51413486 else (if i < 176 then 0x8005148e540024a472a000a1e39500024f1ca8001218a5400241842a00048c21500014ca068000a1d0340014a641a0002a320d000a0f9068000a6483400050e41a00145318d0004d18c6 else 0x8002632454002418e2a0004867143cc2d324a1e6167125400131892a00070c4943cc2c524a8002619254000e0c92a00028649500004324a800514905400134482a000a1e41500038c20a)))) else (if i < 288 then (if i < 240 then (if i < 208 then 0x800263026400121813200070c09900034604c800461826400130c13200070609900034304c8000a182640024a542a0009a2a1500015150a800108a65400241932a00090c9950002434ca else (if i < 224 then 0x8001c31064000d1883200118641900038320c8005030a6400241853200090c29900034614c8004618a640024a413200095209900036904c800268826400054413200120c09900050604c else 0x8001c1c664002394e3200041471900004338c8000a31a64000418d320000866983ca24e2cc1e5047166400050cb320012524190004d120c8001c5106400241883200098c41900048620c)) else (if i < 256 then 0x8002630e7c000e1873e00068c39f0003831cf8000b2d0640024a6332000b531990004e58cc8001d2c66400134633200120d1990005068cc800263466400121a33200070d1990003468cc else (if i < 272 then 0x1460859a7c00080cd3e0004d259f0009252cf1818a69678c28434b3c61421259f0002462cf800263127c000e1893e000a0c41f00048620f8005148e7c0012a473e0004d239f0009061cf else 0x800261828c00120c1460002860a3000929a0f800294d07c00249683e00120d41f00052998f800272cc7c00084563e001452a1f00026950f800483287c00131943e00090ca1f0004c350f))) else (if i < 336 then (if i < 304 then 0x800263108c0012188460009864230009061518002830a8c00121854600121e0a300048f0518001a7828c00093c1460009980a300038c0518000a6028c00241814600098c0a3000486051 else (if i < 320 then 0x800483468c00131a34600090d1a30004c38d18000a5288c0008293460000869a3000043491532c89a08a99424d04600028682300058f211800247908c001330846000994423000906211 else 0x528a02c92c00050e49600008724b00038c8e5800483272c00240d39600119874b0009063a58004819d2c001318d960012062cb000906125800272c68c00123e3460009991a30004ca8d1)) else (if i < 352 then 0x800243454c00130e2a6001198b53000a0f529800485294c0024194a6001186952443164429232892214c00243d0a60004948530009064298001c6512c0005328954a282724aa5140e925 else (if i < 368 then 0x800263514c00121a8a6000987453000a0f9a98002654d4a5444424a600141f2530004c6929800503474c00121a3a600121f15300050f8a98001a7c54c00093e2a600120d1530004c68a9 else 0x400243e8a6000a1f453000906a29))))) >>> (37*(i % 16))) % 137438953472
def wiress191e12 (i : Nat) : W := bandWord (((if i < 32 then (if i < 16 then (if i < 8 then 0x1480000080002112a01480000080002110a01f8000000005ffe7c0138000000005f667c0130000000005f44700120000000005b443000e800000000009628003000000000000440 else 0x560000028000a553205580000280002116a04300000200008447004300000200008445004100000200000004001580000180006336e00180000100004224c01780000080002156a) else (if i < 24 then 0xb00000500014a6c400880000500014a38c01e8000048001297aa00a0000040001087800578000038000e777e0438000030000c667c0430000030000c66540578000028000a557a else 0x4e00001200048dc3004500001200048787004400001200048583000c80001100044ba0c01f8000100005ffe7c00c00001000040f80001f80000580016b7ee00b80000500014a7cc)) else (if i < 48 then (if i < 40 then 0xd30000220005f44700d20000220005b443009080002100057220c0900000200005f000004f8000130004cfe7c04f0000130004cfe540458000130004c787c04f00001200048fc70 else 0x9c80003100057ba0c09b8000250005fa7cc0988000250005fa38c09880002500057a38c0980000240005381800d38000230005f667c0d30000230005f66540d0800023000020028) else (if i < 56 then 0xdf8000330005ffe7c0d58000330005f787c0d58000330004f787c0de0000320005fdc300de0000320005bfc300de0000320005bdc3009c8000310005fba0c09c80003100057fa0c else (if i < 64 then 0xd4800037c0002112a0c0000037c000000000c100003740004224408c800035c0044fa0c08c800035c0044ba0c08a800035c0014a78c080800035c0004220c08c000034c00409800 else 0xcd800037c0044fa4c0cb800037c0014a7cc0c8800037c0014a38c0d5800037c0006336e0c1800037c0004224c)))) >>> (72*(i % 8))) % 4722366482869645213696)
def factss191e12 (i : Nat) : {f : Fact // Sound true f} := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then ⟨item 31 [] 7,claims31⟩ else ⟨item 31 [12] 7,claims31e12⟩) else (if i < 3 then ⟨item 57 [] 4,claims57⟩ else ⟨item 167 [] 7,claims167⟩)) else (if i < 6 then (if i < 5 then ⟨item 167 [12] 7,claims167e12⟩ else ⟨item 177 [] 4,claims177⟩) else (if i < 7 then ⟨item 187 [] 7,claims187⟩ else (if i < 8 then ⟨item 189 [] 8,claims189⟩ else ⟨item 190 [] 7,claims190⟩)))) else (if i < 13 then (if i < 11 then (if i < 10 then ⟨item 190 [12] 7,claims190e12⟩ else ⟨item 29 [] 4,claims29⟩) else (if i < 12 then ⟨item 30 [] 4,claims30⟩ else ⟨item 27 [] 4,claims27⟩)) else (if i < 15 then (if i < 14 then ⟨item 163 [] 4,claims163⟩ else ⟨item 15 [] 4,claims15⟩) else (if i < 16 then ⟨item 23 [] 4,claims23⟩ else (if i < 17 then ⟨item 156 [] 4,claims156⟩ else ⟨item 165 [] 4,claims165⟩)))))
def recss191e12 (i : Nat) : Recipe := ((if i < 32 then (if i < 16 then (if i < 8 then #[(0,[]),(0,[133]),(1,[]),(2,[]),(3,[]),(3,[133]),(4,[]),(5,[])] else #[(6,[]),(7,[]),(8,[]),(9,[]),(1,[129]),(4,[129]),(7,[65]),(10,[])]) else (if i < 24 then #[(11,[]),(0,[129]),(3,[129]),(12,[]),(0,[130]),(1,[130]),(13,[]),(3,[130])] else #[(4,[130]),(0,[131]),(1,[131]),(3,[131]),(4,[131]),(0,[193]),(3,[257]),(14,[])])) else (if i < 48 then (if i < 40 then #[(15,[]),(1,[321]),(16,[]),(4,[321]),(1,[323]),(4,[323]),(1,[197]),(9,[129])] else #[(4,[261]),(9,[321]),(0,[265]),(1,[265]),(7,[197]),(8,[197]),(3,[201]),(4,[201])]) else (if i < 56 then #[(7,[261]),(8,[261]),(1,[337]),(7,[77]),(4,[333]),(7,[81]),(1,[129,197]),(4,[129,261])] else (if i < 64 then #[(1,[129,337]),(4,[129,333]),(1,[129,265]),(4,[129,201]),(0,[129,86]),(3,[129,86]),(1,[321,90]),(4,[321,90])] else #[(9,[26]),(17,[]),(1,[197,337]),(4,[261,333])])))) : Array Recipe).getD (i % 8) default
def levs191e12k5 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x3e20611aa5,0,0xd4126,0x0,0x0,0x0⟩,⟨0x1421011aa5,0,0xd4126,0x0,0x0,0x0⟩,⟨0x3e206102a5,0,0xd402b,0x0,0x0,0x0⟩,⟨0x1421013a35,0,0x126055,0x0,0x0,0x0⟩,⟨0x241a25f815,0,0x35060,0x0,0x0,0x0⟩,⟨0x1a1a24aa85,0,0x60035,0x0,0x0,0x0⟩,⟨0x3e0e615305,0,0x790d1,0x0,0x0,0x0⟩,⟨0x3e0e6152f5,0,0x790d1,0x0,0x0,0x0⟩] else #[⟨0xd0e615055,0,0x1720f9,0x0,0x0,0x0⟩,⟨0xd0e6151b5,0,0x1650f9,0x0,0x0,0x0⟩,⟨0x140f011af5,0,0x9f0dc,0x0,0x0,0x0⟩,⟨0xd0f011b55,0,0x116132,0x0,0x0,0x0⟩,⟨0x140f011b15,0,0x9f0dc,0x0,0x0,0x0⟩,⟨0xd0f011b65,0,0x104132,0x0,0x0,0x0⟩]) : Array Ticket).getD (i % 8) default
def levs191e12k6 (i : Nat) : Ticket := ((if i < 56 then (if i < 24 then (if i < 8 then #[⟨0x93e3440c2e6,0,0x2a045,0x0,0x0,0x0⟩,⟨0x9243440c436,0,0x2a11c,0x0,0x0,0x0⟩,⟨0x93e4840c236,0,0xe810b03b,0x0,0x0,0x2⟩,⟨0x93e3440c2a6,0,0x46,0x0,0x3511b633c420023,0x3609509⟩,⟨0x92434420436,0,0x5015d,0x0,0x0,0x0⟩,⟨0x92428420446,0,0x5003a,0x0,0x0,0x0⟩,⟨0x92428420236,0,0x3f,0x0,0x0,0x51622c481102175050768ab⟩,⟨0x91a284202a6,0,0x137158048,0x0,0x0,0x5⟩] else (if i < 16 then #[⟨0x93e485081f6,0,0x40ca,0x0,0x0,0x0⟩,⟨0x49f24284119f7,0,0x0,0x0,0x0,0xdbd7a29415c9799835d⟩,⟨0x49f2412411a17,0,0x0,0x0,0x0,0x396174bd057393⟩,⟨0x1f1412411aa6,0,0xd4126,0x0,0x0,0x2802⟩,⟨0x93e34508266,0,0xb120,0x0,0x0,0x0⟩,⟨0x49f1a28415267,0,0x0,0x0,0x0,0x1069ae8d54f2d7623a5e⟩,⟨0x48d1412415047,0,0x0,0x0,0x0,0x2e25d033e0d0d5⟩,⟨0x49f1a28407a77,0,0x0,0x0,0x0,0x33⟩] else #[⟨0x49f2428407a07,0,0x0,0x0,0x0,0x30⟩,⟨0x93e3440c276,0,0x9702d,0x0,0x0,0x0⟩,⟨0x93e4840c206,0,0x8602a,0x0,0x0,0x8⟩,⟨0x1f1a1a40c2a6,0,0x9a02d,0x0,0x0,0x8⟩,⟨0x91a28420276,0,0x98055,0x0,0x0,0xb⟩,⟨0x92428420206,0,0x87050,0x0,0x0,0x0⟩,⟨0x12141a420236,0,0x88057,0x0,0x0,0xb⟩,⟨0x1f1412413a36,0,0x1260d4,0x0,0x0,0xb⟩])) else (if i < 40 then (if i < 32 then #[⟨0x48d1412413837,0,0x0,0x0,0x0,0x2e25d070a101c5⟩,⟨0x49f24124101e7,0,0x0,0x0,0x0,0x396324be8c7b93⟩,⟨0x1f14124102a6,0,0xd4126,0x0,0x0,0x8⟩,⟨0x93e48688186,0,0x1b02a,0x0,0x0,0x0⟩,⟨0x92434508406,0,0x21050,0x0,0x0,0x0⟩,⟨0x1f1a1a18c2a6,0,0x9a02d,0x0,0x0,0x0⟩,⟨0x12141a1a0236,0,0x88057,0x0,0x0,0x0⟩,⟨0x49f1a0e40c2a7,0,0x0,0x0,0x0,0x3a89d9ba8cf⟩] else #[⟨0x492140e420237,0,0x0,0x0,0x0,0x4fe7e05d27f⟩,⟨0x12141a1e0a36,0,0x88057,0x0,0x0,0x0⟩,⟨0xd0d0efcc2a6,0,0x9a02d,0x0,0x0,0x0⟩,⟨0x120d1255fa36,0,0x60035,0x0,0x0,0xe⟩,⟨0xd0d1255faa6,0,0x60035,0x0,0x0,0x11⟩,⟨0xd141a243a86,0,0x9a060,0x0,0x0,0x11⟩,⟨0x1f1a1a1ccaa6,0,0x9a02d,0x0,0x0,0x0⟩,⟨0x1f1a1a1cbaa6,0,0x9a02d,0x0,0x0,0x0⟩]) else (if i < 48 then #[⟨0x93e4868c086,0,0x2d022,0x0,0x0,0x0⟩,⟨0x93e341cc2d6,0,0x69121,0x0,0x0,0x0⟩,⟨0x924341cc426,0,0x6b145,0x0,0x0,0x0⟩,⟨0x924341cb436,0,0x2d11a,0x0,0x0,0x0⟩,⟨0x93e341cc2c6,0,0x96121,0x0,0x0,0x0⟩,⟨0x1f1a1a1cc2b6,0,0x910f,0x0,0x0,0x0⟩,⟨0xd0d0e621aa6,0,0x11d02d,0x0,0x0,0x0⟩,⟨0x93e0e610276,0,0x8102d,0x0,0x0,0x0⟩] else #[⟨0x1f0d0e6102a6,0,0x9a02d,0x0,0x0,0x8⟩,⟨0x49f241a1d19d7,0,0x0,0x0,0x0,0x732bdc52b8d⟩,⟨0x93e481cc1c6,0,0x780cd,0x0,0x0,0x0⟩,⟨0x49f240e6119c7,0,0x0,0x0,0x0,0xde17ba9a4d4ccdec360⟩,⟨0x1f0d0e611aa6,0,0x129,0x0,0x0,0x217b787ec008e59cb⟩,⟨0x1f1a0e615256,0,0x9a12c,0x0,0x0,0x14⟩,⟨0x1f1a1a1cc256,0,0x9a02d,0x0,0x0,0x0⟩,⟨0x1f0d0e615376,0,0x9a172,0x0,0x0,0xd017⟩]))) else (if i < 80 then (if i < 64 then #[⟨0xd0d0e615046,0,0x9d09a,0x0,0x0,0x1d⟩,⟨0x93e341cc256,0,0x121,0x0,0x0,0x423816c114c31b8a⟩,⟨0x49f1a0e615257,0,0x0,0x0,0x0,0x3a9075b01d47ecd81fb26a⟩,⟨0x48d0d0e615047,0,0x0,0x0,0x0,0x421cb85eba20e8c6⟩,⟨0x12141a1dea36,0,0x88057,0x0,0x0,0x0⟩,⟨0x924345200e6,0,0x5701c,0x0,0x0,0x0⟩,⟨0x924341e03a6,0,0x660ab,0x0,0x0,0x0⟩,⟨0x924341dcc36,0,0x5715b,0x0,0x0,0x0⟩] else (if i < 72 then #[⟨0x924281e03c6,0,0x680d2,0x0,0x0,0x0⟩,⟨0x9140f010276,0,0x81057,0x0,0x0,0x0⟩,⟨0xa0d0f013a36,0,0x95057,0x0,0x0,0xb⟩,⟨0x120d0f021a36,0,0x15d057,0x0,0x0,0x0⟩,⟨0x120d0e560236,0,0x88057,0x0,0x0,0x0⟩,⟨0x924281e03b6,0,0x850d2,0x0,0x0,0x0⟩,⟨0x12141a1e0386,0,0x50cc,0x0,0x0,0x0⟩,⟨0xa0d0f011b76,0,0x95116,0x0,0x0,0x11820⟩] else #[⟨0x12140f0119c6,0,0x880dc,0x0,0x0,0x26⟩,⟨0x12141a1e01c6,0,0x88057,0x0,0x0,0x0⟩,⟨0x120d0f011a16,0,0xa9088,0x0,0x0,0x29⟩,⟨0x924281e01c6,0,0xd2,0x0,0x0,0x812914e6cfc28adf⟩,⟨0x492140f0119c7,0,0x0,0x0,0x0,0x3f0931802734e6930fc366⟩,⟨0x4920d0f011a17,0,0x0,0x0,0x0,0xde3031cec008bb93⟩,⟨0xa0d0f011aa6,0,0xd7,0x0,0x0,0x181a82498014de1bc⟩,⟨0x48d141a1d5027,0,0x0,0x0,0x0,0x5dcb661191a⟩])) else (if i < 96 then (if i < 88 then #[⟨0x91a281e0256,0,0x9e123,0x0,0x0,0x0⟩,⟨0x48d140f015257,0,0x0,0x0,0x0,0xa09b34504e691a11b66⟩,⟨0x49f090e80f277,0,0x0,0x0,0x0,0x2ee4091e884⟩,⟨0x48a090e813837,0,0x0,0x0,0x0,0x30c211e9102⟩,⟨0x1f241a243816,0,0x88035,0x0,0x0,0xe⟩,⟨0x1f141a1d1b26,0,0xe108,0x0,0x0,0x0⟩,⟨0x1f14121d1af6,0,0xb00da,0x0,0x0,0x20⟩,⟨0x1f0d121d1b56,0,0x116132,0x0,0x0,0x23⟩] else #[⟨0x1f141a1d1b46,0,0xe108,0x0,0x0,0x0⟩,⟨0x1f241a1cfa16,0,0x107027,0x0,0x0,0x0⟩,⟨0x1f14121d1b16,0,0xb00da,0x0,0x0,0x26⟩,⟨0x1f0d121d1b66,0,0x104132,0x0,0x0,0x29⟩,⟨0x49f24281cf9c7,0,0x0,0x0,0x0,0x5eed8dec360⟩,⟨0xf8a0d0e8cfaa7,0,0x0,0x0,0x0,0x5fae65b79bc⟩,⟨0xf86890e8d0aa7,0,0x0,0x0,0x0,0x606bf5ccb96⟩,⟨0xf8a0d0e8d5267,0,0x0,0x0,0x0,0x8410993c9cb⟩]) else (if i < 104 then #[⟨0x506890e8d5047,0,0x0,0x0,0x0,0x85f082132e2⟩,⟨0x1f141a1d5336,0,0x70d0,0x0,0x0,0x0⟩,⟨0xd141a1d3046,0,0x169056,0x0,0x0,0x0⟩,⟨0x1f14121d5306,0,0xae0cf,0x0,0x0,0x14⟩,⟨0x1f141a1d5326,0,0x70d0,0x0,0x0,0x0⟩,⟨0x1f14121d52f6,0,0xae0cf,0x0,0x0,0x17⟩,⟨0xa0d121d5056,0,0x1720f9,0x0,0x0,0x1a⟩,⟨0xa0d121d51b6,0,0x1650f9,0x0,0x0,0x1d⟩] else #[⟨0x49f1a281d3257,0,0x0,0x0,0x0,0x8469b535243⟩])))) : Array Ticket).getD (i % 8) default
def levs191e12k7 (i : Nat) : Ticket := ((if i < 48 then (if i < 24 then (if i < 8 then #[⟨0x49f24345080f7,0,0xb1,0x20101300000e02,0x0,0x21080a004008010020110b31b⟩,⟨0x93e48688186,0,0x0,0x20003600002710000d20000304,0x7b0160280400700a010010014,0x6666666667408066660220256666626666666266222266666666660220666663666666616622228888⟩,⟨0x92434508406,0,0x0,0x20003700002910000c20000304,0xed02e0500880e01401c020014,0x1111172080101111110330361111131133330330333503301111131133333333330330333411110880⟩,⟨0x49f2428248237,0,0x0,0x20003830000730000303,0x33f636858588230400740d01401001c020014,0x2220228900a012122212211710020224202200013b006522222c22⟩,⟨0x49f1a282482a7,0,0x0,0x20003930000302,0x80acfd080db0580a41302302e02c020014,0x800970010040100111a01010011110000003000100012b006500⟩,⟨0x24f921a283480f8,0,0x0,0x30101301,0x0,0x2105820050b21606484017801⟩,⟨0x49f2434348187,0,0x2d,0x20003610000d30000303,0x1d83806a01c020013,0x10a01813⟩,⟨0x4921a28348407,0,0x57,0x20003710000c30000303,0x2204107c01c020013,0x802a80b⟩] else (if i < 16 then #[⟨0x49f1a28248277,0,0x0,0x20003b00703120001330000304,0xcfc2504707c0d41782601401c020014,0x20001190030080300333a03030033331100007000300036500011400⟩,⟨0x49f2428248207,0,0x0,0x20003a00702d20001330000730000305,0x19fa160a0134208380640680680a01201c020014,0x555055b4000c0015155515511a12250559505500018700030655555d55⟩,⟨0xf92141a248237,0,0x88,0x30000301,0x11c220012,0x204000⟩,⟨0xf8d141a2482a7,0,0x9a,0x20001330000302,0xa00ec020012,0x300081⟩,⟨0x49f2434504907,0,0xb1,0x20001330000302,0xac14c020012,0x1e⟩,⟨0x49f2434343187,0,0x2d,0x30000301,0x164298012,0x201⟩,⟨0x4921a28343407,0,0x57,0x30000301,0x1702b0012,0x21⟩,⟨0xf92141a243237,0,0x88,0x30000301,0x2e0011,0x20⟩] else #[⟨0xf8d141a2432a7,0,0x9a,0x20001330000302,0x164020012,0x9⟩,⟨0xf921a28248117,0,0xb1,0x30000301,0x11,0x0⟩,⟨0x24f921a281c80f8,0,0x0,0xe01,0x7c8eb9080012,0x42d5⟩,⟨0x49f24341c8187,0,0x2d,0x20003610002720200f10000d20000305,0x0,0x342f807002011908010141ec0080d⟩,⟨0x4921a281c8407,0,0x57,0x20003710002920200f10000c20000305,0x0,0x12040070020343100d00202876801⟩,⟨0x24f9214121c8238,0,0x0,0x30000730000302,0x0,0x369002eb80206264295458801⟩,⟨0x24f8d14121c82a8,0,0x0,0x30000730000302,0x0,0x158e9d8024080bed5c6d801⟩,⟨0x49f24341c6187,0,0x1b02d,0x0,0x0,0x53⟩])) else (if i < 32 then #[⟨0x4921a281c6407,0,0x21057,0x0,0x0,0x56⟩,⟨0x24f921a283438f8,0,0x0,0x20803d20803c38101f03,0x0,0x200100e8410802a⟩,⟨0x24f8d14121c8278,0,0x0,0x10803130000730000303,0x0,0x563a760083e442001002d5c03801⟩,⟨0x24f9214121c8208,0,0x0,0x10802d30000730000303,0x0,0xda400bae0083a83c00100295403801⟩,⟨0x4921a28343c17,0,0xa305c,0x0,0x0,0x65⟩,⟨0x4921a1a1df987,0,0x2d060,0x0,0x0,0x68⟩,⟨0x4921a1a24abf7,0,0x60035,0x10701e10701d02,0x0,0x21b80206b⟩,⟨0x90a0d121dfa37,0,0x88060,0x0,0x0,0x35865⟩] else (if i < 40 then #[⟨0x68a0d121dfaa7,0,0x9a060,0x0,0x0,0x1b834071⟩,⟨0xf921a283438f7,0,0x0,0x10004020003f20003e03,0x42069cbb92605a01c020013,0x4004024d24904004024928900601a0800125d4000⟩,⟨0x7c90d141a1c98f8,0,0x0,0x32101f01,0x0,0x1⟩,⟨0xf8d141a243a97,0,0xd,0x20101330000302,0x20011,0x2⟩,⟨0xf92141a243a27,0,0x6,0x30000301,0x11,0x0⟩,⟨0x24f921a1a1c9988,0,0x0,0x20002201,0x0,0x69cbb8010024c83d944⟩,⟨0x2490d141a1c9c08,0,0x0,0x20002201,0x0,0x7bcf48010024c876950⟩,⟨0x49f2434343997,0,0x7c034,0x0,0x0,0x74⟩] else #[⟨0xf92141a1c5237,0,0x36088,0x0,0x0,0x65⟩,⟨0xf8d141a1c52a7,0,0x4109a,0x0,0x0,0x74⟩,⟨0x49f2434343977,0,0x2d07c,0x0,0x0,0x77⟩,⟨0x49f24341cc007,0,0x2d022,0x0,0x0,0x7a⟩,⟨0x49f24341cc167,0,0x2d,0x30004120100f30000703,0x418800fa01c020013,0x2015063⟩,⟨0x49f1a1a1cc2e7,0,0x2d096,0x0,0x0,0x22443002⟩,⟨0x4921a1a1cc437,0,0x2d11c,0x0,0x0,0x23002883⟩,⟨0x49f1a1a1cc277,0,0x2d,0x3030000302,0x11e0d4020012,0x432⟩]))) else (if i < 72 then (if i < 56 then #[⟨0x49f241a1cc207,0,0x2d,0x30000301,0x12423c1c0012,0xc09⟩,⟨0x49f241a1cc237,0,0x0,0x20004230000700000530000304,0x19fb212ee4744f89e1362604a80a01001c020014,0x444044801004440440760b4a440c0031042444244202952444d44⟩,⟨0x1f1a1a1cc2a6,0,0x0,0x10003410002602,0x72c550a71482844908c1081dc3a0680b20ec020014,0xd00000010011111119111111111c000000eba00000400777732eeee000008111177177777657111⟩,⟨0x49f1a1a1cc2a7,0,0x0,0x10003430000730000303,0xcfce59a723a300598b015a2784205f01601c020014,0x5900220002602000200222e00000870dc00b000400302200100101a12⟩,⟨0x4921a28343bd7,0,0x570a3,0x0,0x0,0xb6⟩,⟨0x4921a281e00b7,0,0x5701c,0x0,0x0,0xb9⟩,⟨0x4921a281e0397,0,0x57,0x30000f30000302,0xc217e2f0020013,0x4020811a⟩,⟨0x48d141a1e0277,0,0x57,0x30000301,0x1903141f0012,0xe1⟩] else (if i < 64 then #[⟨0x4921a1a1e0437,0,0x5715d,0x0,0x0,0x32c5f80e⟩,⟨0x4921a1a1cac07,0,0x57035,0x0,0x0,0xce⟩,⟨0x492141a1e0447,0,0x57085,0x0,0x0,0x35068811⟩,⟨0x492141a1e0207,0,0x57,0x2c30000302,0x18a104020012,0x4e⟩,⟨0x12141a1e0236,0,0x0,0x10003210002802,0x654810e01ba3686b8ce1963205b0650b8110020014,0x111111111011000000000000080000070000c011111611dd1deba1111dddd32dddd54eeee1111191d11⟩,⟨0x492141a1e0237,0,0x0,0x10003230000730000303,0xcfcf4995222408760e91cc38c4e06202801c020014,0x2022222920220a01102122011115010081002022000760cd0040030b2e2202⟩,⟨0x48d141a1e02a7,0,0x0,0x20004330000300000103,0x40867e7bc888f51e43bc7609c02e01c020014,0x1001211512111211222b1212222412112211111871a1c1131961⟩,⟨0x49f1a28343a67,0,0x122,0x30001301,0x130011,0x1⟩] else #[⟨0x49f14121d0277,0,0x81,0x20001620001330000303,0xd39802ee3ec7c0c511e01c020014,0x207010916058432011⟩,⟨0xf8a0d121d3a37,0,0x95,0x30000301,0x320238012,0x20001⟩,⟨0x2468a0d121d3838,0,0x0,0x30001301,0x0,0x269cd39bc1f6ba20e8840020040084a⟩,⟨0xf920d121caa37,0,0x88035,0x0,0x0,0x338358fe⟩,⟨0xf8d0d121caaa7,0,0x9a035,0x0,0x0,0x3a06e⟩,⟨0x49f24283439f7,0,0xce,0x30001601,0xd0011,0x4⟩,⟨0x24f920d121d01e8,0,0x0,0x30001601,0x0,0x2ee72c009771f0bdc8100100200426b93⟩,⟨0xf8a0d121d02a7,0,0x9a,0x20001330000302,0x124140020012,0x3006⟩])) else (if i < 80 then #[⟨0xf8a0d121d1b77,0,0x95116,0x0,0x0,0x20e4106b901⟩,⟨0xf92141a1d19f7,0,0x7e107,0x0,0x0,0x8690a⟩,⟨0xf9214121d19c7,0,0x880d9,0x0,0x0,0x6d110⟩,⟨0xf92141a2439c7,0,0x88,0x20101f30000302,0x374020012,0x20004⟩,⟨0xf920d121d1a17,0,0x7e088,0x0,0x0,0x38086913⟩,⟨0x24f92141a1d19f8,0,0x0,0x0,0x0,0x6548c9955f4a744a91603a9b59b363⟩,⟨0x49f24282439c7,0,0xcd,0x0,0x0,0x718980a2810ca9954c8bad3233f⟩,⟨0x24f9214121d19c8,0,0x0,0x0,0x0,0x2ee9317ba9a1cc26c8b26a4985ddec360⟩] else (if i < 88 then #[⟨0x24f920d121d1a18,0,0x0,0x501,0x0,0x1bc2380057b8e95f425410393⟩,⟨0xf8a0d121d1aa7,0,0x0,0x30000730000302,0x3f66d2930e59bc24447c8e91c2323b06009e13808c020015,0xb00020000210846808420001c080000018000048000000280e050120001e000800631ad⟩,⟨0xf8d141a1d5267,0,0x8e169,0x0,0x0,0x94125⟩,⟨0xf8d14121d5257,0,0x9a12b,0x0,0x0,0x958a1⟩,⟨0xf8d141a243a57,0,0x9a,0x20101f30000f02,0x290020012,0x204⟩,⟨0xf8a0d121d5377,0,0x9a172,0x0,0x0,0x2684c45392e⟩,⟨0x68a0d121d5047,0,0x8e09a,0x0,0x0,0x4dc55128⟩,⟨0x24f8d141a1d5268,0,0x0,0x0,0x0,0x72e103631de72c8fb6389a9b49d029⟩] else #[⟨0x49f1a28243a57,0,0x121,0x0,0x0,0xe59cb6c114db039c1e42b428a0a⟩,⟨0x24f8d14121d5258,0,0x0,0x0,0x0,0x34f075b01a77ecd81fb26a4863d45813a⟩,⟨0x2468a0d121d5048,0,0x0,0x101,0x0,0x13964897441d1670807782c⟩])))) : Array Ticket).getD (i % 8) default
def levs191e12k8 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x49f2434504907,0,0x0,0x10000e20000d20000c00000b00700a00000830000307,0x260400700d0160280400700a010010014,0x888888888960b04b88880aa0a788888a8888888a88aaaa0aa088888a8888888a88aaaaaaaaaa02288888b88588888b88a0a0abaaa0a0abaa3b0b01b8888888888⟩,⟨0x24f921a28344908,0,0x0,0x30001320801220801120000d20000c00000b00800a10000840000309,0x2100460800e81a03205c0b0140260440800d01401c020015,0x5908b2016422cef10200024a00012e2148421484014a0000ad024a02148421484014a02940021084200842108c00d6b200845100420000280002a00002d6130084⟩,⟨0x24f921a28344868,0,0x0,0x20001820801730001620001520801430001330801010000b40000309,0x1902f0580a41301902c04c0800d01401c020014,0x35535035534d0680007c58555855080006805855585508888100555055335055b505500080008a00330102125155109⟩,⟨0x24f921a28243908,0,0x0,0x20801220801130801030100f10000e20000d20000c10000b10800a1010090000083000030c,0x2204107c0ec1c03504407c0e01902c04c0800d01401c020015,0x24a5496292952a4012739c465996682ca6294a6294c6318c632ccb298a5298a5318c6310c630425394af29ca531cc631cc671c070210d391274808703065214a5294a529400294a5⟩,⟨0x24f921a282438c8,0,0x0,0x20001c20801b20001a20801930001630001330801030100f10000b4000030a,0x4a08e0980e01902c04c0800d01401c020014,0x477470477460590008797779770900059079777977999109447077c707700090009b220313717710a00777077⟩,⟨0x127c90d141a243909,0,0x0,0x20901220901130901030100f10000e20000d20000c10000b10900a1000084000030b,0x0,0x3872c0c8160260040f99502014c0801301a140810840080042680100201c0980101a00405001⟩,⟨0x2490d141a243bf8,0,0x60,0x20801e30801010000b30000310800005,0x3105f0b81642b00d01401c020014,0x94822762252323221⟩,⟨0x7c90d141a243938,0,0x0,0x20002330002220002130102030101f10000e10000b30000308,0x34e5dc3406502c04c0800d01401c020014,0x57555755777a777373575557557777717474555b55665255525572777277660029851555512120035533553⟩] else (if i < 16 then #[⟨0x7c90d141a243918,0,0x0,0x20002520002430102030101f30101330100f10000b1010082010044000032010000b,0x3706b06a07c0e01902c04c0800d01401c020014,0x9a999a991a1117a7112d9a999a991aaaa418a8999199561611391999199111a111a1111651594991411b4179979179970c⟩,⟨0x127c90d141a243939,0,0x0,0x20002330002220002139101040000305,0x0,0x39a7008034bb80a0141d03880109a00400a10⟩,⟨0x24f921a283438a8,0,0x6200f,0x10100801,0x0,0x7d0f41dc00856⟩,⟨0x49f2434343987,0,0x0,0x10002720002600000930000710000610000510700430000308,0x26c4c09512423c4608910c210418800ee1c42c8470760a40b0140260400680a00e014020015,0x739ce739ce739f473e4e739c032009839ce7390e739ce7390e700c802109720c83018c739ce739ce739ec73812e01ce739da739ce7381320316a408032002139ce73d4e739ce73d0e719083014809c5259160f⟩,⟨0x4921a28343c07,0,0x0,0x10002920002800000930000310000210000110700007,0x810bc1722d8598b015a2a8538a41422783a0560940f8160170260400680a01001c020015,0x110822c048210002088243188631af60884111842218c4318d5318c6218c4318d4218c43182210446108c631886310c6318c6318d3218c4318d2214a1108228884420890790ed20442090f922d4940c87c91cc⟩,⟨0x24f8d141a243a78,0,0x0,0x10803110003020002f20802e30001310000840000310000110800009,0x19f9a723a320628c217e29c4e08f0a00a80d01902c04c0800d01401c020015,0x8211022208e401e42114c2108b11184211842818c6a88a6108c2108c6319a63084210424208421384211842119821108312842211e2450429884258849⟩,⟨0x24f921a1a243958,0,0x35,0x20801d30801010000b30000710800405,0x670cb15a1dc2e00d01401c020014,0x490872262323225221⟩,⟨0x24f92141a243a08,0,0x0,0x10802d10002c20002b20802a3000163000131000084000071000051080044000030b,0x67e5dc8e8d71a8344610b31382482982a03e0740e01902c04c0800d01401c020015,0xa8415002a1053d000301200a40618103421034200318c6f98c004210042220114a8021104010800003700052900c000c090176022a8401a00290845d08⟩] else #[⟨0xf92141a243a37,0,0x0,0x10003320003210000630000304,0xca9771cc38c700dd1b432c628b60f417c1782001401c020015,0x84210842108221084210822100210042108421085410842f088421084210922145cd1084210c42408421086210401004600080300c0338c6c108421184210842046202921084042108421084212c42⟩,⟨0x24f92141a243a38,0,0x0,0x20003240000710000518100440000305,0x33f32a5dc8e8f51e43bc760e91a22e44f89c12a1040680b01401c020015,0xa5294a0294a52c0020804301465294652806318d0f1800529405281cd000a029545014a000067000000240c5827201625280c0010a52d0a5⟩,⟨0xf8d141a243aa7,0,0x0,0x10003520003430000310000204,0xe59a72084047f0fb1f035c670980fa1881902301401c020015,0x3c00000001000110822109421084210842109c00000010002108411082210842109221084210000000116b000000031044110c421044110c424042008c2308ce31ac000000600031884a484210⟩,⟨0x24f8d141a243aa8,0,0x0,0x20003440000310000118100004,0x67e72cd391d220434851071ea3005f8bc13826c2200e01401c020015,0x221042103c4218c4210d62188421884318e6218c421884218c6338c621084273442108424084218842198421084a13122944428084228844⟩])) : Array Ticket).getD (i % 8) default
def levs191e12k9 (i : Nat) : Ticket := (#[⟨0x24f921a28344878,0,0x0,0x10000b10800a1000091000082000062000052080044000032000022000012080000b,0xec1c0350640bc1602904c08c1001f03a0700d01902e0580a0130220400700d0160280400700a010010015,0x4420804200442089e0108007442108ca619886219c46c442088c210442088c210ca6198c6698a628ca61988620442088c210442088c2114a528ca6198c6298a6319934202210442088411304219ce1108224084b888411204228cc3320c628cc3320c658c63420e740d0342a6a4cd193e42210446908221046a2cc939461⟩] : Array Ticket).getD (i % 8) default
def trees191e12 : Book :=
  ⟨true,inputSet 191 [12],goalAt 191,9,68,readRule factss191e12 recss191e12,hintss191e12,11,unpackState wiress191e12 7,(fun k => match k with | 5 => 14 | 6 => 105 | 7 => 91 | 8 => 20 | 9 => 1 | _ => 0),fun k => match k with
    | 5 => levs191e12k5
    | 6 => levs191e12k6
    | 7 => levs191e12k7
    | 8 => levs191e12k8
    | 9 => levs191e12k9
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless191e12 : ∀ i, i < 68 → Valid true (goalAt 191) ((trees191e12).rule i) := by
  exact validateRules factss191e12 recss191e12 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k5i0 : bookRange trees191e12 5 0 14 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e12k5 : allGood trees191e12 5 :=
  book_level trees191e12 5 ruless191e12 (book_empty trees191e12 4 rfl) passs191e12k5i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k6i0 : bookRange trees191e12 6 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k6i16 : bookRange trees191e12 6 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k6i32 : bookRange trees191e12 6 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k6i48 : bookRange trees191e12 6 48 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k6i64 : bookRange trees191e12 6 64 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k6i80 : bookRange trees191e12 6 80 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k6i96 : bookRange trees191e12 6 96 9 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e12k6 : allGood trees191e12 6 :=
  book_level trees191e12 6 ruless191e12 goods191e12k5 (@book_split trees191e12 6 0 48 57 (@book_split trees191e12 6 0 16 32 passs191e12k6i0 (@book_split trees191e12 6 16 16 16 passs191e12k6i16 passs191e12k6i32)) (@book_split trees191e12 6 48 32 25 (@book_split trees191e12 6 48 16 16 passs191e12k6i48 passs191e12k6i64) (@book_split trees191e12 6 80 16 9 passs191e12k6i80 passs191e12k6i96)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k7i0 : bookRange trees191e12 7 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k7i16 : bookRange trees191e12 7 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k7i32 : bookRange trees191e12 7 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k7i48 : bookRange trees191e12 7 48 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k7i64 : bookRange trees191e12 7 64 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k7i80 : bookRange trees191e12 7 80 11 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e12k7 : allGood trees191e12 7 :=
  book_level trees191e12 7 ruless191e12 goods191e12k6 (@book_split trees191e12 7 0 48 43 (@book_split trees191e12 7 0 16 32 passs191e12k7i0 (@book_split trees191e12 7 16 16 16 passs191e12k7i16 passs191e12k7i32)) (@book_split trees191e12 7 48 16 27 passs191e12k7i48 (@book_split trees191e12 7 64 16 11 passs191e12k7i64 passs191e12k7i80)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k8i0 : bookRange trees191e12 8 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k8i16 : bookRange trees191e12 8 16 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e12k8 : allGood trees191e12 8 :=
  book_level trees191e12 8 ruless191e12 goods191e12k7 (@book_split trees191e12 8 0 16 4 passs191e12k8i0 passs191e12k8i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs191e12k9i0 : bookRange trees191e12 9 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods191e12k9 : allGood trees191e12 9 :=
  book_level trees191e12 9 ruless191e12 goods191e12k8 passs191e12k9i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims191e12 : Claim true 191 [12] 10 := by
  apply low_search (s:=true) (T:=goalAt 191) (raw:=rawSet 191) (es:=extraSet 191 [12])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 191 12] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 191 [12]) (extraWord 191 12) = inputSet 191 [] := by decide +kernel
      change Low true (remove (inputSet 191 [12]) (extraWord 191 12)) (goalAt 191) 10
      rw [eq]
      exact claims191
  · exact book_end trees191e12 goods191e12k9 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims445e38 : Claim true 445 [38] 10 :=
  rename_rows claims191e12 [0,16,45,53,7,20,50,11,22,51,15,1,17,46,8,12,34,41,55,38,40,0,35,0,0,0,0,0,0,0,0,0,0,0,4,19,48,10,14,0,5,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims486 : Claim true 486 [] 8 :=
  rename_rows claims189 [0,2,0,0,16,18,0,34,36,0,41,4,6,0,19,37,24,26,0,31,42,0,27,0,0,0,0,0,0,0,0,0,0,0,45,47,0,53,55,0,48,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims494 : Claim true 494 [] 10 :=
  rename_rows claims191 [0,45,7,50,4,48,10,2,47,9,6,24,54,29,27,26,16,53,20,19,18,0,31,0,0,0,0,0,0,0,0,0,0,0,34,55,38,37,36,0,42,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims494e38 : Claim true 494 [38] 10 :=
  rename_rows claims191e12 [0,4,7,10,45,48,50,24,27,29,54,2,6,9,47,26,34,37,38,55,42,0,36,0,0,0,0,0,0,0,0,0,0,0,16,19,20,53,31,0,18,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims243 : Claim true 243 [] 7 :=
  rename_rows claims187 [0,1,11,12,0,0,0,24,25,30,0,2,3,13,0,26,16,17,22,0,31,0,18,0,0,0,0,0,0,0,0,0,0,0,34,35,40,0,42,0,36,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims215 : Claim true 215 [] 7 :=
  rename_rows claims187 [0,2,24,26,0,0,0,11,13,30,0,1,3,25,0,12,4,6,27,0,14,0,5,0,0,0,0,0,0,0,0,0,0,0,34,36,42,0,40,0,35,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims222 : Claim true 222 [] 7 :=
  rename_rows claims187 [0,4,34,37,0,0,0,11,14,40,0,7,10,38,0,15,2,6,36,0,13,0,9,0,0,0,0,0,0,0,0,0,0,0,24,27,42,0,30,0,29,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims437 : Claim true 437 [] 7 :=
  rename_rows claims187 [0,16,45,53,0,0,0,4,19,48,0,34,41,55,0,37,1,17,46,0,5,0,35,0,0,0,0,0,0,0,0,0,0,0,11,22,51,0,14,0,40,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims497 : Claim true 497 [] 7 :=
  rename_rows claims187 [0,16,34,41,0,0,0,11,22,40,0,1,17,35,0,12,45,53,55,0,51,0,46,0,0,0,0,0,0,0,0,0,0,0,24,31,42,0,30,0,25,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims99 : Claim true 99 [] 4 :=
  rename_rows claims15 [0,16,1,17,2,18,3,24,31,25,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims135 : Claim true 135 [] 4 :=
  rename_rows claims15 [0,1,2,3,4,5,6,34,35,36,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims198 : Claim true 198 [] 4 :=
  rename_rows claims15 [0,24,2,26,4,27,6,34,42,36,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims378 : Claim true 378 [] 7 :=
  rename_rows claims187 [0,45,16,53,0,0,0,2,47,18,0,24,54,31,0,26,7,50,20,0,9,0,29,0,0,0,0,0,0,0,0,0,0,0,11,51,22,0,13,0,30,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims504 : Claim true 504 [] 7 :=
  rename_rows claims187 [0,45,24,54,0,0,0,11,51,30,0,7,50,29,0,15,16,53,31,0,22,0,20,0,0,0,0,0,0,0,0,0,0,0,34,55,42,0,40,0,38,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims347 : Claim true 347 [] 8 :=
  rename_rows claims189 [0,1,0,0,45,46,0,24,25,0,54,2,3,0,47,26,11,12,0,51,30,0,13,0,0,0,0,0,0,0,0,0,0,0,7,8,0,50,29,0,9,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims349 : Claim true 349 [] 7 :=
  rename_rows claims187 [0,7,4,10,0,0,0,1,8,5,0,11,15,14,0,12,45,50,48,0,46,0,51,0,0,0,0,0,0,0,0,0,0,0,24,29,27,0,25,0,30,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims476 : Claim true 476 [] 7 :=
  rename_rows claims187 [0,7,11,15,0,0,0,24,29,30,0,45,50,51,0,54,4,10,14,0,27,0,48,0,0,0,0,0,0,0,0,0,0,0,34,38,40,0,42,0,55,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims351 : Claim true 351 [] 10 :=
  rename_rows claims191 [0,7,4,10,2,9,6,1,8,5,3,11,15,14,13,12,45,50,48,47,46,0,51,0,0,0,0,0,0,0,0,0,0,0,24,29,27,26,25,0,30,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims367 : Claim true 367 [] 10 :=
  rename_rows claims191 [0,45,24,54,2,47,26,1,46,25,3,16,53,31,18,17,7,50,29,9,8,0,20,0,0,0,0,0,0,0,0,0,0,0,4,48,27,6,5,0,19,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims379 : Claim true 379 [] 10 :=
  rename_rows claims191 [0,45,16,53,1,46,17,2,47,18,3,24,54,31,25,26,7,50,20,8,9,0,29,0,0,0,0,0,0,0,0,0,0,0,11,51,22,12,13,0,30,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims428 : Claim true 428 [] 7 :=
  rename_rows claims31 [0,4,7,10,45,48,50,16,19,20,53,34,37,38,55,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims487 : Claim true 487 [] 10 :=
  rename_rows claims191 [0,16,1,17,2,18,3,4,19,5,6,34,41,35,36,37,45,53,46,47,48,0,55,0,0,0,0,0,0,0,0,0,0,0,24,31,25,26,27,0,42,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
def hintss511 (_ : Nat) : Nat := 0
def wiress511 (i : Nat) : W := bandWord (((if i < 8 then 0x8c07801ffc0000000080c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe00000000000) >>> (72*(i % 8))) % 4722366482869645213696)
def factss511 (i : Nat) : {f : Fact // Sound true f} := (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then ⟨item 31 [] 7,claims31⟩ else ⟨item 167 [] 7,claims167⟩) else (if i < 3 then ⟨item 189 [] 8,claims189⟩ else ⟨item 191 [] 10,claims191⟩)) else (if i < 6 then (if i < 5 then ⟨item 313 [] 7,claims313⟩ else ⟨item 319 [] 10,claims319⟩) else (if i < 7 then ⟨item 334 [] 7,claims334⟩ else ⟨item 347 [] 8,claims347⟩))) else (if i < 12 then (if i < 10 then (if i < 9 then ⟨item 351 [] 10,claims351⟩ else ⟨item 355 [] 7,claims355⟩) else (if i < 11 then ⟨item 367 [] 10,claims367⟩ else ⟨item 379 [] 10,claims379⟩)) else (if i < 14 then (if i < 13 then ⟨item 428 [] 7,claims428⟩ else ⟨item 445 [] 10,claims445⟩) else (if i < 15 then ⟨item 486 [] 8,claims486⟩ else (if i < 16 then ⟨item 487 [] 10,claims487⟩ else ⟨item 494 [] 10,claims494⟩)))))
def recss511 (i : Nat) : Recipe := ((if i < 8 then #[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[])] else (if i < 16 then #[(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[])] else #[(16,[])])) : Array Recipe).getD (i % 8) default
def levs511k12 (i : Nat) : Ticket := (#[⟨0x8732601549,0,0x0,0x20001020000f30000e20000d40000c20000b20000a40000920000830000740000620000540000420000330000240000140000011,0x31baba2589f71959340d2871015,0x19463000001946300000080a0294af0000000000000001a063004201a863004a02a8a5004201a863004c04290808421205215294b105415294d304c100420004201bc630050043d0800c601ac630108000c601ac63010e042d0809121008401b463008802b4a5008400090043508089a16b5af2088200c601c063014a02c0a500c601c063018c0099c17c1ef219645c16b11982⟩] : Array Ticket).getD (i % 8) default
def trees511 : Book :=
  ⟨true,inputSet 511 [],goalAt 511,12,17,readRule factss511 recss511,hintss511,6,unpackState wiress511 4,(fun k => match k with | 12 => 1 | _ => 0),fun k => match k with
    | 12 => levs511k12
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless511 : ∀ i, i < 17 → Valid true (goalAt 511) ((trees511).rule i) := by
  exact validateRules factss511 recss511 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511k12i0 : bookRange trees511 12 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511k12 : allGood trees511 12 :=
  book_level trees511 12 ruless511 (book_empty trees511 11 rfl) passs511k12i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511 : Claim true 511 [] 13 := by
  apply low_search (s:=true) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [] at hw
    contradiction
  · exact book_end trees511 goods511k12 (by decide) (by decide +kernel)
def hintss511e38 (i : Nat) : Nat := ((if i < 192 then (if i < 96 then (if i < 48 then (if i < 16 then 0x8004d9041c002a6820e00161e107000a0f083800625041c002ad810e001ce4087000df2043800579021c0027c810e000ae4087000b0f043800507821c00173c10e0014180870004ca043 else (if i < 32 then 0x8005d9121c001c2890e000294487000e722038006f9101c00173c80e00069e4070009f21438005078a1c00021850e00156c10700073608380027a841c0038c820e0015e41070009f2083 else 0x80048d461c000d3230e0013e4c8700009a643800587b21c00283d90e000294a870009b2483800028a41c00283d20e00166c6870009f23438004d91a1c00283cd0e000098687000c72243)) else (if i < 64 then 0x8003854e1c00052a70e000ced2070004b5903800579481c001c9640e0002cb20700065a9038001a7c81c00263240e00119920700014a903800739461c0017a630e000953187000dda8c3 else (if i < 80 then 0x800139621c0019daf0e0015e57870009f2bc38004d95e1c0008caf0e00096b7070009f2b838003b95c1c0015cae0e0004e5707000e72ac380048d561c000d3eb0e001c653870008d19c3 else 0x80055b08340039c841a0013e420d000572106800587883400283c41a00099420d000af2e438004d9721c00233390e00096bc07000af2e038004f9701c0009cb80e001535c07000906e03))) else (if i < 144 then (if i < 112 then 0x800507b63400054571a000298b8d000d0a5c6800494a634002f2931a000e2290d000151486800687a434002c3ce1a00141e70d0009cf3868002a79c34001c30d1a00029868d000d0a346 else (if i < 128 then 0x800263085400240c42a0011862150004b5dc68004f960340009cb01a0009eb78d00084abc68003655e3400162af1a00099578d00012590680036d48340027c9b1a000134d8d000b0f6c6 else 0x8004d4a65400084532a001718995000a0c4ca8005e3265400240d32a000098715000bc62ca8002689054000e3082a00071839500055114a8002888a5400270c52a00120629500024314a)) else (if i < 160 then 0x8001c64c540030da02a000e23015000df674a80069b3a540031d9d2a00186ce95000bc670a8004e1b854002469b2a00178cd950009036ca800461b6529940c142a0002a2a15000d0f50a else (if i < 176 then 0x4b480a685400171b42a00098da14969014c4a80026362540020db0292d2041814969015c0a4b4c4a60525a405302a00090d815000846bca8002635e540031dab2a00186d59500038c9ca else 0x8001051c64002cd8b320009ea599000af22cc8004f916640026c8b32000a525990001652cc8005079664003128b320019e441900034614c800685026400131b9292d204db950005c6dca)))) else (if i < 288 then (if i < 240 then (if i < 208 then 0x8000b2d0640033ca632000dcb1990003a58cc80071b3c640031d9e3200166cf19000ab678c8005793c64002469c320006b4e1900091a64c8001ad32640026c96320000a2b19000a0f58c else (if i < 224 then 0x800514a87c002b68d3e000eb469f000ac334f8004819a7c00080cd3e000a5259f000de52cf8005e3167c00240cb3e001a1439f000676e0c6b4a14706400246b83200136599900091accc else 0x800243687c001f6af3e00098d79f000829b0f8002b4d87c0020a683e000ad341f000529a0f8001c3507c000969e3e00180cb9f0009035cf800101ae7c00084563e001206b1f00038654f)) else (if i < 256 then 0x800419328c001769946000934ca30009b2591800507ac8c000131646000294a2300020a4d180027aa08c002bc90460013e48230009b2411800587a08c00283d0460018948230004ca211 else (if i < 272 then 0x8002b930d40012a586a00184ac35000b0f61a800507b0d400233176a000c98bb500065149a8004661ad4001930d6a00106413500014a991800092c68c002ad9f46000934e2300080a711 else 0x8003b95ed40012a6a6854a2553b500034f9da8004664ed4001b9646a00161ef35000a0f79a8001a7bad4002331d6a0013e4db5000a0f6da80004336d4002ad986a001ce4c350009f261a))) else (if i < 336 then (if i < 304 then 0x800466372c002345396000a1e9cb00098c4e5800466272c0037293960002949cb00098f3a58004879d2c002630e9600119874b000a0c1658004818b2c00262849600029424b000772dda else (if i < 320 then 0x8004f9692c0026cb4960015e58cb0009f2c658004d9632c002adb0960013e584b00014ca25800685512c000e323960011990cb0009037258006fb372c003769b96001234dcb00098c6e5 else 0x800461af4c00263d6a600101eb5300054f5a9800287ad4c0023316a6000a18b53000e72569800587ab4c00283d5a600161ea53000a0f529800483274c002a692a60011869530004b5429)) else (if i < 352 then 0x8006ed3b94002f69dca0017064e5000bc3232800612819400126aaa600131f45300080fa298002a7d14c00143e8a6000fb52530004c6929800587c14c00283e0a60011ecfd300091a7e9 else (if i < 368 then 0x8004e1f1940026333ca0004199e50004c6bf28004e1df9400080efca000487765000c65af28005e1d7940034967ca0018cb3e5000c259f2800701cf940031966ca001c87365000bc39b2 else 0x8003c663b4001d2b0da0010656ed000c25ab68003c655b4002e31eda000a22e6d0009037368005e337b4002f0d9da001206ced000c256368004662dac002f193d600170696b0009034b5))))) >>> (37*(i % 16))) % 137438953472
def wiress511e38 (i : Nat) : W := bandWord (((if i < 32 then (if i < 16 then (if i < 8 then 0xd28000efd323207aa0bb8000ad3a4ffa7cc09a0000ac3a0ff878002b80008d124b4a7cc0cb80003fc00b4a7cc0b1800021284cf204c00b80000d000b4a7cc055800002a1a0a507a else 0x5429c7ecfc320007aa71b07fe003b8ffc7f04f28400efdbf3207aa0de8001ffd323297aa0eb8001ffd24b4a7cc0cb8001ffc00b4a7cc0a88001fdd24b4a38c0ba0001ec3ffff8780) else (if i < 24 then 0x2cdbbbe33c00c4f84c2c1bbbe33c0084204c388bacffdc00b4a38c388bace3dc00b4a38c7d29e7eefd323207aa7129e7e8c9323207aa6d09e3e63c1202002a6109e3e0081202002a else 0x614bfbe0081202102a7a8becffdd24b4a38c6d0be3f73c1202002a54ebdffdfc320097aa444bdbf53c1200102a542bc7fdfc320007aa3cbbbfe3fc00b4a7cc30bbbfe0d000b4a7cc)) else (if i < 48 then (if i < 40 then 0xa90420020380ff000084341300221808447090a40408c1203087806d4bfbf73c1202102a6e1bfbf73c0484204c6453fbf12258c87870655bfbe02a1a0a507a6413fbe02218084070 else 0x814d0248081202112afba4641ec3ffff8780d2a4441cc3ff308780cfec401fffff3297aacf2c401effff3207aacba4401ec3ffff8780c204401c03ff000000b9a4240ac3a0ff8780) else (if i < 56 then 0xfd2fe7fffd323207aabcbfbffffc00b4a7ccacdfbbf33e40c4f84c8c07801ffc00000000bbbe248ad3a4ffa7cc80c618110240c0f8008bbe008ad3a4ffa7cc821e00809004a4224c else (if i < 64 then 0xf1efffe8c9323297aaf0a7ffe8c120308780f57fffe82a1a0a557af437ffe02218084470f007ffe00000000000eedffbf73e44c4f84ce4d7fbf12258c8f870e55ffbe82a1a0a517a else 0xfdeffffffd323297aafebffffffd24b4a7ccfca7fffffd20308780f4f7fff12258c8fc70f0c7fff10240c0f800fdb7ffeae3b8ffc7f0f2bfffe8d124b4a7cc)))) >>> (72*(i % 8))) % 4722366482869645213696)
def factss511e38 (i : Nat) : {f : Fact // Sound true f} := (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then ⟨item 31 [] 7,claims31⟩ else ⟨item 167 [] 7,claims167⟩) else (if i < 3 then ⟨item 189 [] 8,claims189⟩ else (if i < 4 then ⟨item 313 [] 7,claims313⟩ else ⟨item 313 [38] 7,claims313e38⟩))) else (if i < 7 then (if i < 6 then ⟨item 319 [] 10,claims319⟩ else ⟨item 334 [] 7,claims334⟩) else (if i < 8 then ⟨item 334 [38] 7,claims334e38⟩ else (if i < 9 then ⟨item 347 [38] 8,claims347e38⟩ else ⟨item 351 [38] 10,claims351e38⟩)))) else (if i < 15 then (if i < 12 then (if i < 11 then ⟨item 355 [] 7,claims355⟩ else ⟨item 379 [38] 10,claims379e38⟩) else (if i < 13 then ⟨item 428 [38] 7,claims428e38⟩ else (if i < 14 then ⟨item 445 [] 10,claims445⟩ else ⟨item 445 [38] 10,claims445e38⟩))) else (if i < 17 then (if i < 16 then ⟨item 486 [] 8,claims486⟩ else ⟨item 494 [] 10,claims494⟩) else (if i < 18 then ⟨item 494 [38] 10,claims494e38⟩ else (if i < 19 then ⟨item 243 [] 7,claims243⟩ else ⟨item 215 [] 7,claims215⟩))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then ⟨item 30 [] 4,claims30⟩ else ⟨item 190 [] 7,claims190⟩) else (if i < 23 then ⟨item 222 [] 7,claims222⟩ else (if i < 24 then ⟨item 166 [] 4,claims166⟩ else ⟨item 165 [] 4,claims165⟩))) else (if i < 27 then (if i < 26 then ⟨item 437 [] 7,claims437⟩ else ⟨item 497 [] 7,claims497⟩) else (if i < 28 then ⟨item 99 [] 4,claims99⟩ else (if i < 29 then ⟨item 187 [] 7,claims187⟩ else ⟨item 27 [] 4,claims27⟩)))) else (if i < 35 then (if i < 32 then (if i < 31 then ⟨item 163 [] 4,claims163⟩ else ⟨item 177 [] 4,claims177⟩) else (if i < 33 then ⟨item 23 [] 4,claims23⟩ else (if i < 34 then ⟨item 135 [] 4,claims135⟩ else ⟨item 198 [] 4,claims198⟩))) else (if i < 37 then (if i < 36 then ⟨item 378 [] 7,claims378⟩ else ⟨item 504 [] 7,claims504⟩) else (if i < 38 then ⟨item 347 [] 8,claims347⟩ else (if i < 39 then ⟨item 349 [] 7,claims349⟩ else ⟨item 476 [] 7,claims476⟩))))))
def recss511e38 (i : Nat) : Recipe := ((if i < 104 then (if i < 48 then (if i < 24 then (if i < 8 then #[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[])] else (if i < 16 then #[(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[])] else #[(16,[]),(17,[]),(0,[193]),(2,[129]),(4,[321]),(8,[385]),(9,[449]),(10,[257])])) else (if i < 32 then #[(11,[449]),(14,[449]),(0,[197]),(7,[321]),(8,[389]),(9,[453]),(10,[261]),(11,[453])] else (if i < 40 then #[(15,[321]),(17,[449]),(18,[]),(7,[261]),(9,[393]),(12,[257]),(14,[389]),(15,[325])] else #[(17,[389]),(2,[265]),(19,[]),(4,[197]),(11,[265]),(12,[133]),(14,[265]),(17,[201])]))) else (if i < 72 then (if i < 56 then #[(7,[201]),(8,[265]),(9,[333]),(11,[329]),(17,[265]),(4,[265]),(8,[333]),(9,[401])] else (if i < 64 then #[(11,[397]),(14,[397]),(2,[149]),(12,[333]),(14,[469]),(15,[337]),(17,[469]),(20,[])] else #[(21,[]),(22,[]),(9,[449,226]),(11,[449,162]),(14,[449,162]),(23,[]),(9,[449,290]),(11,[449,226])])) else (if i < 88 then (if i < 80 then #[(14,[449,226]),(1,[257]),(14,[449,353]),(15,[277]),(24,[]),(9,[453,354]),(11,[453,354]),(17,[449,290])] else #[(1,[261]),(2,[329]),(17,[449,353]),(9,[453,418]),(25,[]),(17,[449,418]),(26,[]),(0,[9])]) else (if i < 96 then #[(27,[]),(1,[9]),(28,[]),(3,[17]),(9,[393,33]),(14,[389,33]),(29,[]),(30,[])] else #[(31,[]),(9,[393,226]),(14,[389,162]),(17,[389,162]),(0,[265]),(3,[145]),(9,[393,289]),(14,[389,225])])))) else (if i < 152 then (if i < 128 then (if i < 112 then #[(12,[257,133]),(14,[389,265]),(17,[389,201]),(7,[261,201]),(9,[393,333]),(17,[389,265]),(32,[]),(0,[77])] else (if i < 120 then #[(1,[77]),(9,[77]),(11,[265,97]),(17,[201,33]),(11,[265,353]),(17,[201,289]),(33,[]),(34,[])] else #[(9,[398]),(11,[265,418]),(14,[265,418]),(17,[201,418]),(4,[197,265]),(11,[265,397]),(14,[265,397]),(8,[265,333])])) else (if i < 136 then #[(9,[333,401]),(11,[329,397]),(0,[13]),(1,[17]),(9,[29]),(10,[17]),(11,[29]),(14,[469,33])] else (if i < 144 then #[(1,[81]),(9,[93]),(10,[81]),(11,[93]),(17,[469,33]),(14,[449,226,357]),(14,[449,353,166]),(14,[449,353,230])] else #[(9,[449,418]),(11,[449,418]),(14,[449,353,422]),(17,[449,290,357]),(9,[453,226]),(11,[453,162]),(17,[449,353,166]),(17,[449,353,294])]))) else (if i < 176 then (if i < 160 then #[(11,[453,418]),(17,[449,353,422]),(9,[393,33,230]),(14,[389,33,166]),(9,[393,33,486]),(35,[]),(36,[]),(14,[389,33,265])] else (if i < 168 then #[(9,[393,33,333]),(9,[393,226,37]),(14,[389,162,37]),(9,[393,226,293]),(14,[389,162,229]),(9,[393,226,289]),(14,[389,162,225]),(14,[389,225,265])] else #[(9,[393,289,333]),(1,[141]),(37,[]),(9,[393,77]),(17,[389,201,37]),(17,[389,201,293]),(9,[77,418]),(11,[265,97,422])])) else (if i < 192 then (if i < 184 then #[(17,[201,33,422]),(38,[]),(11,[265,97,486]),(39,[]),(9,[77,401]),(11,[265,97,397]),(9,[333,398]),(11,[265,353,418])] else #[(17,[201,289,418]),(11,[265,353,397]),(9,[398,97]),(11,[265,418,101]),(17,[201,418,37]),(9,[398,353]),(11,[265,418,357]),(17,[201,418,293])]) else (if i < 200 then #[(9,[29,226]),(11,[29,162]),(14,[469,33,166]),(9,[29,418]),(11,[29,418]),(14,[469,33,422]),(9,[93,226]),(11,[93,162])] else #[(17,[469,33,166]),(9,[93,418]),(11,[93,418]),(17,[469,33,422])]))))) : Array Recipe).getD (i % 8) default
def levs511e38k7 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x9d2a660fc62b7,0,0xd3108,0x0,0x0,0x0⟩,⟨0x9d2a660fc3ac7,0,0x3b130,0x0,0x0,0x0⟩,⟨0x9d2a660fc60d7,0,0xd3108,0x0,0x0,0x0⟩,⟨0xed3a65f01d167,0,0x33126,0x0,0x0,0x0⟩,⟨0xed3a65f011977,0,0x11c0c5,0x0,0x0,0x0⟩,⟨0xed3a65f011b57,0,0x11c0c5,0x0,0x0,0x0⟩,⟨0xf9a305f0e0ae7,0,0x620af,0x0,0x0,0x0⟩,⟨0xa53b24d106237,0,0x11004,0x0,0x0,0x0⟩] else #[⟨0xa53b24d1120b7,0,0xd007,0x0,0x0,0x0⟩,⟨0x9d2a6611062b7,0,0xbf107,0x0,0x0,0x0⟩,⟨0x9d2a6611060d7,0,0xc9107,0x0,0x0,0x0⟩,⟨0xed3a65f111977,0,0x660c4,0x0,0x0,0x0⟩,⟨0xed3a65f111b57,0,0x670c4,0x0,0x0,0x0⟩]) : Array Ticket).getD (i % 8) default
def levs511e38k8 (i : Nat) : Ticket := ((if i < 32 then (if i < 16 then (if i < 8 then #[⟨0x76a53a660fcfb78,0,0x3f126,0x0,0x0,0x0⟩,⟨0x76a53a660fcf938,0,0x3f126,0x0,0x0,0x0⟩,⟨0x529d92660fcf8c8,0,0x3f04c,0x0,0x0,0x0⟩,⟨0x76a53a660fc8378,0,0x3f127,0x0,0x0,0x0⟩,⟨0x76a53a660fdb9d8,0,0x16f03f,0x0,0x0,0x0⟩,⟨0x76a52a660fdb9a8,0,0x3a14c,0x0,0x0,0x0⟩,⟨0x76a53a660fc91d8,0,0x16f03f,0x4b01,0x0,0x1⟩,⟨0x76a53a660fc9248,0,0x16103f,0x0,0x0,0x0⟩] else #[⟨0x529d2a660fc90c8,0,0x8304c,0x0,0x0,0x0⟩,⟨0x76a592660fd21b8,0,0x16103a,0x0,0x0,0x0⟩,⟨0x76a53a660fd2138,0,0x3a03f,0x0,0x0,0x0⟩,⟨0x76a592660fd21c8,0,0x3a03f,0x0,0x0,0x0⟩,⟨0x529d92660fd20c8,0,0x3f04c,0x0,0x0,0x0⟩,⟨0x76a53a660fc9918,0,0x16f03f,0x0,0x0,0x0⟩,⟨0x76a52a660fc98f8,0,0x3a157,0x0,0x0,0x0⟩,⟨0x76a52a660fc99c8,0,0x3a14b,0x0,0x0,0x0⟩]) else (if i < 24 then #[⟨0x529d2a660fc98c8,0,0x3a04c,0x0,0x0,0x0⟩,⟨0x52c92a660fce0c8,0,0x3a04c,0x0,0x0,0x0⟩,⟨0x529d2a660fc6078,0,0x8303a,0x0,0x0,0x2802⟩,⟨0x4ec92a660fc62c8,0,0x3b132,0x0,0x0,0x4005⟩,⟨0x4ec92a65f01b0a8,0,0x160054,0x0,0x0,0x0⟩,⟨0x769d9255f01b158,0,0x3209a,0x0,0x0,0x0⟩,⟨0x4ec92a65f01b048,0,0x132054,0x0,0x0,0x0⟩,⟨0x4ec92a65f00c0a8,0,0x160054,0x5101,0x0,0x1⟩] else #[⟨0x4ec92a65f01b018,0,0x133054,0x0,0x0,0x0⟩,⟨0x769d9265f00c238,0,0x16401a,0x0,0x0,0x0⟩,⟨0x4ec92a65f00c0b8,0,0xdb054,0x0,0x0,0x0⟩,⟨0x76a53b25f00f238,0,0x3201a,0x0,0x0,0x0⟩,⟨0x769d9255f00f198,0,0x32132,0x0,0x0,0x0⟩,⟨0x529d9255f00f0b8,0,0x32054,0x0,0x0,0x0⟩,⟨0x76a53a65f011ba8,0,0x33126,0x0,0x0,0x700b⟩,⟨0x769d9265f011968,0,0x164032,0x0,0x0,0x5811⟩])) else (if i < 48 then (if i < 40 then #[⟨0x529d9265f011848,0,0x1a054,0x0,0x0,0x0⟩,⟨0x769d9265f011998,0,0x3201a,0x0,0x0,0x0⟩,⟨0x529d9265f0118b8,0,0x1a054,0x0,0x0,0x0⟩,⟨0x769d9255f00c948,0,0x3209a,0x0,0x0,0x0⟩,⟨0x4ec92a65f00c838,0,0x160054,0x0,0x0,0x0⟩,⟨0x4ec92a65f00c848,0,0x132054,0x0,0x0,0x0⟩,⟨0x4ec92a65f00c8b8,0,0x32054,0x0,0x0,0x0⟩,⟨0x529d9255f005898,0,0xdb032,0x0,0x0,0x0⟩] else #[⟨0x7cd193078f542e8,0,0x870fe,0x0,0x0,0x0⟩,⟨0x7cd14b278f54338,0,0x870a4,0x0,0x0,0x0⟩,⟨0x7cd19305ef20ae8,0,0x9e0fe,0x0,0x0,0x14⟩,⟨0x7cd14b05f0d4418,0,0xaf062,0x0,0x0,0x14⟩,⟨0x7ca59305ef140e8,0,0xa708c,0x0,0x0,0x0⟩,⟨0x7cd182f790d42e8,0,0x620fe,0x0,0x0,0x14⟩,⟨0x7cd14af790d4338,0,0x620a4,0x0,0x0,0x0⟩,⟨0x76a53b24d123238,0,0x82004,0x0,0x0,0x17⟩]) else (if i < 56 then #[⟨0x76a53b24d112458,0,0xdc00d,0x0,0x0,0x1a⟩,⟨0x529d9254d1230b8,0,0x176007,0x0,0x0,0x1a⟩,⟨0x529d9254d106458,0,0x171011,0x0,0x0,0x17⟩,⟨0x76a5926611121b8,0,0x16308b,0x0,0x0,0x0⟩,⟨0x76a53a661112138,0,0xd70b8,0x0,0x0,0x0⟩,⟨0x76a5926611121c8,0,0x1240f3,0x0,0x0,0x0⟩,⟨0x529d926611120c8,0,0x14513c,0x0,0x0,0x0⟩,⟨0x76a52a6611099c8,0,0xfb0c2,0x0,0x0,0x0⟩] else (if i < 64 then #[⟨0x529d2a6611098c8,0,0x1240bb,0x0,0x0,0x0⟩,⟨0x52c92a66110e0c8,0,0x1240f5,0x0,0x0,0x0⟩,⟨0x529d2a661106078,0,0x1240bf,0x0,0x0,0x1d⟩,⟨0x4ec92a6611062c8,0,0x1350c9,0x0,0x0,0x20⟩,⟨0x76a53b25f10f238,0,0x7e05b,0x0,0x0,0x0⟩,⟨0x769d9255f10f198,0,0x114072,0x0,0x0,0x0⟩,⟨0x529d9255f10f0b8,0,0x14205e,0x0,0x0,0x0⟩,⟨0x76a53a65f111ba8,0,0x7e066,0x0,0x0,0x23⟩] else #[⟨0x769d9265f111968,0,0x9410d,0x0,0x0,0x26⟩,⟨0x769d9265f111998,0,0x14210c,0x0,0x0,0x0⟩,⟨0x529d9265f1118b8,0,0x14713a,0x0,0x0,0x0⟩,⟨0x4ec92a65f10c8b8,0,0x142111,0x0,0x0,0x0⟩,⟨0x529d9255f105898,0,0xea142,0x0,0x0,0x0⟩])))) : Array Ticket).getD (i % 8) default
def levs511e38k9 (i : Nat) : Ticket := ((if i < 32 then (if i < 16 then (if i < 8 then #[⟨0x3b68a53a660fcf929,0,0x15d01e,0xf01,0x0,0x802⟩,⟨0x3b529d92660fcfc69,0,0xe903f,0x30201201,0x0,0x2002801⟩,⟨0x3b68a53a660fc9109,0,0x16e01e,0xf20000102,0x0,0x1005801⟩,⟨0x76a53a54cc1fb78,0,0x0,0x20008d10004b30004910004710004605,0x220380680a00e010010013,0x6e36db6db6db6db6db6db6c36db0d80000001c36db6db6db6db6d96dbcdb6da6db6da6c000201b6d249249b6db6db0001406db6d24adb6db6d0db⟩,⟨0x3b529d2a660fc9379,0,0x161083,0x10004b30004902,0x0,0x805005801⟩,⟨0x3b529d2a660fc9469,0,0x161083,0x20001701,0x0,0x680b801⟩,⟨0x76a53b24cc1fa48,0,0x0,0x20008e10004b30004910004310004205,0x740b80d01401c020013,0x24d24924924924124904800004924924924924924124924524925124aa492452492452000040249492492480004009264912492492000c12492249924412⟩,⟨0x3b529d92660fe3249,0,0x3a03f,0x30004910004202,0x0,0x2604600410004⟩] else #[⟨0x76a53a54cc1f938,0,0x0,0x20008f10004b30004910004710004605,0x580a40680a00e014020013,0x6e36db6db6db6c36db0d80000db6db6db6db6db69b6d96db6d96c000101b6c925b6db6db0001406db6c926db5b6db6db6c00386dbcc926db6d61b⟩,⟨0x3b529d2a660fe3139,0,0x8303a,0x10004601,0x0,0x640bc00820⟩,⟨0x3b52c92a660fe31c9,0,0x8303a,0x0,0x0,0xd417823⟩,⟨0x529d9254cc1f8c8,0,0x0,0x20009210009110009030004904,0x760e00d00a01001c020013,0x80492000000000002000000000100000200050000000000000c000200924a24001248000924c2400004929240001c9240030000492924040⟩,⟨0x294ec92a660fe30c9,0,0x3a04c,0x10009030004902,0x0,0x350080c800826⟩,⟨0x769d9254cbe0368,0,0x0,0x20009310005130005010004e10004d05,0x881041f00d01401c020013,0x4ba49000000249249249248249249248a4924924924924924924824d24924924800010124912492492714924800124922493099249249124aa412⟩,⟨0x3b4ec92a65f00c369,0,0x1640db,0x10005130005002,0x0,0x812800847⟩,⟨0x344ec92a65f00c019,0,0x15f046,0x20001a00000202,0x0,0x425004⟩]) else (if i < 24 then #[⟨0x3b4ec92a65f00c459,0,0x1640db,0x20001a01,0x0,0x14026801⟩,⟨0x344ec92a65f00c049,0,0xdb046,0x201,0x0,0x844⟩,⟨0x3b529d9255f0229e9,0,0xdb032,0x0,0x0,0x1642b053⟩,⟨0x76a53b24cbe0238,0,0x0,0x20009610009510009430005004,0xc417c2e04d01401c020013,0x700000002000000004024900000000000000000100000200000000000000200924a2524800000000c02494924d26db000000c092400054926db040⟩,⟨0x3b529d9265f022a39,0,0x3201a,0x10009530005002,0x0,0x680ca00429804⟩,⟨0x769d9254cbe0198,0,0x0,0x20009710005130005010004e10004d05,0xe21b83580d01401c020013,0x4ba49000249249249248249249248a49249249249249209349248000101249124925249200049248924c2649124b2000492492492249a64924412⟩,⟨0x3b4ec92a65f022999,0,0xdb032,0x10004e01,0x0,0xe81942b001⟩,⟨0x529d9254cbe00b8,0,0x0,0x20009910009810005310005130005005,0x1dc2800d01401c020013,0x50000100924000000000004000000006000000000000000004010000c04924d20000db6db00010049200001b6dc6e490000049200000001b6f3924080⟩] else #[⟨0x294ec92a65f0228b9,0,0x32054,0x10009830005002,0x0,0x740021a02c804⟩,⟨0x294ec92a65f022849,0,0x17d054,0x20001a01,0x0,0x1c431001⟩,⟨0x7cd14a764c1e218,0,0x0,0x20009b20009a30005920002204,0x1401c020012,0x555555565aa005555555556500555556555555565557554555aaba55aaba00355aaa555aa55ff45⟩,⟨0x3e68a53b260f1ea19,0,0xd8087,0x0,0x0,0x0⟩,⟨0x7cd14b260f1ea88,0,0x0,0x20009f10005c30005910002720002205,0x3241f43d00d01401c020013,0x24924924924924926900036db6db6924924924924924924926924924924928924824924924924936db8da490000924924924c01492492552000fff⟩,⟨0x7cd13b260f1ead8,0,0x0,0x2000a010005d30005910002720002205,0xd01401c020013,0x924924924925248001249224928924900049224928924924924a24924a249249a49209249249249252491c92491c80001b6da490052492492492⟩,⟨0x68a53b24ac1e008,0,0x0,0x20009e20009d20009c30005940005820002206,0x800d01401c020013,0x228a6932c924a69124948a49269100924a49a28a49228a49924a28a4a924a08a29248a29264925b2eb6924db6eb6522aa4402296ca4928db6522a2924211⟩,⟨0x34529d92560f1e809,0,0x8707a,0x0,0x0,0x0⟩])) else (if i < 48 then (if i < 40 then #[⟨0x7cd14a764c1e388,0,0x0,0x2000a22000a120005a30005904,0x1401c020012,0x20aa55aaa0000000000002055aa00000200000002000300100000aaba00aaba557ff0010⟩,⟨0x7cd14a760bde398,0,0x0,0x2000a42000a310006320005a10000a20000106,0x800d01401c020013,0x40249124a49240000000000000000001004925249240000249259000249259124adb6d0000c09248e40000c0924b6d49249b6c0008000⟩,⟨0x7cd14a760bd0438,0,0x0,0x2000a62000a510006340005e20005a10000a20000107,0x4c0800d01401c020013,0x406180db6280db75d7686186180186db62815d7680000ed775ac06ed775bb6db0000803b5d96b018803b5edb492061b6db6d80db6aa69a69a400⟩,⟨0x3e68a59305ef14419,0,0x8c,0x1910aa3000a920100003,0x4308310001c020013,0x24a26884924b⟩,⟨0x7cd19305ef142e8,0,0x0,0x2000ad10006c10006920002a20000110000006,0xd08891001e80800d01401c020014,0x11110011101011404020204040441111011011141111111311111111111811111111111111111104404344333322222233331111110440454433335555555622225555559999001101222227000⟩,⟨0x7cd14b25ef14338,0,0x0,0x2000ac1000ab30007020002a10002905,0x3422303e80d01401c020013,0x249249249249a4db6492db6da492492492492492692492492492492c924924924924936db8da492894924929249924892492489248012492492fff⟩,⟨0x7cd14b05ef21a88,0,0x0,0x2000a710006a10006620002220000105,0x1231182244180d01401c020014,0x20011112222222222000000000000000000000022222422000011114444444444444700000022222322000003004444111111333333330000000000006001111158888⟩,⟨0x7cd13b05ef21ad8,0,0x0,0x2000a810006d10006720002220000105,0xd01401c020013,0x492124c92480002000004926492480002000000492452492452124a49240000001812491c92489244924b6d8000600000000000000⟩] else #[⟨0x3e68a53b05ef21a29,0,0x173062,0x20000101,0x0,0x801⟩,⟨0x7cd192660bd7058,0,0x0,0x2000b82000b71000b610007a40006e20002a20000110000008,0x2c04c0800d01401c020013,0xdb60b6d92db76b25b25926924927124926124b2592c96ed6f67b325984bb5d96edb391b2592ed77dbb6dbed248ff7fb6db6d965929a6b269a49a6c0⟩,⟨0x7cd13305ea17428,0,0x0,0x2000b910008010007e10007520002a20000110000007,0x4c0800d01401c020013,0x49249041282145169041a49248b42492db6db1249c49249848b4596edb2492524849261249248b4576edb67b49224936db649201208009249249⟩,⟨0x3e68c93305ea17089,0,0x8f0fe,0x20000101,0x0,0x801⟩,⟨0x7cd14b24cbd4318,0,0x0,0x2000bc2000bb1000ba30007020002a05,0xd01401c020013,0x924924928900024924924924a24924924924b2492492492492494922492c90006db24925249448924c25b6dc6c0004924249249209252492249209⟩,⟨0x7cd192660bd42a8,0,0x0,0x2000bf2000be1000bd10007a20002a20000110000007,0x4c0800d01401c020013,0x20825042082424904824c24924d24924b24924924924924912049256db6d2492c91208e4b6d49249b6c92491209a4b6dbad6db492db6d80240240241⟩,⟨0x7cd14b24cbd4068,0,0x0,0x2000b02000af1000ae30007020002a05,0xd01401c020013,0x924924928900024924924924a24924924924b24924924925248924b2400092494925122493096db71b0001092492482494924892492496db924209⟩,⟨0x3e68a59265ea19869,0,0x8f155,0x0,0x0,0x0⟩]) else (if i < 56 then #[⟨0x76d14b24cbd4028,0,0x0,0x2000b32000b22000b130007040006e20002a06,0x800d01401c020013,0x124a69124a69124924948a49148a49948a4924924a249148948a8916c948a89100948aa916cbad948aa94924b21008a4924928268b64a4524936db6db211⟩,⟨0x3b68a59265ea19829,0,0x1550f1,0x0,0x0,0x0⟩,⟨0x7cd14a65ea19c28,0,0x0,0x2000b51000b410007330007020002a10002906,0x800d01401c020013,0x9249249249289124c9248924a2492492492494922492a9124db6a492a9249252491c89249a56db5da4925b6da492492492200492492492492492⟩,⟨0x3b529d9254d123459,0,0x1660ea,0x0,0x0,0x1302544908f⟩,⟨0x76a53b24cc22248,0,0x0,0x2000c21000c11000c020008530008305,0x79826c4900d01401c020013,0x10000000000020000804924800000000000000000800000c00001000000000000c04924d26590001000004925122d9924940000000492c8000b65b9241c0⟩,⟨0x3b529d92661123249,0,0x124145,0x1000c030008302,0x0,0xa41420104f001⟩,⟨0x3b529d2a661123139,0,0xe9124,0x10003d01,0x0,0x15429c4f001⟩,⟨0x3b52c92a6611231c9,0,0xe9124,0x0,0x0,0x2b4538a1⟩] else #[⟨0x529d9254cc220c8,0,0x0,0x2000c51000c41000c330008320008205,0x2b81662c04c00d01401c020014,0x10100000121120200110111101101112111111111113111111141111011011110110110000110131102202322111113333301100220242211111411333344444501101702201111610111333344440811⟩,⟨0x294ec92a6611230c9,0,0x12413c,0x1000c330008302,0x0,0xad0082a8008a4⟩,⟨0x3b529d9255f1229e9,0,0xea142,0x0,0x0,0x2f05c8b6⟩,⟨0x76a53b24cbe2238,0,0x0,0x2000c81000c71000c620008a30008805,0x3d21842fc4780d01401c020014,0x100000000000002000002002222000000000000000000000002000000030000000000000000000300222223223131000004000000040022221331343344444500000000702222000006133144440800⟩,⟨0x3b529d9265f122a39,0,0x142147,0x1000c730008802,0x0,0xc818a0045b004⟩,⟨0x3b4ec92a65f122999,0,0xea142,0x10003a01,0x0,0x1963145c801⟩,⟨0x529d9254cbe20b8,0,0x0,0x2000cb1000ca1000c930008820006f05,0x5763384a80d01401c020013,0x410000512820090492090494492492496492492482412482412000482c90904d22492db6db0483090902493096db71b92494120241224924125b6f39241c9⟩,⟨0x294ec92a65f1228b9,0,0x14213a,0x1000ca30008802,0x0,0xcb0023205e004⟩]))) : Array Ticket).getD (i % 8) default
def levs511e38k10 (i : Nat) : Ticket := ((if i < 8 then #[⟨0x3b68a53b24cc1f9f9,0,0x0,0x20004420004320004230004130004050003f40101210000f30000109,0x640b0130200340500700a010010014,0x25555080055550800555585858883555505050055550755550700757577500500500500085005000050050007000000090000000a0000105005090058855005090057757977999950050058858a88500557757a779999aaaaaa55555555666855550055550505006565666565004⟩,⟨0x3b68a53a54cc1f929,0,0x0,0x20004820004720004650004510000f30000106,0x440800e01a02c0500800e010010014,0x302230030500300305005555300305003553555a33333333003003053003050035535533333333000003030030130030700555530030700555557553003377377300300555559553003555559553003007777399399333300535358556333300535355333340737377939399300⟩,⟨0x3b529d9254cc1fc69,0,0x0,0x20004b20004a40004910001810001630001206,0x981182003a0680b8140220400680a00e014020014,0x44644ed0000404044404044000041000041441010111010c104404404404444044044414444444444444344444445444474444444b4a044004404444044044442449804404344044043440110131144443333333304404404400110151144444433335555555555000⟩,⟨0x3b689d9254cbe0189,0,0x0,0x20004f20004e20004d50004c30001a10000230000107,0x6a0c81782c05204c0800d01401c020014,0x30b222204002222320204003242444a22223242442332000023020004230200043333030300050303333300233223020004301120020024422442454430030535535520020024424644244230030055555655366366233290234248447234244333300233300535355636366222⟩,⟨0x3b529d9254cbe0459,0,0x0,0x20005220005140005010001f10001d30001a06,0x134250470881041f03b0700c80800d01401c020014,0x33e33dc000033303063303033b3a00000000313310101010033033330330333303303331333333333332333333333333333303300330330330333133433980330330330323301101211333332222222222272033033033035330110333333222225225555555555000⟩,⟨0x34529d9254cbe0049,0,0x0,0x30005620005530005420005350004c30001a10000230000108,0x2683502c04c0800d01401c020014,0x222204002222320204003242444932328022220400324223020004233200002302000433330303000703033333002332002302000430124422002070024424744300307377377244246442002060024423003006666666736636623424544233200234245333300233353535353222⟩,⟨0x3e68a53b24ac1e3d9,0,0x0,0x20005d20005c20005a40005950005830005720002730002208,0x2f85c0b21582985002c04c0800d01401c020014,0x333354434344d4c32324422224644222232324644323262626632423242444242443242222246443202626233334423324446234244442342444633334443434447333340434322223424444b23424446a33335443434494834434426626766244226626766344347443003077777001⟩,⟨0x3e68a53b260bde209,0,0x0,0x20006320006220006150006050005f50005e30005a5000583000013010000a,0x680ca1880e01902c04c0800d01401c020014,0x4224112424114444171144444444372454444411241444441711444437222242241117425411114214111712121118121242241113c21121146747877411446747877466438211219114774797741141911477468864334393324240044443744441144443724241311b64643834343339a411⟩] else (if i < 16 then #[⟨0x7cd14b260bde288,0,0x0,0x20006a20006940006830002b20002a2000291000243000232000223000012000000b,0xe81c43706b0ac07c0e01902c04c0800d01401c020014,0x111110101100001411204060401010101011111101101114011011111111111911111111111f11111111111105704944011025956595999e11111103304a4401101a11538523a2aaab63a6001101101d1126c6⟩,⟨0x7cd13b260bde2d8,0,0x0,0x20006d20006c40006b1000263000252000222000041000023000012000000a,0xee1640e01902c04c0800d01401c020014,0x11111010110000408010101811101040808810101811111101101118011011181111111611111111111b1111111111110230868802808688426211111111191107708988077027524794999a1111191100111111⟩,⟨0x3e68a53a560bde439,0,0x0,0x20006720006630006420005a50005810002830002220000a30000109,0x7a0ee1d03401902c04c0800d01401c020014,0x44440050444410464600666607006666464607004646464677460646060046060046066666070046262746767766664060000b64060007a4444005094444c04004006776787760066776787740040800422448848840040300677673776006030067764004030088884224224334400⟩,⟨0x3e76d192660bd42e9,0,0x0,0x20007520007450006e10003210002e30002a30000120000008,0x1062003e86e02c04c0800d01401c020014,0x5555015115555b1555511555514115555555544511551151111a511511141111111611111113111151151151151151155115161185445522526566566511513115115131154454344666652252253355115115115171154454744666667663333522557757755550101555521119500⟩,⟨0x3e68a592660bd4059,0,0x0,0x20007b20007a20007910007850007750007650006e30002a3000012000000a,0x8910c1f40e01902c04c0800d01401c020014,0x3333113333161133332633333443341311163443111114141117141411181414344311311336633113171132232731131811366368663113777732232822311311356369663113191175757977858535532933330133331211a33330133332633331211c43431123232723232228b535329300⟩,⟨0x3e76d14b24cbd4339,0,0x0,0x20007320007210007140007030006f50006e30002a20002908,0x4c09512423c4607102c04c0800d01401c020014,0x24422224422224544222245442222525255222244222244244224424444d24424445244244444444444644442442444444442442244246448255224424644211266662442442442474425525755244247446666676621121777772222342222142222410002442c444b2442a44492442⟩,⟨0x7cd14a660bd4428,0,0x0,0x20007e20007d40007c10003710002f30002d20002a2000292000073000012000000b,0x9810007c0e01902c04c0800d01401c020014,0x111110101100001711407010101711101010101111110880011019114894991111191111111a1103807a770110838343a3aaac11111a11111111022076770110161182989699325342641111001101101b111111⟩,⟨0x7cd13a660bd6c28,0,0x0,0x20008120008030007f10003930003510003430003020000c1000023000012000000b,0x7c0e01902c04c0800d01401c020014,0x111110101911000010101911101019111010101019111010191111066006809a9911111a11111a111111110260979902909799626211111111171111111104409599044064a6a5aa243211111511111100111111⟩] else #[⟨0x3b529d9254cc22469,0,0x0,0x20008710008630008510008440008330008220003d07,0x568aa14e2905089e13604c0800d01401c020014,0x22422dc1111212122212122111123111123223131333131b31221222212212222122122232222222222252222222622222222a2122112212222122122111229812212212212522133135332222255454545455122126221221133136332222262245546666676666000⟩,⟨0x3b529d9254cbe2459,0,0x0,0x20008c10008b30008a10008940008830006f20003a07,0x5f8bc1722d8598b013604c0800d01401c020014,0x22422dc111121212121b2111123111123223131313133122122221221222212212223222222222225222222222222222212211221222212212211122a912212212212522133135332222255454555454851221262212212622133122222622455456556666676666000⟩])) : Array Ticket).getD (i % 8) default
def levs511e38k11 (i : Nat) : Ticket := (#[⟨0x3b68a53b24a9983f9,0,0x0,0x20001920001820001630001540001430001340001220000f40000109,0x320580981001a0280400700a010010014,0x244440900444409004444040409009494999544440404004444094444090094944004004004000940040000400400090000000000000a0000000b00003040044004000040040000140040a00477440040a0047849a990000a7a7aa40040046749b99400446949b990000007676b6b6⟩,⟨0x3b68a53b24a997c09,0,0x0,0x20002120001f20001d30001c40001b40001a20000240000108,0x58098110200380680b01401c020014,0x822220700222207002222020207007272777622220002024022222222070072727720020000200200072002000020020007000000000009000000000020022002002002000700120020025522002090025527977000009959520020023327a7720020a00233200000053939a99a3a3⟩,⟨0x3e68a53b24ac17bc9,0,0x0,0x2000282000264000252000244000233000223000043090032000024000013000000b,0x4007c0e81c0340640b81602804c0800d01401c020014,0x11113110101100001811000010101811508010101010111010000018115080881111110110111801101111011011181111111111111c11111111111f00001101111d01101118b11119111111102408c88011002808c8811111c1152c211111e1106608e8801101e11066011111e1126a256e5eee7⟩,⟨0x3e76d14b24cc17a89,0,0x0,0x20002f20002e40002d20002c40002b30002a3000291000093000074000013000000b,0x580a41302303e0700d01902c04c0800d01401c020014,0x11110101100001311000013115030101011000011111101101111f0110111301101111111111171111111a1111111111111101101711906600110171156757711111a1101101a1104603a330110646454a4aaae11111101101b1102203b3301101b1162767b77428452b50011010110d101101c11⟩,⟨0x3e76d13b24cc17ad9,0,0x0,0x20003420003320003230003140003010000e30000c3000042000024000013000000b,0x2f03e0740e01902c04c0800d01401c020014,0x111101018110000181100001010181110101800001810101811111101101111c011011180110111811111119111111151111111111111101101911a0330037089881111191111110110151102308588028085883232111111111b1101101b1106608b88066036939b99264211111b11001101011011⟩,⟨0x3e68a53a54cc17c29,0,0x0,0x20003920003820003730003640003510001130000c3000072000024000013000000b,0x2f05807c0e01902c04c0800d01401c020014,0x111111101018110000181100001010181110101811101010101110100000181110101800001101111c01101118b111111111119066001101911067089881111191111191111111a1102608a88011002808a8811111a11626211111a1111111103308588011015110330111115116396959923421111⟩,⟨0x3b529d9254cc17c49,0,0x0,0x20003e20003c40003b30003a10000b30000a1000092000083000073000044000013000000c,0x1a83204407c0e01902c04c0800d01401c020014,0x11600001010110000150000151150500110111101101111011011151111111111171111111a11111111110110011011110110110000110110110171102405755111117727201101a11011008505a5511111a112828a8a8aaad01101b1101101b11033011111b1123727b778398b3b3bbbc⟩] : Array Ticket).getD (i % 8) default
def levs511e38k12 (i : Nat) : Ticket := (#[⟨0x1f3b68a53b24a9982fa,0,0x0,0x20001120a01020000e20a00d40000c20000b20000930000840000740a00620a00540000440a00330000250000140000010,0xb81582804a0880f81c0320580a0130220400700d0160280400700a010010015,0x21084010040800425340000050108000005010800000401005010840100401000000042100401020000000140000005010842108421080210042109601080210a0010802108401080210a021084210842108428884210842a08421000000802100001080210849008401085038842108d11004200a2211408400021005110808782118404210851108421128210a630084015042011008521000840012008521010842150424110410842132c210aa10084015842039c085a100084015842039c0108421584243a288da3123a44⟩] : Array Ticket).getD (i % 8) default
def trees511e38 : Book :=
  ⟨true,inputSet 511 [38],goalAt 511,12,204,readRule factss511e38 recss511e38,hintss511e38,11,unpackState wiress511e38 7,(fun k => match k with | 7 => 13 | 8 => 69 | 9 => 64 | 10 => 18 | 11 => 7 | 12 => 1 | _ => 0),fun k => match k with
    | 7 => levs511e38k7
    | 8 => levs511e38k8
    | 9 => levs511e38k9
    | 10 => levs511e38k10
    | 11 => levs511e38k11
    | 12 => levs511e38k12
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless511e38 : ∀ i, i < 204 → Valid true (goalAt 511) ((trees511e38).rule i) := by
  exact validateRules factss511e38 recss511e38 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k7i0 : bookRange trees511e38 7 0 13 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e38k7 : allGood trees511e38 7 :=
  book_level trees511e38 7 ruless511e38 (book_empty trees511e38 6 rfl) passs511e38k7i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k8i0 : bookRange trees511e38 8 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k8i16 : bookRange trees511e38 8 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k8i32 : bookRange trees511e38 8 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k8i48 : bookRange trees511e38 8 48 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k8i64 : bookRange trees511e38 8 64 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e38k8 : allGood trees511e38 8 :=
  book_level trees511e38 8 ruless511e38 goods511e38k7 (@book_split trees511e38 8 0 32 37 (@book_split trees511e38 8 0 16 16 passs511e38k8i0 passs511e38k8i16) (@book_split trees511e38 8 32 16 21 passs511e38k8i32 (@book_split trees511e38 8 48 16 5 passs511e38k8i48 passs511e38k8i64)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k9i0 : bookRange trees511e38 9 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k9i16 : bookRange trees511e38 9 16 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k9i32 : bookRange trees511e38 9 32 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k9i48 : bookRange trees511e38 9 48 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e38k9 : allGood trees511e38 9 :=
  book_level trees511e38 9 ruless511e38 goods511e38k8 (@book_split trees511e38 9 0 32 32 (@book_split trees511e38 9 0 16 16 passs511e38k9i0 passs511e38k9i16) (@book_split trees511e38 9 32 16 16 passs511e38k9i32 passs511e38k9i48))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k10i0 : bookRange trees511e38 10 0 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k10i16 : bookRange trees511e38 10 16 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e38k10 : allGood trees511e38 10 :=
  book_level trees511e38 10 ruless511e38 goods511e38k9 (@book_split trees511e38 10 0 16 2 passs511e38k10i0 passs511e38k10i16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k11i0 : bookRange trees511e38 11 0 7 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e38k11 : allGood trees511e38 11 :=
  book_level trees511e38 11 ruless511e38 goods511e38k10 passs511e38k11i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e38k12i0 : bookRange trees511e38 12 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e38k12 : allGood trees511e38 12 :=
  book_level trees511e38 12 ruless511e38 goods511e38k11 passs511e38k12i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e38 : Claim true 511 [38] 13 := by
  apply low_search (s:=true) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [38])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 38] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 511 [38]) (extraWord 511 38) = inputSet 511 [] := by decide +kernel
      change Low true (remove (inputSet 511 [38]) (extraWord 511 38)) (goalAt 511) 13
      rw [eq]
      exact claims511
  · exact book_end trees511e38 goods511e38k12 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e12 : Claim true 511 [12] 13 :=
  rename_rows claims511e38 [0,45,16,53,1,46,17,2,47,18,3,24,54,31,25,26,7,50,20,8,9,21,29,32,34,55,41,35,56,36,42,38,39,43,11,51,22,12,13,23,30,15,40,57,44,4,48,19,5,49,6,27,28,10,37,14,52,33,58] (by decide +kernel)
def hintss511e4 (_ : Nat) : Nat := 0
def wiress511e4 (i : Nat) : W := bandWord (((if i < 8 then 0x81cf1a590a52c2f92a80c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc00000000) >>> (72*(i % 8))) % 4722366482869645213696)
def factss511e4 (i : Nat) : {f : Fact // Sound true f} := ⟨item 494 [] 10,claims494⟩
def recss511e4 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levs511e4k12 (i : Nat) : Ticket := (#[⟨0x7983260154a,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def trees511e4 : Book :=
  ⟨true,inputSet 511 [4],goalAt 511,12,1,readRule factss511e4 recss511e4,hintss511e4,3,unpackState wiress511e4 4,(fun k => match k with | 12 => 1 | _ => 0),fun k => match k with
    | 12 => levs511e4k12
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless511e4 : ∀ i, i < 1 → Valid true (goalAt 511) ((trees511e4).rule i) := by
  exact validateRules factss511e4 recss511e4 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e4k12i0 : bookRange trees511e4 12 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e4k12 : allGood trees511e4 12 :=
  book_level trees511e4 12 ruless511e4 (book_empty trees511e4 11 rfl) passs511e4k12i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4 : Claim true 511 [4] 13 := by
  apply low_search (s:=true) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl
    · have eq : remove (inputSet 511 [4]) (extraWord 511 4) = inputSet 511 [] := by decide +kernel
      change Low true (remove (inputSet 511 [4]) (extraWord 511 4)) (goalAt 511) 13
      rw [eq]
      exact claims511
  · exact book_end trees511e4 goods511e4k12 (by decide) (by decide +kernel)
def hintss511e4e12 (_ : Nat) : Nat := 0
def wiress511e4e12 (i : Nat) : W := bandWord (((if i < 8 then 0x80c618110240c0f800863e1380b21cac667c821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc0000000081cf1a590a52c2f92a) >>> (72*(i % 8))) % 4722366482869645213696)
def factss511e4e12 (i : Nat) : {f : Fact // Sound true f} := ⟨item 494 [12] 10,claims494e12⟩
def recss511e4e12 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levs511e4e12k12 (i : Nat) : Ticket := (#[⟨0x68a93270154b,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def trees511e4e12 : Book :=
  ⟨true,inputSet 511 [4,12],goalAt 511,12,1,readRule factss511e4e12 recss511e4e12,hintss511e4e12,3,unpackState wiress511e4e12 4,(fun k => match k with | 12 => 1 | _ => 0),fun k => match k with
    | 12 => levs511e4e12k12
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless511e4e12 : ∀ i, i < 1 → Valid true (goalAt 511) ((trees511e4e12).rule i) := by
  exact validateRules factss511e4e12 recss511e4e12 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e4e12k12i0 : bookRange trees511e4e12 12 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e4e12k12 : allGood trees511e4e12 12 :=
  book_level trees511e4e12 12 ruless511e4e12 (book_empty trees511e4e12 11 rfl) passs511e4e12k12i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4e12 : Claim true 511 [4,12] 13 := by
  apply low_search (s:=true) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4,12])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4,extraWord 511 12] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · have eq : remove (inputSet 511 [4,12]) (extraWord 511 4) = inputSet 511 [12] := by decide +kernel
      change Low true (remove (inputSet 511 [4,12]) (extraWord 511 4)) (goalAt 511) 13
      rw [eq]
      exact claims511e12
    · have eq : remove (inputSet 511 [4,12]) (extraWord 511 12) = inputSet 511 [4] := by decide +kernel
      change Low true (remove (inputSet 511 [4,12]) (extraWord 511 12)) (goalAt 511) 13
      rw [eq]
      exact claims511e4
  · exact book_end trees511e4e12 goods511e4e12k12 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e16 : Claim true 511 [16] 13 :=
  rename_rows claims511e4 [0,2,1,3,16,18,17,45,47,46,53,24,26,25,31,54,4,6,5,19,48,49,27,28,11,13,12,22,23,51,30,14,52,33,34,36,35,41,55,56,42,37,40,57,44,7,9,8,20,21,50,29,32,10,15,38,39,43,58] (by decide +kernel)
def hintss511e4e16 (_ : Nat) : Nat := 0
def wiress511e4e16 (i : Nat) : W := bandWord (((if i < 8 then 0xc21e409c93ffa4224c80c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc0000000081cf1a590a52c2f92a) >>> (72*(i % 8))) % 4722366482869645213696)
def factss511e4e16 (i : Nat) : {f : Fact // Sound true f} := ⟨item 428 [] 7,claims428⟩
def recss511e4e16 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levs511e4e16k12 (i : Nat) : Ticket := (#[⟨0x78a93260154b,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def trees511e4e16 : Book :=
  ⟨true,inputSet 511 [4,16],goalAt 511,12,1,readRule factss511e4e16 recss511e4e16,hintss511e4e16,3,unpackState wiress511e4e16 4,(fun k => match k with | 12 => 1 | _ => 0),fun k => match k with
    | 12 => levs511e4e16k12
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless511e4e16 : ∀ i, i < 1 → Valid true (goalAt 511) ((trees511e4e16).rule i) := by
  exact validateRules factss511e4e16 recss511e4e16 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e4e16k12i0 : bookRange trees511e4e16 12 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e4e16k12 : allGood trees511e4e16 12 :=
  book_level trees511e4e16 12 ruless511e4e16 (book_empty trees511e4e16 11 rfl) passs511e4e16k12i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4e16 : Claim true 511 [4,16] 13 := by
  apply low_search (s:=true) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4,16])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4,extraWord 511 16] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · have eq : remove (inputSet 511 [4,16]) (extraWord 511 4) = inputSet 511 [16] := by decide +kernel
      change Low true (remove (inputSet 511 [4,16]) (extraWord 511 4)) (goalAt 511) 13
      rw [eq]
      exact claims511e16
    · have eq : remove (inputSet 511 [4,16]) (extraWord 511 16) = inputSet 511 [4] := by decide +kernel
      change Low true (remove (inputSet 511 [4,16]) (extraWord 511 16)) (goalAt 511) 13
      rw [eq]
      exact claims511e4
  · exact book_end trees511e4e16 goods511e4e16k12 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims494e23 : Claim true 494 [23] 10 :=
  rename_rows claims191e12 [0,45,7,50,4,48,10,34,55,38,37,16,53,20,19,41,24,54,29,27,42,0,31,0,0,0,0,0,0,0,0,0,0,0,2,47,9,6,36,0,18,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e23 : Claim true 511 [23] 13 :=
  rename_rows claims511e38 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
def hintss511e4e23 (_ : Nat) : Nat := 0
def wiress511e4e23 (i : Nat) : W := bandWord (((if i < 8 then 0x80c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000094b41708e33838c7f084341300221808447090a40408c120308780 else 0xf007ffe000000000008c07801ffc0000000081cf1a590a52c2f92a) >>> (72*(i % 8))) % 4722366482869645213696)
def factss511e4e23 (i : Nat) : {f : Fact // Sound true f} := ⟨item 494 [23] 10,claims494e23⟩
def recss511e4e23 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levs511e4e23k12 (i : Nat) : Ticket := (#[⟨0x28a94370165b,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def trees511e4e23 : Book :=
  ⟨true,inputSet 511 [4,23],goalAt 511,12,1,readRule factss511e4e23 recss511e4e23,hintss511e4e23,3,unpackState wiress511e4e23 4,(fun k => match k with | 12 => 1 | _ => 0),fun k => match k with
    | 12 => levs511e4e23k12
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless511e4e23 : ∀ i, i < 1 → Valid true (goalAt 511) ((trees511e4e23).rule i) := by
  exact validateRules factss511e4e23 recss511e4e23 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e4e23k12i0 : bookRange trees511e4e23 12 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e4e23k12 : allGood trees511e4e23 12 :=
  book_level trees511e4e23 12 ruless511e4e23 (book_empty trees511e4e23 11 rfl) passs511e4e23k12i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4e23 : Claim true 511 [4,23] 13 := by
  apply low_search (s:=true) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4,23])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4,extraWord 511 23] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · have eq : remove (inputSet 511 [4,23]) (extraWord 511 4) = inputSet 511 [23] := by decide +kernel
      change Low true (remove (inputSet 511 [4,23]) (extraWord 511 4)) (goalAt 511) 13
      rw [eq]
      exact claims511e23
    · have eq : remove (inputSet 511 [4,23]) (extraWord 511 23) = inputSet 511 [4] := by decide +kernel
      change Low true (remove (inputSet 511 [4,23]) (extraWord 511 23)) (goalAt 511) 13
      rw [eq]
      exact claims511e4
  · exact book_end trees511e4e23 goods511e4e23k12 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims379e4 : Claim true 379 [4] 10 :=
  rename_rows claims191e4 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,0,13,0,0,0,0,0,0,0,0,0,0,0,24,25,31,54,29,0,30,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e27 : Claim true 511 [27] 13 :=
  rename_rows claims511e4 [0,4,7,10,45,48,50,16,19,20,53,34,37,38,55,41,2,6,9,47,18,21,36,39,11,14,15,51,52,22,40,13,23,57,24,27,29,54,31,32,42,26,30,33,44,1,5,8,46,49,17,35,56,3,12,25,28,43,58] (by decide +kernel)
def hintss511e4e27 (_ : Nat) : Nat := 0
def wiress511e4e27 (i : Nat) : W := bandWord (((if i < 8 then 0x81cf1a590a52c2f92a80c618110240c0f800821e00809004a4224c814d0248081202112ac204401c03ff000000a90420020380ff000084341300221808447090a40408c120308780 else 0xf007ffe000000000008c37931ffe180844708c07801ffc00000000) >>> (72*(i % 8))) % 4722366482869645213696)
def factss511e4e27 (i : Nat) : {f : Fact // Sound true f} := ⟨item 379 [4] 10,claims379e4⟩
def recss511e4e27 (i : Nat) : Recipe := (#[(0,[])] : Array Recipe).getD (i % 8) default
def levs511e4e27k12 (i : Nat) : Ticket := (#[⟨0x97a83260154b,2,0x0,0x0,0x0,0x0⟩] : Array Ticket).getD (i % 8) default
def trees511e4e27 : Book :=
  ⟨true,inputSet 511 [4,27],goalAt 511,12,1,readRule factss511e4e27 recss511e4e27,hintss511e4e27,3,unpackState wiress511e4e27 4,(fun k => match k with | 12 => 1 | _ => 0),fun k => match k with
    | 12 => levs511e4e27k12
    | _ => fun _ => default⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ruless511e4e27 : ∀ i, i < 1 → Valid true (goalAt 511) ((trees511e4e27).rule i) := by
  exact validateRules factss511e4e27 recss511e4e27 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem passs511e4e27k12i0 : bookRange trees511e4e27 12 0 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem goods511e4e27k12 : allGood trees511e4e27 12 :=
  book_level trees511e4e27 12 ruless511e4e27 (book_empty trees511e4e27 11 rfl) passs511e4e27k12i0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4e27 : Claim true 511 [4,27] 13 := by
  apply low_search (s:=true) (T:=goalAt 511) (raw:=rawSet 511) (es:=extraSet 511 [4,27])
  · decide +kernel
  · decide +kernel
  · intro w hw
    change w ∈ [extraWord 511 4,extraWord 511 27] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · have eq : remove (inputSet 511 [4,27]) (extraWord 511 4) = inputSet 511 [27] := by decide +kernel
      change Low true (remove (inputSet 511 [4,27]) (extraWord 511 4)) (goalAt 511) 13
      rw [eq]
      exact claims511e27
    · have eq : remove (inputSet 511 [4,27]) (extraWord 511 27) = inputSet 511 [4] := by decide +kernel
      change Low true (remove (inputSet 511 [4,27]) (extraWord 511 27)) (goalAt 511) 13
      rw [eq]
      exact claims511e4
  · exact book_end trees511e4e27 goods511e4e27k12 (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4e38 : Claim true 511 [4,38] 13 :=
  rename_rows claims511e4e23 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4e57 : Claim true 511 [4,57] 13 :=
  rename_rows claims511e4e16 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4e58 : Claim true 511 [4,58] 13 :=
  rename_rows claims511e4e12 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem claims511e4e68 : Claim true 511 [4,68] 13 :=
  rename_rows claims511e4e27 [0,1,16,17,45,46,53,7,8,20,50,11,12,22,51,15,2,3,18,47,9,21,13,23,34,35,41,55,56,38,40,36,39,57,24,25,31,54,29,32,30,26,42,43,44,4,5,19,48,49,10,14,52,6,37,27,28,33,58] (by decide +kernel)
end PEqualNP.Outside.L_meta_4413

theorem PEqualNP.Outside.L_meta_4413 : have x1 : List (BitVec (59 : ℕ)) := [(360930119642124586 : BitVec (59 : ℕ)), (432486920269079116 : BitVec (59 : ℕ)), (293578547141297264 : BitVec (59 : ℕ)), (289365901620316032 : BitVec (59 : ℕ)), (439119665042618368 : BitVec (59 : ℕ)), (297239789478805504 : BitVec (59 : ℕ)), (306275578149863424 : BitVec (59 : ℕ)), (540467122476679168 : BitVec (59 : ℕ)), (576425567931334656 : BitVec (59 : ℕ))]; have x2 : List (BitVec (59 : ℕ)) → Fin (3 : ℕ) × List (Fin (25 : ℕ)) → List (BitVec (59 : ℕ)) := fun (x2 : List (BitVec (59 : ℕ))) (x3 : Fin (3 : ℕ) × List (Fin (25 : ℕ))) =>   have x4 : List (BitVec (59 : ℕ)) := List.map (fun (x4 : Fin (25 : ℕ)) => x2.getD ↑x4 (0 : BitVec (59 : ℕ))) x3.2;   x2 ++ [if x3.1 = (0 : Fin (3 : ℕ)) then List.foldr (fun (x5 x6 : BitVec (59 : ℕ)) => x5 &&& x6) (~~~(0 : BitVec (59 : ℕ))) x4 else if x3.1 = (1 : Fin (3 : ℕ)) then List.foldr (fun (x5 x6 : BitVec (59 : ℕ)) => x5 ||| x6) (0 : BitVec (59 : ℕ)) x4 else ~~~x4.headD (0 : BitVec (59 : ℕ))]; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : List (Fin (3 : ℕ) × List (Fin (25 : ℕ)))) (x6 : Fin (25 : ℕ)),   (10 : ℕ) * Min.min ↑x3 ↑x4 + Max.max ↑x3 ↑x4 ∈ [(12 : ℕ), (16 : ℕ), (23 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (58 : ℕ), (68 : ℕ)] →     x5.length ≤ (13 : ℕ) →       (∀ x9 ∈ x5, x9.2.length ≤ (2 : ℕ)) →         (∀ (x10 : Fin (25 : ℕ)), ↑x10 < (9 : ℕ) → ∃ x12 ∈ x5, x10 ∈ if x12.1 = (2 : Fin (3 : ℕ)) then List.take (1 : ℕ) x12.2 else x12.2) →           have x11 : List (BitVec (59 : ℕ)) := x1 ++ [x1.getD (0 : ℕ) (0 : BitVec (59 : ℕ)) ||| x1.getD (4 : ℕ) (0 : BitVec (59 : ℕ)), x1.getD ↑x3 (0 : BitVec (59 : ℕ)) ||| x1.getD ↑x4 (0 : BitVec (59 : ℕ))];           have x12 : List (BitVec (59 : ℕ)) := List.foldl x2 x11 x5;           x12.getD ↑x6 (0 : BitVec (59 : ℕ)) ≠ (316380210352264264 : BitVec (59 : ℕ)) := by
  intro raw step a b gs out allowed small arity _
  apply PEqualNP.Outside.L_meta_4413.from_bounds a b gs out small arity
  · change PEqualNP.Outside.L_meta_4413.key a b ∈ [12,16,23,27,38,57,58,68] at allowed
    simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
    rcases allowed with h | h | h | h | h | h | h | h
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claimm511e4e12
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claimm511e4e16
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claimm511e4e23
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claimm511e4e27
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claimm511e4e38
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claimm511e4e57
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claimm511e4e58
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claimm511e4e68
  · change PEqualNP.Outside.L_meta_4413.key a b ∈ [12,16,23,27,38,57,58,68] at allowed
    simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
    rcases allowed with h | h | h | h | h | h | h | h
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claims511e4e12
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claims511e4e16
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claims511e4e23
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claims511e4e27
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claims511e4e38
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claims511e4e57
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claims511e4e58
    · rw [h]; exact PEqualNP.Outside.L_meta_4413.claims511e4e68
