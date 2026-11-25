import Mathlib.Data.Finset.Sort
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0

def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]

def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0

def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

lemma gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, hM]

lemma getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

lemma wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

lemma eval_tabs (C : Circuit) (hC : Monotone2 C) (M p : ℕ)
    (hM : M.testBit p = true) (T0 : List ℕ) :
    C.eval (T0.map fun t => t.testBit p) =
      ((tabs M T0 C.gates).getD C.output 0).testBit p := by
  unfold Circuit.eval Circuit.wires
  rw [wires_tabs M p hM C.gates T0]
  · exact getD_map_testBit _ _ _
  · intro g hg
    obtain ⟨hop, hlen⟩ := hC g hg
    refine ⟨?_, hlen⟩
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hop
    rcases hop' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

lemma eval_of_table {n : ℕ} (C : Circuit) (hC : Monotone2 C)
    (cols : List ℕ) (target : ℕ) (x : Fin n → Fin 26 → Bool)
    (hcols : ∀ p : Fin n, cols.map (fun t => t.testBit p.val) = List.ofFn (x p))
    (hout : (tabs (2 ^ n - 1) cols C.gates).getD C.output 0 = target) :
    ∀ p : Fin n, C.eval (List.ofFn (x p)) = target.testBit p.val := by
  intro p
  rw [← hcols p, eval_tabs C hC (2 ^ n - 1) p.val, hout]
  rw [Nat.testBit_two_pow_sub_one]
  simp [p.isLt]



def pack : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (pack bs)

lemma pack_testBit (l : List Bool) (p : ℕ) :
    (pack l).testBit p = l.getD p false := by
  induction l generalizing p with
  | nil => simp [pack]
  | cons b bs ih =>
    cases p with
    | zero => simp [pack]
    | succ p => simpa only [pack, Nat.testBit_bit_succ, List.getD_cons_succ] using ih p

def columns (tests : List ((Fin 26 → Bool) × Bool)) : List ℕ :=
  List.ofFn fun i : Fin 26 => pack (tests.map fun t => t.1 i)

def desired (tests : List ((Fin 26 → Bool) × Bool)) : ℕ :=
  pack (tests.map Prod.snd)

lemma columns_row (tests : List ((Fin 26 → Bool) × Bool))
    (row : (Fin 26 → Bool) × Bool) (p : ℕ) (hp : tests[p]? = some row) :
    (columns tests).map (fun t => t.testBit p) = List.ofFn row.1 := by
  simp only [columns, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [pack_testBit]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hp]

lemma desired_row (tests : List ((Fin 26 → Bool) × Bool))
    (row : (Fin 26 → Bool) × Bool) (p : ℕ) (hp : tests[p]? = some row) :
    (desired tests).testBit p = row.2 := by
  rw [desired, pack_testBit]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hp]

lemma checks_of_packed (C : Circuit) (hC : Monotone2 C)
    (tests : List ((Fin 26 → Bool) × Bool)) (T : List ℕ) (target : ℕ)
    (hcols : columns tests = T) (htarget : desired tests = target)
    (hout : (tabs (2 ^ tests.length - 1) T C.gates).getD C.output 0 = target) :
    ∀ row ∈ tests, C.eval (List.ofFn row.1) = row.2 := by
  intro row hrow
  obtain ⟨p, hp, hget⟩ := List.mem_iff_getElem.mp hrow
  have hget' : tests[p]? = some row := by simp [hp, hget]
  rw [← columns_row tests row p hget', hcols,
    eval_tabs C hC (2 ^ tests.length - 1) p]
  · rw [hout, ← htarget]
    exact desired_row tests row p hget'
  · rw [Nat.testBit_two_pow_sub_one]
    simp [hp]


lemma small_set_check {α : Type*} [LinearOrder α] (P : Finset α → Prop)
    (h0 : P ∅)
    (h1 : ∀ a, P {a})
    (h2 : ∀ a b, a < b → P {a, b})
    (h3 : ∀ a b c, a < b → b < c → P {a, b, c}) :
    ∀ s : Finset α, s.card ≤ 3 → P s := by
  intro s hs
  have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hc with hc | hc | hc | hc
  · exact (Finset.card_eq_zero.mp hc) ▸ h0
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    exact h1 a
  · let f := s.orderEmbOfFin hc
    have he : ({f 0, f 1} : Finset α) = s := by
      have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      simpa only [hu, Finset.image_insert, Finset.image_singleton] using
        s.image_orderEmbOfFin_univ hc
    rw [← he]
    exact h2 _ _ (f.strictMono (by decide))
  · let f := s.orderEmbOfFin hc
    have he : ({f 0, f 1, f 2} : Finset α) = s := by
      have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      simpa only [hu, Finset.image_insert, Finset.image_singleton] using
        s.image_orderEmbOfFin_univ hc
    rw [← he]
    exact h3 _ _ _ (f.strictMono (by decide)) (f.strictMono (by decide))


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev incident (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ [0, 1, 3, 9]

def input (S T : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ S)
  else decide (Fin.ofNat 13 i.val ∈ T)

def common (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ S, ¬ incident p l

def smallSets : List (Finset (Fin 13)) :=
  [∅] ++ (List.finRange 13).map (fun a => {a}) ++
    (List.finRange 13).flatMap (fun a =>
      ((List.finRange 13).filter (fun b => decide (a < b))).map fun b => {a, b}) ++
    (List.finRange 13).flatMap (fun a =>
      ((List.finRange 13).filter (fun b => decide (a < b))).flatMap fun b =>
        ((List.finRange 13).filter (fun c => decide (b < c))).map fun c => {a, b, c})

lemma small_empty : (∅ : Finset (Fin 13)) ∈ smallSets := by
  simp [smallSets]

lemma small_single (a : Fin 13) : ({a} : Finset (Fin 13)) ∈ smallSets := by
  simp only [smallSets, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨a, by simp, rfl⟩)))

lemma small_pair (a b : Fin 13) (hab : a < b) :
    ({a, b} : Finset (Fin 13)) ∈ smallSets := by
  simp only [smallSets, List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨a, by simp,
    List.mem_map.mpr ⟨b, by simp [hab], rfl⟩⟩))

lemma small_triple (a b c : Fin 13) (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset (Fin 13)) ∈ smallSets := by
  simp only [smallSets, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨a, by simp,
    List.mem_flatMap.mpr ⟨b, by simp [hab],
      List.mem_map.mpr ⟨c, by simp [hbc], rfl⟩⟩⟩)

def tests : List ((Fin 26 → Bool) × Bool) :=
  (List.finRange 13).flatMap (fun p => (List.finRange 13).map fun l =>
    (input {p} {l}, decide (incident p l))) ++
  smallSets.flatMap (fun S =>
    [(input S (common S), false), (input (common S) S, false)])

lemma positive_mem (p l : Fin 13) (h : incident p l) :
    (input {p} {l}, true) ∈ tests := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨p, by simp, List.mem_map.mpr ⟨l, by simp, ?_⟩⟩
  simp [h]

lemma negative_mem (S : Finset (Fin 13)) (h : S ∈ smallSets) :
    (input S (common S), false) ∈ tests ∧
    (input (common S) S, false) ∈ tests := by
  constructor
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨S, h, by simp⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨S, h, by simp⟩)

lemma small_mem (S : Finset (Fin 13)) (h : S.card ≤ 3) : S ∈ smallSets :=
  small_set_check (fun T => T ∈ smallSets) small_empty small_single small_pair small_triple S h

lemma exact_tests_of_suite (C : Circuit)
    (h : ∀ row ∈ tests, C.eval (List.ofFn row.1) = row.2) :
    (∀ p l : Fin 13, incident p l → C.eval (List.ofFn (input {p} {l})) = true) ∧
      ∀ S : Finset (Fin 13), S.card ≤ 3 →
        C.eval (List.ofFn (input S (common S))) = false ∧
        C.eval (List.ofFn (input (common S) S)) = false := by
  constructor
  · intro p l hp
    exact h (input {p} {l}, true) (positive_mem p l hp)
  · intro S hS
    have hn := negative_mem S (small_mem S hS)
    exact ⟨h (input S (common S), false) hn.1, h (input (common S) S, false) hn.2⟩

def star : Circuit :=
  ⟨[⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [16, 22]⟩,
    ⟨GateOp.or, [26, 27]⟩,
    ⟨GateOp.and, [0, 28]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [21, 25]⟩,
    ⟨GateOp.or, [30, 31]⟩,
    ⟨GateOp.and, [1, 32]⟩,
    ⟨GateOp.or, [14, 20]⟩,
    ⟨GateOp.or, [24, 25]⟩,
    ⟨GateOp.or, [34, 35]⟩,
    ⟨GateOp.and, [2, 36]⟩,
    ⟨GateOp.or, [13, 19]⟩,
    ⟨GateOp.or, [23, 24]⟩,
    ⟨GateOp.or, [38, 39]⟩,
    ⟨GateOp.and, [3, 40]⟩,
    ⟨GateOp.or, [18, 22]⟩,
    ⟨GateOp.or, [23, 25]⟩,
    ⟨GateOp.or, [42, 43]⟩,
    ⟨GateOp.and, [4, 44]⟩,
    ⟨GateOp.or, [17, 21]⟩,
    ⟨GateOp.or, [22, 24]⟩,
    ⟨GateOp.or, [46, 47]⟩,
    ⟨GateOp.and, [5, 48]⟩,
    ⟨GateOp.or, [16, 20]⟩,
    ⟨GateOp.or, [21, 23]⟩,
    ⟨GateOp.or, [50, 51]⟩,
    ⟨GateOp.and, [6, 52]⟩,
    ⟨GateOp.or, [15, 19]⟩,
    ⟨GateOp.or, [20, 22]⟩,
    ⟨GateOp.or, [54, 55]⟩,
    ⟨GateOp.and, [7, 56]⟩,
    ⟨GateOp.or, [14, 18]⟩,
    ⟨GateOp.or, [19, 21]⟩,
    ⟨GateOp.or, [58, 59]⟩,
    ⟨GateOp.and, [8, 60]⟩,
    ⟨GateOp.or, [13, 17]⟩,
    ⟨GateOp.or, [18, 20]⟩,
    ⟨GateOp.or, [62, 63]⟩,
    ⟨GateOp.and, [9, 64]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [19, 25]⟩,
    ⟨GateOp.or, [66, 67]⟩,
    ⟨GateOp.and, [10, 68]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.or, [18, 24]⟩,
    ⟨GateOp.or, [70, 71]⟩,
    ⟨GateOp.and, [11, 72]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.or, [17, 23]⟩,
    ⟨GateOp.or, [74, 75]⟩,
    ⟨GateOp.and, [12, 76]⟩,
    ⟨GateOp.or, [29, 33]⟩,
    ⟨GateOp.or, [78, 37]⟩,
    ⟨GateOp.or, [79, 41]⟩,
    ⟨GateOp.or, [80, 45]⟩,
    ⟨GateOp.or, [81, 49]⟩,
    ⟨GateOp.or, [82, 53]⟩,
    ⟨GateOp.or, [83, 57]⟩,
    ⟨GateOp.or, [84, 61]⟩,
    ⟨GateOp.or, [85, 65]⟩,
    ⟨GateOp.or, [86, 69]⟩,
    ⟨GateOp.or, [87, 73]⟩,
    ⟨GateOp.or, [88, 77]⟩], 89⟩

def cols : List ℕ := [142540229436419592040194909678370738424624817996974584031451423622900299229973328029634552068394997567884250896300369264326973279725264901282833995324646791569238754162081984799693405991683572114744962632400335448325072592955741675819262080972927115469248414951636719097912238079,
  2215836978209798327001382209908848473336520510428738262691956507384309394754679257508255185106944234910524453064513691489216999446360696239803893222088987558652702446168914995648517812998743875714809314784581937125738686464312885819797870315339427304052064226467973793834852352,
  540973600011336506959346213439819242782180916454350140761076689340517805136029099599923734385084166272070609059114051761254539660216036795414033357693016417645805226648533770889092152331209535734380813394873918205391756844397798279108599742420489344760520909604815030452224,
  8657724310572106100379914017712117736982602239004883635998867808692488977932366253290112401165600757565254374828871913255084797447677275886572748416879598593780222499019454323799258845468103703115039846391997275108717637121169652991576897680808133976479754070934499115401216,
  8254609952428005762800228648035608003950995642891624655263501502376916573558172594571294904207321164341355068043304315015623068054969662052033295369741074898629900188409642925013180282212892556882602034845533082561204159696325138458226551323576959785104934881577664512,
  33810882237352630615692494030330908267952616212369892104350393927329279654970490607103660689294713112935240544116013158393788586522119817484251497175020535047446343055139834977451036499213722892308293872861422973207654367909389703682141273139714521434247484375620978212864,
  35453245842144607266683168181340768856367769182974139730037945849010013614711320815804335285882828488931070187860870213215323742003718763516182414014263749642987703976313696122868652252334659618224452143610757826643699074329256417953822587998369343486697328383024056153891930112,
  142540142048131806174831287914308163458570482994672327529862291708794735322987247042298921460946437922096394870116797514535343967753777305201325306903485552855296096261924935419473465508939264538035783930393780718867194937555483902220131887560671604923047980523661679374951776256,
  188714763319593000638666484712111838486172716965126607188099996698776177552110634581559868868693935855763908084767593968150856841931508850672384212779211621019656789102095030169187273184880962355049390641138874912612241545977689428430427449592847084476367562195525866074409009152,
  212355671692845876920733640624047534538210523357952552150731425797714029431401543000332948175758708676166807919528150689914985733663822283387442771562203004533490726230763362238970348727241995123438640054567382580338835428302332873114103212554930861949335995909021833532335456256,
  78786072975733869207983144611187613524890028380663891612659751804937151135406775357219094378663991588247845313812861769007241295632617902304012604572358905882507052113570849330815407447421299581765144928945878825606256093785987082081504422385296546831722905077301882277481938944,
  99047505584297645431091082377603744131147456633558689120342064986842409254042141399755024800705488729946333099057178003412233130723196837987035604619166271024192696093865574412745860967717760933880993310869560429793837861664957059473644926473705422650376029580866076124433612800,
  129433567035085698670813841293856020773126778245985868855998783454611185327914806090282941080497157784455958281866021566676948470163812511237094926392647738951080165197742372626522409093507062622473379142600791339907634403797619673523848767222139840025002255670544739263043338240,
  71270114718209796020097454839185369212312408998487292015725711811450149614986664014817276034197498783942125448150184632163486639862682398618222053538025501340296067741932960796134878573969486125442906055673520789509501087265683469897011829859838916428597892445119082250375274497,
  1107918489104899163500691104954424236668260255214369131345978253692154697377339628754127592553472182291442990297771822500981369897523384712569269523418950655795437017121170756403426508963468879513101110845640101843848680973455912420475435290073772153614572797895551502124072962,
  270486800005668253479673106719909621391090458227175070380538344670339165872176359698448820773453811418552031260106746159718317917283108183074294294551908536214432136642310082361313511429115813149465570578119010092186390785247024683890961309145775453656305546744503514202116,
  4328862155286053050189957008856058868491301119881474555377536671716520546087436979651082451770805756854000214191959192881999878773164171582527681419710873505841573297912433896876797295227778932804541888848098355927471452739496920086157956317409259928997156176437537872609288,
  4127304976214002881400141636204921077858225419781369019141577555436365288773350383959278649099855167581514484696078428368822292149184472674246724512800311630878526285982067279850495164093429159065295530017053438358022258483430457422930411585749060246887198433254440976,
  16905441118676435428115507863056946555429762841000119563258427172929683086129479401589769534934689813984913754882066577155232832807953796716356587905060679603301730905699235048677707698381521880889395502888097468314310305839131157855416935015365511763350355765370556776480,
  17726622921201281790237007094556591836050681177066455443188849759743616468793226319098515842919424381833471588970926732344095587776713630809167164882430320636761679337188696395217627867742496199691568396044678581620030264036635599302448873689179056043444466578160948743795900480,
  71270206267336895783586202451422941408458210286885227787471991605170169640519548761514058588928357172155581023794878430566861117899807342689614820161619103226955294604547231230522254086685127088252938366259988015011600107756380003577871286971159115464844119585494602704122544256,
  94911203415566102315517961242899346448792881027882855013101936679913140889345889305167672621818252544183510135297580562223617196408460622280301957574303298726137199818287292624125467018434500243038063466436745512743669678061020724083124514822373446286621663412342885891440640256,
  141085647136816742698163304884252770653096002740131918113810884009309037341946005338005505137895921582089389857603188827877245429121277124087765648500823156230221951346985626032035145093552594206478645843185044261401571179650790557297556903071404511968498022076651519819724620288,
  154192399700326947223033119266093608555047112086158643686123250745304171795384147808863928851190512048178216420514619472878743311147218726233505273005318430722360447442462787667867997997354192246470928501858998290390698521222578402518968582506420661890737407153828986007492494336,
  184578461151119351104746167295065306878806606756796804991583257322285348425010184600551333014416349922196460436992185255109124728491764241131223790070672792463237716006640622659112966773193046397489593515252560658471910971112374680210238257164945304178168219531024541191365462016,
  204839893759674426043825442846697572507689908952868151403839183984085535421018651507187635586003692418449346233725297543508830184645677325962035913762948479947456901956204787596977220575471367979805545092046568371316001636869564197876074016744657834300926485534698992970921676800]

lemma star_mono : Monotone2 star := by
  simp [Monotone2, star]

lemma star_size : star.size = 64 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma table_out : (tabs (2 ^ 925 - 1) cols star.gates).getD star.output 0 = 95569001814980550449331158939433059977520687915531 := by
  decide +kernel


set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma columns_eq : columns tests = cols := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma desired_eq : desired tests = 95569001814980550449331158939433059977520687915531 := by
  decide +kernel

set_option maxRecDepth 8192 in
lemma tests_length : tests.length = 925 := by
  decide +kernel

lemma exact_tests_of_table (C : Circuit) (hC : Monotone2 C)
    (hout : (tabs (2 ^ 925 - 1) cols C.gates).getD C.output 0 =
      95569001814980550449331158939433059977520687915531) :
    (∀ p l : Fin 13, incident p l → C.eval (List.ofFn (input {p} {l})) = true) ∧
      ∀ S : Finset (Fin 13), S.card ≤ 3 →
        C.eval (List.ofFn (input S (common S))) = false ∧
        C.eval (List.ofFn (input (common S) S)) = false := by
  apply exact_tests_of_suite C
  apply checks_of_packed C hC tests cols _ columns_eq desired_eq
  simpa only [tests_length] using hout

lemma star_checks :
    (∀ p l : Fin 13, incident p l → star.eval (List.ofFn (input {p} {l})) = true) ∧
      ∀ S : Finset (Fin 13), S.card ≤ 3 →
        star.eval (List.ofFn (input S (common S))) = false ∧
        star.eval (List.ofFn (input (common S) S)) = false :=
  exact_tests_of_table star star_mono table_out

lemma witness_of_table (C : Circuit) (hC : Monotone2 C) (hs : C.size ≤ 63)
    (hout : (tabs (2 ^ 925 - 1) cols C.gates).getD C.output 0 =
      95569001814980550449331158939433059977520687915531) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  refine ⟨C, hC, hs, ?_⟩
  exact exact_tests_of_table C hC hout

lemma baseline64 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (64 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  refine ⟨star, star_mono, ?_, ?_⟩
  · exact Nat.le_of_eq star_size
  · exact star_checks

end PEqualNP.Outside.L_meta_2056_aux
