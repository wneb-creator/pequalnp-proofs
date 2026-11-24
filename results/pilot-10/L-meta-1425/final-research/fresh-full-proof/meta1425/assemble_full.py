from pathlib import Path
import json,hashlib,re
B=Path('/tmp/oec/pequalnp-pilot-10');D=B/'fresh-full-proof/meta1425';NS='PEqualNP.Outside.L_meta_1425.Cert'
TS=[0xe8a8a8a8,0xe8a8e888,0xe8e8e880,0xeaa8a888,0xeaa8c888,0xeaa8e880,0xeaaac880,0xeac0e8c0,0xeac8e0c0,0xeac8e880]
CAPS=[5,6,7,8,6,8,6,5,4,8]
def body(p):return p.read_text().split('namespace '+NS,1)[1].rsplit('end '+NS,1)[0]
generic=(D/'FormalNatRun1425.lean').read_text().rsplit('end '+NS,1)[0]
for p in [B/'proof-strategy/meta1425/TightCoverSuffix1425.lean',B/'independent-theory/meta1425/GroupedCover1425.fragment.lean',B/'independent-theory/meta1425/GroupedTightCover1425.fragment.lean',D/'budget-bar.fragment.lean',B/'fresh-full-proof/meta984/cert_flat.fragment.lean']:
 generic+='\n'+p.read_text()+'\n'
generic+='\n'+body(B/'independent-theory/meta1425/MonotoneUpper1425V2.lean')
generic+='\ndef fld (x b j : Nat) : Nat := (x >>> (b*j)) &&& (2^b-1)\ndef hk (ws : List Nat) : Nat := (ws.map (fun w => (w+317)^3+1)).sum % 4294967291\n'
generic+=(B/'independent-search/1425/direct_tight/helpers.fragment.lean').read_text()
generic+='\ndef tableFn (T : Nat) : BFn 5 := fun x => Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0)\ndef allRows : List Nat := List.range 32\n'
parts={}
def joined(names):
 if len(names)==1:return names[0]
 m=len(names)//2
 return '(span_join '+joined(names[:m])+' '+joined(names[m:])+')'
for i,(t,cap) in enumerate(zip(TS,CAPS)):
 pre=f'C{i}';t=hex(t)
 data=(B/f'independent-search/1425/direct_tight/{pre}.data.fragment.lean').read_text()
 meta=json.loads((B/f'independent-search/1425/direct_tight/{pre}.data.json').read_text())
 pairs=json.loads((B/f'single-not-reduction/meta1425/t{i}-reduced-tight.pairs.json').read_text())
 groups={}
 for a,b in pairs:groups[a]=groups.get(a,0)|(1<<b)
 glit='['+', '.join(f'({a},{hex(mask)})' for a,mask in groups.items())+']'
 defs=data+f'''
def {pre}_groups : List (Nat × Nat) := {glit}
def {pre}_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover {pre}_groups ws else diffCover 0xffffffff {pre}_groups ws
def {pre}_Z := barBudget 0xffffffff {t} {pre}_cover {pre}_S {pre}_N {pre}_idx
def {pre}_flat := certAt {pre}_Z {pre}_N {cap+1}
'''
 checks=f'''
theorem {pre}_diff_good : diffGroupsGood 32 0xffffffff {t} {pre}_groups = true := by decide +kernel
theorem {pre}_dir_good : dirGroupsGood 32 {t} {pre}_groups = true := by decide +kernel
theorem {pre}_initial_ok : ∀ s ≤ {cap}, {pre}_initial.length ≤ s+1 → found {pre}_S {pre}_N {pre}_idx s {pre}_initial = true := by
  have h : ∀ s : Fin {cap+1}, {pre}_initial.length ≤ s.val+1 → found {pre}_S {pre}_N {pre}_idx s {pre}_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem {pre}_hnc : ∃ x x' : Fin 5 → Bool, tableFn {t} x ≠ tableFn {t} x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem {pre}_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = {pre}_initial := by decide +kernel
theorem {pre}_goal : encL (tableFn {t}) allRows = {t} := by decide +kernel
theorem {pre}_proper : ∀ zs ∈ {pre}_initial.sublists, zs ≠ {pre}_initial → diffCover 0xffffffff {pre}_groups zs = false := by decide +kernel
'''
 total=sum(v['N'] for v in meta['layers'].values());chunks=[]
 for k,start in enumerate(range(0,total,64)):
  n=min(64,total-start);name=f'{pre}_b{k}';chunks.append(name)
  checks+=f'\nset_option maxRecDepth 8192 in\nset_option maxHeartbeats 0 in\ntheorem {name} : span {pre}_flat {n} {start} = true := by decide +kernel\n'
 joins=f'''
theorem {pre}_checked : ∀ s ≤ {cap}, ∀ i < {pre}_N s, {pre}_Z s i = true := by
  apply certFlat_sound
  exact {joined(chunks)}
theorem {pre}_cover_ok {{s ws}} (h : NatRun 0xffffffff {t} s ws) : {pre}_cover s ws = true := by
  unfold {pre}_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› {pre}_dir_good
  · exact diffCover_ok_of_good h {pre}_diff_good
theorem {pre}_no_run : ∀ s ≤ {cap}, ¬ NatRun 0xffffffff {t} s {pre}_initial :=
  noRun_from_barBudget (fun h => {pre}_cover_ok h) {pre}_checked {pre}_initial_ok
theorem {pre}_lower : ¬ HasCircuitSize 5 (tableFn {t}) {cap} :=
  encoded_exclusion (tableFn {t}) {pre}_hnc {cap} allRows {pre}_initial 0xffffffff {t}
    (diffCover 0xffffffff {pre}_groups) (fun h => diffCover_ok_of_good h {pre}_diff_good)
    {pre}_inputs (by decide +kernel) {pre}_goal {pre}_proper {pre}_no_run
'''
 parts[i]=(defs,checks,joins,meta)

tset='({'+', '.join(hex(t) for t in TS)+'} : Finset Nat)'
final=f'''\ntheorem table_lower (T : Nat) (hT : T ∈ {tset}) :
    ¬ HasCircuitSize 5 (tableFn T) (upperBudget T - 1) := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
'''
for i in range(10):final+=f'  · exact C{i}_lower\n'
statement=(B/'statement-meta-1425.txt').read_text().strip()
final+='\ntheorem solution :\n    '+statement+''' := by
  intro T hT gates o hfan _hnot heval
  apply monotone_equivalent_of_upperBudget_le T hT gates
  by_contra! hsize
  apply table_lower T hT
  refine ⟨⟨gates,o⟩,hfan,?_,heval⟩
  change gates.length ≤ upperBudget T - 1
  omega
'''
full=generic+''.join(parts[i][0] for i in range(10))+''.join(parts[i][1] for i in range(10))+''.join(parts[i][2] for i in range(10))+final+'\nend '+NS+'\n'
(D/'Full1425-tight-v1.lean').write_text(full)
# Small complete strong instance, with same exact data, checks, and lower.
i=8
small=generic+''.join(parts[i][:3])+'''
theorem C8_monotone_equivalent (gates : List Gate) (o : Nat)
    (hfan : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) =
      Nat.testBit 0xeac8e0c0 (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0)) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates',o'⟩ (List.ofFn x) =
        Nat.testBit 0xeac8e0c0 (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0) := by
  have hsize : 5 ≤ gates.length := by
    by_contra! h
    apply C8_lower
    refine ⟨⟨gates,o⟩,hfan,?_,heval⟩
    change gates.length ≤ 4
    omega
  exact ⟨upperCircuit8.gates,upperCircuit8.output,upperCircuit8_mono,hsize,upperCircuit8_computes⟩
'''+'\nend '+NS+'\n'
(D/'CompleteT8Tight1425-v1.lean').write_text(small)
# Representative hardest-table large layer check, no claim of full lower bound.
i=3;meta=parts[i][3];layer=max(meta['layers'],key=lambda k:meta['layers'][k]['N'])
bench=generic+parts[i][0]+re.split(r'\nset_option maxRecDepth',parts[i][1],1)[0]+f'''\nset_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_benchmark : span (C3_Z {layer}) 32 0 = true := by decide +kernel
'''+ '\nend '+NS+'\n'
(D/'Hard32Tight1425-v1.lean').write_text(bench)
for name in ['Full1425-tight-v1.lean','CompleteT8Tight1425-v1.lean','Hard32Tight1425-v1.lean']:
 p=D/name;print(name,len(p.read_bytes()),hashlib.sha256(p.read_bytes()).hexdigest())
print('HARD_LAYER',layer,'N',meta['layers'][layer]['N'])
assert len(full.encode())<=524288
assert not re.search(r'\b(sorry|axiom|native_decide|unsafe|admit)\b',full)
assert '"' not in full
