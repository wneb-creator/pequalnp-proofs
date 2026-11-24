from pathlib import Path
import ast,json,hashlib
BASE=Path('/tmp/oec/pequalnp-pilot-10')
HERE=BASE/'independent-theory/meta1425'
SEARCH=BASE/'independent-search/1425'
formulas=json.loads((BASE/'proof-strategy/meta1425/formula-upperbounds.json').read_text())
Ts=[int(d['table'],16) for d in formulas]
chosen=[]
for i,t in enumerate(Ts):
 candidates=[]
 for p in SEARCH.glob(f't{i}-mono*.result.json'):
  d=json.loads(p.read_text())
  if d.get('result')=='sat':
   assert int(d['target'],16)==t
   candidates.append((len(d['gates']),d['gates'],d['output'],str(p)))
 formula=formulas[i]['formula']
 gs=[]
 def visit(n):
  if isinstance(n,ast.Constant):
   assert isinstance(n.value,int) and 0<=n.value<5
   return n.value
  assert isinstance(n,ast.BinOp)
  a,b=visit(n.left),visit(n.right)
  assert isinstance(n.op,(ast.BitAnd,ast.BitOr))
  gs.append({'op':'and' if isinstance(n.op,ast.BitAnd) else 'or','inputs':[a,b]})
  return 5+len(gs)-1
 out=visit(ast.parse(formula,mode='eval').body)
 candidates.append((len(gs),gs,out,'formula-upperbounds.json'))
 n,gs,out,src=min(candidates,key=lambda v:v[0])
 actual=0
 for x in range(32):
  ws=[bool(x>>j&1) for j in range(5)]
  for g in gs:
   a,b=(ws[j] for j in g['inputs'])
   ws.append(a and b if g['op']=='and' else a or b)
  actual |= int(ws[out])<<x
 assert actual==t,(i,hex(actual),hex(t))
 chosen.append({'table':hex(t),'count':n,'gates':gs,'output':out,'source':src})
lines=['import Mathlib','import PEqualNP.Defs','','namespace PEqualNP.Outside.L_meta_1425.Cert','','open PEqualNP.CircuitLowerBounds','','-- Explicit upper bounds only; no minimality or NOT-elimination claim.',
'def upperMono (C : Circuit) : Prop :=',
'  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2','',
'def upperComputes (C : Circuit) (T : Nat) : Prop :=',
'  ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) =',
'    Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0)','']
for i,d in enumerate(chosen):
 gates=', '.join('⟨.'+g['op']+', ['+','.join(map(str,g['inputs']))+']⟩' for g in d['gates'])
 lines += [f'def upperCircuit{i} : Circuit := ⟨[{gates}], {d["output"]}⟩',
 f'theorem upperCircuit{i}_mono : upperMono upperCircuit{i} := by',
 f'  simp [upperMono, upperCircuit{i}]',
 f'theorem upperCircuit{i}_computes : upperComputes upperCircuit{i} {d["table"]} := by',
 '  decide +kernel','']
lines += ['def upperBudget (T : Nat) : Nat :=']
for i,d in enumerate(chosen):
 lines += [f'  if T = {d["table"]} then {d["count"]} else']
lines += ['  0','',
 'theorem monotone_upper (T : Nat)',
 '    (hT : T ∈ ({'+', '.join(hex(t) for t in Ts)+'} : Finset Nat)) :',
 '    ∃ C : Circuit, upperMono C ∧ C.gates.length = upperBudget T ∧ upperComputes C T := by',
 '  simp only [Finset.mem_insert, Finset.mem_singleton] at hT',
 '  rcases hT with '+ ' | '.join(['rfl']*10)]
for i,d in enumerate(chosen):
 lines += [f'  · exact ⟨upperCircuit{i}, upperCircuit{i}_mono, by decide +kernel, upperCircuit{i}_computes⟩']
lines += ['',
 'theorem monotone_equivalent_of_upperBudget_le (T : Nat)',
 '    (hT : T ∈ ({'+', '.join(hex(t) for t in Ts)+'} : Finset Nat))',
 '    (gates : List Gate) (hsize : upperBudget T ≤ gates.length) :',
 '    ∃ (gates\' : List Gate) (o\' : Nat),',
 '      (∀ g ∈ gates\', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧',
 '      gates\'.length ≤ gates.length ∧',
 '      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates\', o\'⟩ (List.ofFn x) =',
 '        Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0) := by',
 '  rcases monotone_upper T hT with ⟨C, hmono, hlen, heval⟩',
 '  exact ⟨C.gates, C.output, hmono, hlen.le.trans hsize, heval⟩','',
 'end PEqualNP.Outside.L_meta_1425.Cert','']
p=HERE/'MonotoneUpper1425.lean';p.write_text('\n'.join(lines))
(HERE/'upper-witnesses.json').write_text(json.dumps(chosen,indent=2)+'\n')
print(json.dumps({'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines()),'bytes':p.stat().st_size,'budgets':[d['count'] for d in chosen]},indent=2))
