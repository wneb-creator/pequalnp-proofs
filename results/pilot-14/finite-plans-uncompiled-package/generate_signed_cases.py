from pathlib import Path
import argparse,json
ap=argparse.ArgumentParser()
ap.add_argument('--outdir',required=True)
ap.add_argument('--pairs',required=True)
ap.add_argument('--skip',default='')
a=ap.parse_args()
out=Path(a.outdir);out.mkdir(parents=True,exist_ok=True)
pairs=[(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)]
skip={tuple(map(int,x.split(':')))for x in a.skip.split(',')if x}
costs=json.loads(Path('/tmp/oec/pequalnp-pilot-14/status-review/SlackOneAllCaseCosts.json').read_text())['rows']
manifest=[]
def put(name,imports,ns,body):
 s=''.join('import '+i+'\n'for i in imports)+'namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.'+ns+'\nopen LiveCheck TightFormula\n'+body+'\nend PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.'+ns+'\n'
 (out/(name+'.lean')).write_text(s)
 return name
limit='set_option maxRecDepth 20000 in\nset_option maxHeartbeats 0 in\n'
for p in map(int,a.pairs.split(',')):
 i,j=pairs[p]
 for u in range(4):
  if(p,u)in skip:continue
  name=f'SignedCaseP{p}U{u}';ns=f'FiniteP{p}U{u}'
  actual=u^((int(i in[0,4])<<1)|int(j in[0,4]))
  cost=next(c for c in costs if c['pair']==[i,j]and c['sign']==actual)
  hard=[n for n,c in cost['duplicates']if c>200]
  order=[]
  common=put(name+'Common',['UnorderedEndgameTest'],ns,
   f'def state : List Sig := (ops (phase (raw.getD {i} zero)) (phase (raw.getD {j} zero))).getD {u} zero :: inputs\n')
  order.append(common)
  hardmods=[]
  for d in hard:
   mod=put(name+f'Dup{d}',[common],ns,
    f'def duplicate{d} : List Sig := state[{d}] :: state\n'+limit+
    f'lemma duplicate{d}_children (i : Fin (UnorderedPairs.steps duplicate{d}).length) :\n'
    f'    ((unionSep true (UnorderedPairs.steps duplicate{d})[i] == top) &&\n'
    f'      UnorderedFormula.test 3 (UnorderedPairs.steps duplicate{d})[i]) = false := by\n'
    f'  fin_cases i <;> decide +kernel\n\n'
    f'lemma duplicate{d}_excluded : UnorderedFormula.test 4 duplicate{d} = false :=\n'
    f'  test_succ_false 3 duplicate{d} (by decide +kernel) duplicate{d}_children\n')
   order.append(mod);hardmods.append(mod)
  proof='  fin_cases i\n'+''.join(('  · exact duplicate'+str(d)+'_excluded\n')if d in hard else('  · decide +kernel\n')for d in range(10))
  dup=put(name+'Duplicates',[common]+hardmods,ns,limit+
   'lemma duplicates (i : Fin state.length) :\n'
   '    UnorderedFormula.test 4 (state[i] :: state) = false := by\n'+proof)
  consume=put(name+'Consume',[common],ns,limit+
   'lemma consume (i : Fin (UnorderedPairs.steps state).length) :\n'
   '    ((unionSep true (UnorderedPairs.steps state)[i] == top) &&\n'
   '      UnorderedFormula.testOne 3 (UnorderedPairs.steps state)[i]) = false := by\n'
   '  fin_cases i <;> decide +kernel\n')
  keep=put(name+'Keep',[common],ns,limit+
   'lemma keep (i : Fin (UnorderedPairs.keepSteps state).length) :\n'
   '    ((unionSep true (UnorderedPairs.keepSteps state)[i] == top) &&\n'
   '      UnorderedFormula.test 3 (UnorderedPairs.keepSteps state)[i]) = false := by\n'
   '  fin_cases i <;> decide +kernel\n')
  closed=put(name+'Closed',[dup,consume,keep],ns,
   'lemma excluded : UnorderedFormula.testOne 4 state = false :=\n'
   '  testOne_succ_false 3 state (by decide +kernel) duplicates consume keep\n')
  order += [dup,consume,keep,closed]
  manifest.append({'pair_index':p,'pair':[i,j],'canonical_sign':u,'actual_sign':actual,'hard_duplicates':hard,'namespace':'PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.'+ns,'modules':order,'closed':closed})
(out/'signed-cases-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps([{'pair':x['pair'],'canonical_sign':x['canonical_sign'],'hard_duplicates':x['hard_duplicates']}for x in manifest]))
