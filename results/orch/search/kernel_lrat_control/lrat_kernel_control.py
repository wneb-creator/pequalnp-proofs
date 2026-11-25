from pathlib import Path
import collections,json,hashlib

SCRATCH=Path('/tmp/oec/pequalnp-pilot-64')
REPO=Path('/workspace/pequalnp-proofs')
stem=SCRATCH/'path-center5-replay'
cnf=SCRATCH/'audit-path-center5.cnf'
clauses=[]
for line in cnf.read_text().splitlines():
    if line.startswith(('c','p')):continue
    values=list(map(int,line.split()));assert values[-1]==0
    clauses.append(values[:-1])
db={i+1:tuple(c) for i,c in enumerate(clauses)}
steps=[]
for line in stem.with_suffix('.lrat').read_text().splitlines():
    parts=line.split()
    if 'd' in parts:continue
    vals=list(map(int,parts));cid=vals[0];z=vals.index(0)
    clause=tuple(vals[1:z]);hints=vals[z+1:-1]
    assert vals[-1]==0 and all(h>0 for h in hints)
    false=set(clause);used=[]
    for hint in hints:
        remainder=set(db[hint])-false
        if not remainder:
            used.append((hint,None));break
        assert len(remainder)==1,(cid,hint,remainder)
        unit=next(iter(remainder));used.append((hint,unit));false.add(-unit)
    else:raise AssertionError(('no conflict',cid))
    assert cid not in db
    db[cid]=clause;steps.append((cid,clause,used))
assert not steps[-1][1]
byid={c[0]:c for c in steps};needed={steps[-1][0]};todo=list(needed)
while todo:
    cid=todo.pop()
    if cid not in byid:continue
    for hint,_ in byid[cid][2]:
        if hint not in needed:needed.add(hint);todo.append(hint)
trim=[x for x in steps if x[0] in needed]
freq=collections.Counter(h for _,_,hs in trim for h,_ in hs)
keys={cid:i for i,cid in enumerate(sorted(needed,key=lambda x:(-freq[x],x)))}
def lit(x):return 2*abs(x)+(x<0)
tokens=[]
for cid,clause,hs in trim:
    tokens += [keys[cid],*[lit(x) for x in clause],0]
    for h,u in hs:
        tokens.append(keys[h])
        if u is not None:tokens.append(lit(u))
width=max(tokens).bit_length();words=[]
for start in range(0,len(tokens),128):
    ts=tokens[start:start+128];word=1
    for token in reversed(ts):word=(word<<width)|token
    words.append(word)
formula=[[lit(x) for x in c] for c in clauses]
fk=[keys[i+1]+1 if i+1 in needed else 0 for i in range(len(clauses))]
def lean_list(xs):return '['+','.join(map(str,xs))+']'
checker=(REPO/'lean/PEqualNP/Library/LRAT/Checker.lean').read_text().replace('("words")','(words)')
out=REPO/'results/orch/lemmas/Reductions.lean'
out.parent.mkdir(parents=True,exist_ok=True)
body='import PEqualNP.Defs.CircuitLowerBounds\n\n'+checker+'\n\nnamespace PEqualNP.Outside.Pilot64KernelControl\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
body+='def formula : List (List Nat) :=\n  ['+',\n   '.join(lean_list(c) for c in formula)+']\n\n'
body+='def initialKeys : List Nat :=\n  '+lean_list(fk)+'\n\n'
body+='def certificate : List Nat :=\n  ['+',\n   '.join(map(str,words))+']\n\n'
body+='set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem cnfUnsat : ¬ PEqualNP.Library.LRAT.FormulaSat formula := by\n'
body+='  apply PEqualNP.Library.LRAT.checkW_sound formula initialKeys '+str(width)+' certificate\n  decide +kernel\n\nend PEqualNP.Outside.Pilot64KernelControl\n'
out.write_text(body)
record={'scope':'UNSAT of the explicitly listed five-gate path synthesis CNF only; circuit encoding bridge not proved.','cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),'lrat_sha256':hashlib.sha256(stem.with_suffix('.lrat').read_bytes()).hexdigest(),'original_steps':len(steps),'trimmed_steps':len(trim),'needed_initial_clauses':sum(i<=len(clauses) for i in needed),'token_count':len(tokens),'word_width':width,'word_count':len(words),'lean_bytes':len(body.encode()),'lean_sha256':hashlib.sha256(body.encode()).hexdigest()}
(SCRATCH/'lrat-kernel-control-metadata.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
