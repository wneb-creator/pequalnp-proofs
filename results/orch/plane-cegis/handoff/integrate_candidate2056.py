import argparse,hashlib,json,re
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument('--input',required=True)
ap.add_argument('--output',required=True)
ap.add_argument('--statement',required=True)
ap.add_argument('--control64',action='store_true')
a=ap.parse_args()
repo=Path('/workspace/pequalnp-proofs')
template=repo/'results/orch/lemmas/PackedChunks2056.lean'
named=repo/'lean/PEqualNP/Outside/L_meta_2056.lean'
given_output=Path(a.output)
assert not given_output.is_symlink()
output=given_output.resolve()
assert output.is_relative_to(repo) or output.is_relative_to(Path('/tmp/oec/pequalnp-pilot-121'))
raw=template.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='19c0e60b53f255ed800c96b51539473d84a44c65da699e1838c61542a85fd38d'
source=raw.decode()
record=json.loads(Path(a.input).read_text())
if isinstance(record,dict):
 gates=record['gates']
 if 'n' in record:assert record['n']==26
 if 'size' in record:assert type(record['size'])is int and record['size']==len(gates)
 out=record.get('output',26+len(gates)-1)
else:gates=record;out=26+len(gates)-1
assert isinstance(gates,list) and gates and type(out)is int and 0<=out<26+len(gates)
for j,gate in enumerate(gates):
 assert isinstance(gate,list) and len(gate)==3 and all(type(x)is int for x in gate)
 op,u,v=gate;assert op in (0,1) and 0<=u<26+j and 0<=v<26+j
if a.control64:
 assert len(gates)==64 and output!=named
else:assert len(gates)<=63
edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
neighbors=[sum(1<<l for l in range(13) if (p,13+l) in edges) for p in range(13)]
negative=set()
for points in range(8192):
 lines=8191
 for p in range(13):
  if points&(1<<p):lines&=~neighbors[p]
 if points==sum(1<<p for p in range(13) if not neighbors[p]&lines):negative.add(points|(lines<<13))
positive={(1<<p)|(1<<l) for p,l in edges}
assert len(positive)==52 and len(negative)==704 and not positive&negative
for row in positive|negative:
 values=[bool(row&(1<<p)) for p in range(26)]
 for op,u,v in gates:values.append(values[u] or values[v] if op else values[u] and values[v])
 assert values[out]==(row in positive),('candidate fails full boundary',row)
statement=Path(a.statement).read_text().strip()
marker='    (reverseNegative : ∀ b : Fin 16, packedEval C (reversedChunk incident b) = 0) :\n'
statement_from_template=source[source.index(marker,source.index('lemma exact_statement_of_checks'))+len(marker):].split(' := by\n',1)[0]
assert statement==statement_from_template
begin=source.index('def control : Circuit :=\n')
end=source.index('\nlemma control_size : control.size = 64 := rfl\n',begin)
literals=['⟨.'+('or' if op else 'and')+',['+str(u)+','+str(v)+']⟩' for op,u,v in gates]
literal='def control : Circuit :=\n  ⟨['+',\n    '.join(literals)+'],'+str(out)+'⟩\n'
source=source[:begin]+literal+source[end:]
source=source.replace('lemma control_size : control.size = 64 := rfl','lemma control_size : control.size = '+str(len(gates))+' := rfl')
namespace='PEqualNP.Outside.L_meta_2056_aux.PackedChunks'
if a.control64:
 source=source.replace(namespace,'PEqualNP.Outside.L_meta_2056_aux.PackedHandoffControl')
 scope='CONTROL ONLY: explicit64-gate circuit; no posted<=63 theorem is declared'
else:
 source=re.sub(r'\bcontrol(?=\b|_)','candidate',source)
 source+='\ntheorem PEqualNP.Outside.L_meta_2056 :\n'+statement+' := by\n'
 source+='  exact '+namespace+'.exact_statement_of_checks\n'
 source+='    '+namespace+'.candidate '+namespace+'.candidate_mono\n'
 source+='    (by rw ['+namespace+'.candidate_size]; decide)\n'
 source+='    '+namespace+'.candidate_positive\n'
 source+='    '+namespace+'.candidate_negative_chunks\n'
 source+='    '+namespace+'.candidate_reverse_chunks\n'
 scope='CANDIDATE ONLY: external boundary checks passed; Lean build and local checker still required'
prefix='control' if a.control64 else 'candidate'
assert len(re.findall(r'^lemma '+prefix+r'_negative_[0-9]+ :',source,re.M))==16
assert len(re.findall(r'^lemma '+prefix+r'_reverse_[0-9]+ :',source,re.M))==16
assert source.startswith('import PEqualNP.Defs\n') and source.count('import ')==1
assert all(x not in source for x in ['_root_','"','sorry','native_decide','axiom '])
assert len(source.encode())<=512*1024
output.parent.mkdir(parents=True,exist_ok=True)
output.write_text(source)
report={'scope':scope,'input_sha256':hashlib.sha256(Path(a.input).read_bytes()).hexdigest(),'template_sha256':hashlib.sha256(raw).hexdigest(),'output':str(output),'output_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),'size':len(gates),'circuit_output':out,'boundary_rows_checked':756,'negative_kernel_certificates':32,'chunk_width':512,'lines':len(source.splitlines()),'named_file_written':output==named}
report_path=Path('/tmp/oec/pequalnp-pilot-121/gate-elimination')/(output.stem+'.handoff.json')
report_path.parent.mkdir(parents=True,exist_ok=True)
report_path.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
