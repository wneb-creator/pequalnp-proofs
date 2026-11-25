from pathlib import Path
import hashlib,json,re
repo=Path(__file__).resolve().parents[2]
basepath=repo/'results/orch/lemmas/TwoAndAssemblyBase.lean'
import tempfile
out=Path(tempfile.mkdtemp(prefix='two-and-replay-', dir='/tmp/oec/pequalnp-pilot-87'))
sha=lambda s:hashlib.sha256(s).hexdigest()
base=basepath.read_bytes();pieces=[base];records=[]
records.append({'kind':'base','source':str(basepath.relative_to(repo)),'bytes':len(base),'sha256':sha(base),'output_start':0,'output_end':len(base)})
for name in ['FreeBankExtraction','TwoZeroInfluence','TwoAndBank','TwoAndBankLower','FreeSegments','TwoAndOrdinary']:
 source=repo/'results/orch/lemmas'/(name+'.lean');raw=source.read_bytes();text=raw.decode()
 if name=='FreeBankExtraction':
  start=text.index('lemma gate_rep_free ')
  content='namespace PEqualNP.Outside.L_meta_2373.Live1024.FreeBank\n\n'+text[start:]
  recipe={'mode':'new helpers only','source_start_character':start,'omitted':'Checked Count/PositiveTail helper copies; resolve original same-file Live1024 private gate_rep/pull_gate'}
 else:
  content=''.join(line for line in text.splitlines(keepends=True) if not line.startswith('import ')).lstrip('\n')
  recipe={'mode':'strip import lines only'}
 body=b'\n'+content.encode();offset=sum(map(len,pieces));pieces.append(body)
 records.append({'kind':'append','source':str(source.relative_to(repo)),'source_bytes':len(raw),'source_sha256':sha(raw),'appended_bytes':len(body),'appended_sha256':sha(body),'output_start':offset,'output_end':offset+len(body),**recipe})
result=b''.join(pieces);text=result.decode();assert len(result)<512*1024
assert '_root_' not in text and '"' not in text and 'native_decide' not in text
assert re.findall(r'^import .*$',text,re.M)==['import PEqualNP.Defs']
assert not re.search(r'^(structure|inductive|class|instance|axiom|opaque)\b',text,re.M)
assert 'NineMonotoneExtension' not in text and 'nine_monotone_reach_lower' not in text
attrs=re.findall(r'@\[([^]]+)\]',text);assert all(a.strip() in ['simp','local simp'] for a in attrs),attrs
(out/'TwoAndCombined.lean').write_bytes(result)
report={'source_bytes':len(result),'source_sha256':sha(result),'base_bytes':len(base),'added_bytes':len(result)-len(base),'pieces':records,'format_scan':{'imports':['PEqualNP.Defs'],'forbidden_substring':False,'quotes':False,'new_datatype_declarations':False,'attributes':sorted(set(attrs))},'scope':'Adds restricted twoNOT helper/circuit lower only; required gap theorem still absent.'}
(out/'assembly-map.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['source_bytes','source_sha256','base_bytes','added_bytes','scope']}))

assert result==(repo/'results/orch/lemmas/TwoAndCombined.lean').read_bytes()
print('Exact archived source replay verified')
