from pathlib import Path
import hashlib,json,re
repo=Path('/workspace/pequalnp-proofs');folder=repo/'results/orch/lemmas'
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((repo/'results/orch/two-and-assembly-map.json').read_text())
base=(folder/'TwoAndAssemblyBase.lean').read_bytes()
assert len(base)==353344 and sha(base)=='8c4c7d99c9079fb7fe118236e2cd7f9f248273a82071a29e349a62ddf81bb85f'
assert base==(repo/'lean/PEqualNP/Outside/L_meta_2373.lean').read_bytes()
parts=[base];records=[]
for name in ['FreeBankExtraction','TwoZeroInfluence','TwoAndBank','TwoAndBankLower','FreeSegments','TwoAndOrdinary']:
 raw=(folder/(name+'.lean')).read_bytes();s=raw.decode()
 if name=='FreeBankExtraction':
  body='namespace PEqualNP.Outside.L_meta_2373.Live1024.FreeBank\n\n'+s[s.index('lemma gate_rep_free '):]
 else:body=''.join(line for line in s.splitlines(True) if not line.startswith('import ')).lstrip('\n')
 b=b'\n'+body.encode();start=sum(map(len,parts));parts.append(b)
 record=manifest['pieces'][len(parts)-1]
 assert record['source_sha256']==sha(raw) and record['source_bytes']==len(raw)
 assert record['appended_sha256']==sha(b) and record['appended_bytes']==len(b)
 assert record['output_start']==start and record['output_end']==start+len(b)
 records.append({'module':name,'source_sha256':sha(raw),'appended_bytes':len(b)})
result=b''.join(parts);archived=(folder/'TwoAndCombined.lean').read_bytes();assert result==archived
assert sha(result)=='c74bd69129237388a77bda176728dad78f13ff3a502f3f98c66075dbc5b8caec'
text=result.decode();assert len(result)==376638<512*1024
assert re.findall(r'^import .*$',text,re.M)==['import PEqualNP.Defs']
for token in ['_root_','"','sorry','native_decide','bv_decide','NineMonotoneExtension','nine_monotone_reach_lower']:assert token not in text,token
assert not re.search(r'(?m)^\s*(?:private\s+|protected\s+)?(?:axiom|opaque|unsafe|structure|inductive|class|instance|macro|syntax|elab|initialize|notation)\b',text)
assert not re.search(r'(?m)^\s*#',text)
assert set(re.findall(r'set_option\s+(\S+)',text))<={'maxRecDepth','maxHeartbeats','maxRecDepth','synthInstance.maxHeartbeats','maxSynthPendingDepth'}
assert all(x.strip() in ('simp','local simp') for x in re.findall(r'@\[([^]]+)\]',text))
free=(folder/'FreeBankExtraction.lean').read_text();ten=base.decode().split('namespace PEqualNP.Outside.L_meta_2373.Live1024\n',1)[1]
for name,nextname in [('gate_rep','pull_gate'),('pull_gate','extract')]:
 chunk=lambda s:s[s.index('private lemma '+name+' '):s.index('private lemma '+nextname+' ')]
 assert chunk(free)==chunk(ten)
log=(folder/'TwoAndCombined.compile.txt').read_text();assert log.endswith('\nCompiler exit code: 0\n')
assert not re.search(r'\.lean:\d+:\d+: error:',log)
report={'status':'PASS','source_sha256':sha(result),'source_bytes':len(result),'lines':len(text.splitlines()),'base_unchanged_from_active_target':True,'ingredients':records,'reused_private_helpers_byte_identical':['Live1024.gate_rep','Live1024.pull_gate'],'warnings':len(re.findall(r'\.lean:\d+:\d+: warning:',log)),'compiler_exit_code':0,'archive_log_sha256':sha(log.encode()),'raw_log_sha256':sha(log[:-len('\nCompiler exit code: 0\n')].encode()),'sole_import':'PEqualNP.Defs','new_datatypes_or_forbidden_constructs':False,'scope':'Restricted two-NOT partial; posted full gap theorem absent.'}
Path('/tmp/oec/pequalnp-pilot-87/audit-two-and-assembly.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
