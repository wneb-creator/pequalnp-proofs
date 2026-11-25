from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import hashlib,json,gzip,re,signal
import sympy as s
base=Path('/workspace/pequalnp-proofs/results/gct231/triangle-qq-trace-r1');root=Path('/tmp/oec/pequalnp-pilot-75/gct231')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
man=base/'sha256.json';assert sha(man)=='ce31e3a5f594cc94dccbdfc1f285c14afac166090abd548681312121bf7e1617'
expected=json.loads(man.read_text());files={p.name:p for p in base.iterdir() if p.is_file() and p!=man};assert len(files)==19 and set(files)==set(expected)
assert sum(p.stat().st_size for p in files.values())+man.stat().st_size==70713
for name,p in files.items():
 assert not p.is_symlink() and sha(p)==expected[name]
 b=p.read_bytes();b.decode('utf8');assert b'\x00' not in b and not b.startswith((b'\x7fELF',b'MZ'))
assert sha(base/'triangle-twelve-equations.json')=='03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7'
assert (base/'triangle-twelve-equations.json').read_bytes()==(root/'triangle_concept/triangle-twelve-equations.json').read_bytes()
qqlines=(base/'triangle-qq.in').read_bytes().splitlines();fflines=(base.parent/'triangle-native-r1/triangle-p1009.in').read_bytes().splitlines()
assert qqlines[1:]==fflines[1:] and qqlines[0].split()==[b'12',b'26',b'0',b'686'] and fflines[0].split()==[b'12',b'26',b'1009',b'686']
d=json.loads((base/'triangle-twelve-equations.json').read_text());variables=s.symbols(d['unknowns']);loc=dict(zip(d['unknowns'],variables));polys=[s.Poly(s.sympify(row['coefficient'],locals=loc),*variables,domain=s.QQ) for row in d['equations']]
prov=json.loads((base/'triangle-qq.provenance.json').read_text());assert prov['source_sha256']==sha(base/'triangle-twelve-equations.json') and prov['input_sha256']==sha(base/'triangle-qq.in')
vals=list(map(int,(base/'triangle-qq.in').read_text().split()));lengths=vals[4:30];pos=30;inputrows=[]
for i,(length,poly) in enumerate(zip(lengths,polys)):
 got={}
 for _ in range(length):
  num,den=vals[pos:pos+2];mon=tuple(vals[pos+2:pos+14]);pos+=14
  assert den>0 and mon not in got and all(v>=0 for v in mon);got[mon]=s.Rational(num,den)
 denominator,integral=poly.clear_denoms();content,primitive=integral.primitive();scale=prov['equation_scalings'][i]
 assert s.Rational(scale['denominator'])/s.Rational(scale['content'])==denominator/content
 assert got==dict(primitive.terms());inputrows.append(got)
assert pos==len(vals)
companion=base/'triangle-qq-run.f4.in';lines=companion.read_text().splitlines();assert lines[0]=='0 12 26' and len(lines)==28
x=s.symbols(lines[1]);xl=dict(zip(lines[1].split(),x))
for line,want in zip(lines[2:],inputrows):assert dict(s.Poly(s.sympify(line.replace('^','**'),locals=xl),*x,domain=s.QQ).terms())==want
print('Exact19-file coverage/hashes/70713bytes/text-only; reviewed source, all26 rational rows, FF header-only delta and replay companion: PASS',flush=True)
pre=json.loads((base/'preflight.json').read_text());run=json.loads((base/'triangle-qq-run.run.json').read_text())
assert pre['source_sha256']==sha(base/'triangle-twelve-equations.json') and pre['input_sha256']==run['input_sha256']==sha(base/'triangle-qq.in')
for name,item in pre['bindings'].items():assert sha(Path(item['path']))==item['sha256'],name
assert sha(base/'run_neogb_trace_primitive.py')==pre['bindings']['runner']['sha256']
assert run['binary_sha256']==pre['bindings']['binary']['sha256'] and run['companion_sha256']==sha(companion)
assert run['status']=='UNKNOWN_OUTPUT_FILE_SIZE_LIMIT' and run['returncode']==-signal.SIGXFSZ==-25
assert (run['seconds_limit'],run['memory_mib_limit'],run['output_file_mib_limit'],run['pairs'])==(600,2048,256,32)
assert run['wall_seconds']==80.5414999129971
elf=(base/'elf-dynamic.log').read_text();assert 'libneogb_trace.so' in elf and 'certificate-trace-primitive' in elf
log=(base/'triangle-qq-run.log').read_text();rows=[line for line in log.splitlines() if re.match(r'^\s*\d+\s+\d+\s+\d+\s+\d+\s+x\s+\d+',line)]
completed=[line for line in rows if re.search(r'\d+\.\d+\s+\|\s+\d+\.\d+\s*$',line)];unfinished=[line for line in rows if line not in completed]
assert len(completed)==30 and len(unfinished)==1 and '2635 x 4476' in completed[-1] and '1807 x 4089' in unfinished[0]
assert 'reduce final basis' not in log
pres=json.loads((base/'trace-preservation.json').read_text());assert pres['completed_rounds_with_timings']==30 and pres['last_completed_round']==completed[-1] and pres['unfinished_round_log']==unfinished[0] and not pres['basis_output_exists']
assert not (base/'triangle-qq-run.basis.json').exists() and not (root/'triangle-qq-trace-r1/triangle-qq-run.basis.json').exists()
print('Reviewed runner/engine bindings, SIGXFSZ output-limit UNKNOWN status,30 timed rounds+unfinished1807x4089, no basis/replay verdict: PASS',flush=True)
def streamhash(stream):
 digest=hashlib.sha256();size=0;newlines=0;last=b''
 for block in iter(lambda:stream.read(1024*1024),b''):
  digest.update(block);size+=len(block);newlines+=block.count(b'\n');last=block[-1:]
 return digest.hexdigest(),size,newlines,last
raw=root/'triangle-qq-trace-r1/triangle-qq-run.trace';gz=root/'triangle-qq-trace-r1/triangle-qq-run.trace.gz'
with raw.open('rb') as f:rh,sz,nl,last=streamhash(f)
assert rh==pres['raw_sha256'] and sz==pres['raw_bytes']==268435456 and nl==pres['raw_newline_count']==269716 and last!=b'\n' and not pres['raw_ends_with_newline']
with gz.open('rb') as f:gh,gs,_,_=streamhash(f)
assert gh==pres['compressed_sha256'] and gs==pres['compressed_bytes']==123750576
with gzip.open(gz,'rb') as f:uh,us,_,_=streamhash(f)
assert uh==rh and us==sz and pres['decompression_sha256_verified']
print('Raw/gzip full hashes and lossless decompression verified by streaming bytes only; truncated final record/no newline confirmed, no algebraic trace parsing/replay: PASS',flush=True)
readme=(base/'README.md').read_text();assert 'UNKNOWN_OUTPUT_FILE_SIZE_LIMIT' in readme and 'no rational or complex contradiction is claimed' in readme and 'remain in scratch' in readme
print('README scope matches interrupted unverified QQ attempt; no finite-field result promoted. No solver rerun.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
