from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,signal,subprocess
import sympy as s
base=Path(__file__).resolve().parent;root=base.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
source=base/'triangle-generic-eleven-equations.json';assert sha(source)=='8ded9d5e1145761185086336d90b749165633b5bad27a9c8de1677e32617eb48'
d=json.loads(source.read_text());vs=s.symbols(d['unknowns']);loc=dict(zip(d['unknowns'],vs))
qqlines=(base/'generic-qq.in').read_bytes().splitlines();fflines=(base/'generic-p1009.in').read_bytes().splitlines()
assert qqlines[1:]==fflines[1:] and qqlines[0].split()==[b'11',b'20',b'0',b'1050'] and fflines[0].split()==[b'11',b'20',b'1009',b'1050']
def parse_sparse(path):
 vals=list(map(int,path.read_text().split()));n,m,p,total=vals[:4];lengths=vals[4:4+m];pos=4+m;rows=[];assert sum(lengths)==total
 for count in lengths:
  row={}
  for _ in range(count):
   num,den=vals[pos:pos+2];mon=tuple(vals[pos+2:pos+2+n]);pos+=n+2
   assert den>0 and mon not in row and all(e>=0 for e in mon)
   row[mon]=s.Rational(num,den)
  rows.append(row)
 assert pos==len(vals)
 return (n,m,p,total),rows
_,rows=parse_sparse(base/'generic-qq.in')
prov=json.loads((base/'generic-qq.provenance.json').read_text());assert prov['source_sha256']==sha(source) and prov['input_sha256']==sha(base/'generic-qq.in')
for i,(row,e) in enumerate(zip(rows,d['equations'])):
 poly=s.Poly(s.sympify(e['coefficient'],locals=loc),*vs,domain=s.QQ);den,ip=poly.clear_denoms();content,primitive=ip.primitive()
 assert row==dict(primitive.terms());scale=prov['equation_scalings'][i];assert den/content==s.Rational(scale['denominator'])/s.Rational(scale['content'])
comp=base/'generic-qq-run.f4.in';lines=comp.read_text().splitlines();assert lines[0]=='0 11 20' and len(lines)==22
xs=s.symbols(lines[1]);xl=dict(zip(lines[1].split(),xs))
for line,row in zip(lines[2:],rows):assert dict(s.Poly(s.sympify(line.replace('^','**'),locals=xl),*xs,domain=s.QQ).terms())==row
print('All20 exact QQ rows/scalings, F1009 header-only delta,11variable order/1050terms and replay companion: PASS',flush=True)
f=json.loads((base/'generic-p1009-run.result.json').read_text());basis=json.loads((base/'generic-p1009.basis.json').read_text())
assert f['status']=='COMPLETED' and f['returncode']==0 and f['unit_basis'] and f['basis_size']==1
assert basis=={'characteristic':1009,'nvars':11,'nterms':1,'basis':[[['1',[0]*11]]]}
assert f['output_sha256']==sha(base/'generic-p1009.basis.json') and f['input_sha256']==sha(base/'generic-p1009.in')
assert (f['wall_limit_seconds'],f['memory_mib'],f['output_mib'],f['threads'],f['pairs'])==(120,1024,64,1,32)
assert f['seconds']==2.2348354239984474 and f['child_maxrss_kib']==22652
binary=Path(f['command'][0]);assert sha(binary)==f['binary_sha256'];assert sha(binary.with_name('libneogb_checkpoint.so'))==f['library_sha256']
cp=f['checkpoint'];assert sha(Path(cp['path']))==cp['sha256'];header,cp_rows=parse_sparse(Path(cp['path']));assert header==(11,21,1009,1051)
mod=lambda row:{mon:int(c.p)*pow(int(c.q),-1,1009)%1009 for mon,c in row.items()}
assert list(map(mod,cp_rows[:20]))==list(map(mod,rows)) and cp_rows[-1]=={(0,)*11:s.Integer(1)}
assert cp['metadata']['round']==78 and cp['metadata']['sequence']==2
flog=(base/'generic-p1009-run.log').read_text();pairlog=flog.split('reduce final basis')[0]
pattern=r'^\s*\d+\s+\d+\s+\d+\s+\d+\s+x\s+\d+'
frounds=[line for line in pairlog.splitlines() if re.match(pattern,line)];assert len(frounds)==78
print('F1009 actual basis[1], exit0,2.234835s/22652KiB,78pairrounds, engine hashes and final checkpoint original20rows+unit: PASS',flush=True)
q=json.loads((base/'generic-qq-run.run.json').read_text());assert q['status']=='UNKNOWN_OUTPUT_FILE_SIZE_LIMIT' and q['returncode']==-signal.SIGXFSZ==-25
assert q['input_sha256']==sha(base/'generic-qq.in') and q['companion_sha256']==sha(comp)
assert (q['seconds_limit'],q['memory_mib_limit'],q['output_file_mib_limit'],q['pairs'])==(120,1024,64,32) and q['wall_seconds']==4.798031910999271
qb=root/'sparse-engine/certificate-trace-compact/neogb_cli_trace';assert sha(qb)==q['binary_sha256']=='158c41ae065a43663cb6f60e0f561e818a7d81c238a671ef759d98b38bba7a00'
elf=subprocess.run(['readelf','-d',str(qb)],capture_output=True,text=True,check=True).stdout
assert 'libneogb_trace.so' in elf and 'certificate-trace-compact' in elf
log=(base/'generic-qq-run.log').read_text();qr=[line for line in log.splitlines() if re.match(pattern,line)];done=[line for line in qr if re.search(r'\d+\.\d+\s+\|\s+\d+\.\d+\s*$',line)]
assert len(done)==15 and len(qr)==16 and '1328 x 2094' in qr[-1] and 'reduce final basis' not in log
assert not (base/'generic-qq-run.basis.json').exists()
raw=base/'generic-qq-run.trace';h=hashlib.sha256();size=0;nl=0;last=b''
with raw.open('rb') as stream:
 for chunk in iter(lambda:stream.read(1<<20),b''):h.update(chunk);size+=len(chunk);nl+=chunk.count(b'\n');last=chunk[-1:]
assert size==64*1024**2
print('QQ UNKNOWN_OUTPUT_FILE_SIZE_LIMIT,SIGXFSZ-25,4.798032s;15timedrounds+unfinished1328x2094; no basis/replay. Compact adapter binary/RUNPATH matches metadata: PASS',flush=True)
print('Truncated trace bytes/hash/newlines/ends_newline',size,h.hexdigest(),nl,last==b'\n',flush=True)
u=json.loads((base/'generic-untraced-qq-run.result.json').read_text())
assert u['status']=='UNKNOWN_TIME_LIMIT' and u['returncode'] is None
assert u['seconds']==120.06181987599848 and u['wall_limit_seconds']==120 and u['memory_mib']==1024 and u['child_maxrss_kib']==745384
assert u['input_sha256']==sha(base/'generic-qq.in') and u['binary_sha256']==sha(Path(u['command'][0]))=='644e650682ead6ec3d8c4c7b55dc335fb6bb6d883553c2b7c4dddcc48572d1ca'
assert not (base/'generic-untraced-qq.basis.json').exists()
ul=(base/'generic-untraced-qq-run.log').read_text();assert 'reduce final basis' not in ul
print('Additional completed untraced QQ r1: UNKNOWN_TIME_LIMIT120.061820s/745384KiB at120s/1024MiB; reviewed qqfix binary/input bindings match; no basis: PASS',flush=True)
print('Scope: finite-field unit computation only; both completed QQ attempts remain UNKNOWN. No trace algebra/replay, solver rerun, or characteristic-zero conclusion. Any subsequent r2 run is outside this review.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
