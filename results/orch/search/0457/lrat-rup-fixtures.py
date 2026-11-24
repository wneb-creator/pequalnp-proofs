from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path('/tmp/oec/pequalnp-pilot-21/search/lrat-rup-fixtures')
CHECK=ROOT.parent/'lrat-rup-replay.py'
assert hashlib.sha256(CHECK.read_bytes()).hexdigest()=='0f1aba1fe39efaed530fcbff6c0ef71ba0ba9a7ec8e5097c8ba7b26f63c10ab6'
ROOT.mkdir(exist_ok=False)
def number(n):
 u=2*abs(n)+(n<0); result=bytearray()
 while u>=128: result.append((u&127)|128);u>>=7
 result.append(u);return bytes(result)
def seq(xs):return b''.join(number(x) for x in xs)+number(0)
def add(i,c,h):return b'a'+number(i)+seq(c)+seq(h)
def delete(xs):return b'd'+seq(xs)
base='p cnf 1 2\n1 0\n-1 0\n'
cases=[
 ('valid_direct',base,add(3,[],[1,2]),True),
 ('valid_chain',base,add(3,[1],[1])+add(4,[],[3,2]),True),
 ('valid_duplicate_unit','p cnf 1 2\n1 1 0\n-1 0\n',add(3,[],[1,2]),True),
 ('deleted_hint',base,delete([1])+add(3,[],[1,2]),False),
 ('future_hint',base,add(3,[],[4,2]),False),
 ('missing_empty',base,add(3,[1],[1]),False),
 ('nonunit_hint','p cnf 2 2\n1 2 0\n-1 -2 0\n',add(3,[],[1,2]),False),
 ('needed_rat',base,add(3,[],[-1,2]),False),
 ('corrupt_final',base,add(3,[],[1]),False),
 ('truncated_integer',base,b'a'+bytes([128]),False),
]
results=[]
for name,cnf,proof,wanted in cases:
 d=ROOT/name;d.mkdir();(d/'input.cnf').write_text(cnf);(d/'input.lrat').write_bytes(proof)
 with (d/'checker.log').open('wb') as log:
  p=subprocess.run([sys.executable,str(CHECK),'--cnf',str(d/'input.cnf'),'--proof',str(d/'input.lrat'),'--outdir',str(d/'checked'),'--max-address-space-mib','128'],stdout=log,stderr=subprocess.STDOUT,timeout=10)
 actual=p.returncode==0
 assert actual==wanted,(name,p.returncode)
 assert (d/'checked/result.json').exists()==wanted
 results.append({'fixture':name,'expected_success':wanted,'exit_code':p.returncode})
 print(name,'PASS',flush=True)
(ROOT/'fixtures.json').write_text(json.dumps(results,indent=2)+'\n')
print('ALL10FIXTURESPASSED',flush=True)
