from pathlib import Path
from fractions import Fraction
import argparse, hashlib, json, math, re, resource, time, zlib, gzip, shutil
BASE=Path('/tmp/oec/pequalnp-pilot-78/construct_search')
OUT=BASE/'net_normal_form'
NAMES=['x0','x1','x2','x4','x6','x8','x3','x5','x7','x9','zz']
INDEX={n:i for i,n in enumerate(NAMES)}
MARKERS={'FP_MODULUS','FP_INDEX','FP_POLYNOMIAL','FP_VECTOR_END'}
MAX_TEXT=32*2**20
MAX_TERMS=250000

def decode_monomial(m):return [(m>>(8*i))&255 for i in range(11)]
def encode_monomial(m):
 assert len(m)==11 and all(isinstance(e,int) and 0<=e<128 for e in m)
 return sum(e<<(8*i) for i,e in enumerate(m))
def parse_poly(text,modulus):
 text=re.sub(r'\s+','',text)
 if text=='0':return {}
 assert text and len(text)<=MAX_TEXT
 result={}
 terms=re.findall(r'[+-]?[^+-]+',text)
 assert ''.join(terms)==text,'Malformed polynomial punctuation'
 for term in terms:
  sign=-1 if term[0]=='-' else 1
  if term[0] in '+-':term=term[1:]
  value=Fraction(sign);exps=[0]*11
  for factor in term.split('*'):
   m=re.fullmatch(r'(x[0-9]|zz)(?:\^(\d+))?',factor)
   if m:exps[INDEX[m[1]]]+=int(m[2] or 1)
   else:
    assert re.fullmatch(r'\d+(?:/\d+)?',factor),('Unexpected polynomial token',factor[:100])
    value*=Fraction(factor)
  key=encode_monomial(exps)
  if modulus:value=int(value.numerator)*pow(int(value.denominator),-1,modulus)%modulus
  result[key]=(result.get(key,0)+value)%(modulus or 1) if modulus else result.get(key,Fraction(0))+value
  if not result[key]:del result[key]
  assert len(result)<=MAX_TERMS
 return result

def original_generators():
 data=json.loads((BASE/'rank1-certificate-conventions.json').read_text());assert data['variable_order']==NAMES
 return [{encode_monomial(m):Fraction(v) for v,m in g['terms']} for g in data['generators']]

def verify(vector,gens,p):
 residual={0:(p-1 if p else Fraction(-1))}
 for a,b in zip(vector,gens):
  for ma,va in a.items():
   for mb,vb in b.items():
    mon=ma+mb
    value=va*(int(vb.numerator)*pow(int(vb.denominator),-1,p)%p if p else vb)
    value=(residual.get(mon,0)+value)%p if p else residual.get(mon,Fraction(0))+value
    if value:residual[mon]=value
    elif mon in residual:del residual[mon]
 return not residual,len(residual)

def gzip_lines(path,limit=None):
 dec=zlib.decompressobj(31);pending=b'';offset=0
 if limit is None:limit=path.stat().st_size
 with path.open('rb') as f:
  while True:
   chunk=f.read(min(65536,limit))
   limit-=len(chunk)
   if not chunk:break
   while chunk:
    data=dec.decompress(chunk,65536);chunk=dec.unconsumed_tail
    pending+=data
    assert len(pending)<=MAX_TEXT,'A single log line exceeded bounded parser limit'
    while b'\n' in pending:
     line,pending=pending.split(b'\n',1)
     start=offset;offset+=len(line)+1
     yield start,offset,line.decode('ascii').strip(),line+b'\n'
 # An unfinished trailing line is intentionally ignored, even on active gzip.

def complete_blocks(path,limit=None):
 block=None;expect=None;index=None;parts=[];size=0
 def finish():
  nonlocal parts,size
  if parts:
   assert block is not None and index is not None
   assert index not in block['polys'],'Duplicate cofactor index'
   block['polys'][index]=parse_poly(''.join(parts),block['modulus']);parts=[];size=0
 for start,end,line,raw in gzip_lines(path,limit):
  if block is not None:block['raw_hash'].update(raw)
  if line in MARKERS:
   finish()
   if line=='FP_MODULUS':block={'polys':{},'raw_start':start,'raw_hash':hashlib.sha256(raw)};expect='modulus';index=None
   elif line=='FP_INDEX':assert block is not None;expect='index';index=None
   elif line=='FP_POLYNOMIAL':assert block is not None and index is not None;expect='polynomial'
   else:
    assert block is not None and set(block['polys'])==set(range(1,14))
    vector=[block['polys'][i] for i in range(1,14)];assert not vector[7]
    yield block['modulus'],vector,{'uncompressed_start':block['raw_start'],'uncompressed_end_exclusive':end,'sha256':block['raw_hash'].hexdigest()}
    block=None;expect=None;index=None
  elif block is not None:
   if expect=='modulus':assert re.fullmatch(r'\d+',line);block['modulus']=int(line);expect=None
   elif expect=='index':assert re.fullmatch(r'\d+',line);index=int(line);expect=None
   elif expect=='polynomial':
    parts.append(line);size+=len(line);assert size<=MAX_TEXT
   elif line:raise ValueError('Unexpected text inside modular vector: '+line[:100])

def rational_reconstruct(a,m):
 if a==0:return Fraction(0)
 bound=math.isqrt(m//2);r0,r1=m,a;t0,t1=0,1
 while abs(r1)>bound:
  q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
 if t1<0:r1,t1=-r1,-t1
 if not (0<t1<=bound and math.gcd(r1,t1)==1 and (r1-a*t1)%m==0):return None
 return Fraction(r1,t1)

def rational_vector(vector,m):
 result=[]
 for poly in vector:
  q={}
  for mon,c in poly.items():
   value=rational_reconstruct(c,m)
   if value is None:return None
   if value:q[mon]=value
  result.append(q)
 return result

def combine(a,m,b,p):
 assert math.gcd(m,p)==1;mi=pow(m,-1,p);result=[]
 for x,y in zip(a,b):
  poly={}
  for mon in x.keys()|y.keys():
   old=x.get(mon,0);v=old+m*((y.get(mon,0)-old)*mi%p)
   if v:poly[mon]=v
  result.append(poly)
 return result,m*p

def export_vector(vector,modulus,label,budget):
 target=OUT/(label+'.json.gz');tmp=OUT/(label+'.json.gz.tmp')
 budget=min(budget,max(0,shutil.disk_usage(OUT).free-16*2**20))
 if budget==0:return {'exported':False,'reason':'retain at least16MiB filesystem reserve'}
 class BudgetExceeded(Exception):pass
 class LimitedWriter:
  def __init__(self,f):self.f=f;self.n=0
  def write(self,data):
   if self.n+len(data)>budget:raise BudgetExceeded()
   n=self.f.write(data);self.n+=n;return n
  def flush(self):self.f.flush()
 try:
  with tmp.open('wb') as raw:
   limited=LimitedWriter(raw)
   with gzip.GzipFile(fileobj=limited,mode='wb',compresslevel=6,mtime=0) as out:
    def write(text):out.write(text.encode('ascii'))
    write('{"variable_order":'+json.dumps(NAMES,separators=(',',':'))+',"cofactors":[')
    for i,poly in enumerate(vector):
     if i:write(',')
     write('{"terms":[')
     for j,(k,v) in enumerate(sorted(poly.items())):
      if j:write(',')
      write(json.dumps([str(v),decode_monomial(k)],separators=(',',':')))
     write(']}')
    write(']')
    if modulus:write(',"modulus":'+str(modulus)+',"scope":"Verified finite-field unit identity only; not a QQ certificate."')
    else:write(',"scope":"Independently verified exact QQ unit identity."')
    write('}\n')
  size=tmp.stat().st_size;tmp.replace(target)
  return {'exported':True,'path':str(target),'bytes':size,'sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
 except BudgetExceeded:return {'exported':False,'reason':'compressed disk budget exceeded'}
 finally:
  if tmp.exists():tmp.unlink()

def scan(path,output_budget):
 gens=original_generators();reports=[];aggregate=None;modulus=1;used=set();remaining=output_budget;start=time.monotonic()
 snapshot_bytes=path.stat().st_size;digest=hashlib.sha256()
 with path.open('rb') as inp:
  left=snapshot_bytes
  while left:
   data=inp.read(min(65536,left));assert data;digest.update(data);left-=len(data)
 snapshot={'compressed_prefix_bytes':snapshot_bytes,'compressed_prefix_sha256':digest.hexdigest()}
 for p,vector,raw_block in complete_blocks(path,snapshot_bytes):
  assert p>2 and p not in used;used.add(p)
  ok,n=verify(vector,gens,p);assert ok,('Modular identity failed',p,n)
  item={'modulus':p,'status':'exact modular identity PASS','cofactor_terms':[len(g) for g in vector],'raw_block':raw_block}
  artifact=export_vector(vector,p,'rank1-modular-vector-'+str(p),remaining);item['artifact']=artifact
  if artifact['exported']:remaining-=artifact['bytes']
  if aggregate is None:aggregate=vector;modulus=p
  else:aggregate,modulus=combine(aggregate,modulus,vector,p)
  candidate=rational_vector(aggregate,modulus)
  if candidate is None:item['rational_reconstruction']='at least one coefficient has no bounded reconstruction'
  else:
   exact,n=verify(candidate,gens,None);item['rational_reconstruction']='exact QQ identity PASS' if exact else 'coefficient reconstruction failed exact QQ identity';item['QQ_residual_terms']=n
   if exact:
    item['QQ_artifact']=export_vector(candidate,None,'rank1-exact-unit-certificate',remaining)
    print('EXACT_QQ_UNIT_IDENTITY_VERIFIED',flush=True)
  reports.append(item)
  (OUT/'modular-vector-audit-report.json').write_text(json.dumps({'scope':'Only complete FP blocks processed; modular evidence is explicitly distinguished from exact QQ identities.','source':str(path),'snapshot':snapshot,'complete_blocks':len(reports),'reports':reports,'seconds':time.monotonic()-start},indent=2)+'\n')
  print(json.dumps(item),flush=True)
 if not reports:
  (OUT/'modular-vector-audit-report.json').write_text(json.dumps({'scope':'No complete FP block yet; active/incomplete blocks ignored.','source':str(path),'snapshot':snapshot,'complete_blocks':0,'seconds':time.monotonic()-start},indent=2)+'\n')
 print('COMPLETE_BLOCKS',len(reports),flush=True)

def selftest():
 assert parse_poly('-2*x0^2*x3+7/3*zz-4',101)=={encode_monomial([2,0,0,0,0,0,1,0,0,0,0]):99,1<<(8*10):7*pow(3,-1,101)%101,0:97}
 assert parse_poly('2*x0-2*x0',101)=={}
 for p in [101,1009,1000000007]:
  for a,b in [(1,2),(-3,4),(0,1),(3,1)]:
   assert rational_reconstruct(a*pow(b,-1,p)%p,p)==Fraction(a,b)
 assert combine([{0:2}],7,[{0:4}],11)==([{0:37}],77)
 assert verify([{0:1}], [{0:Fraction(1)}],101)==(True,0)
 assert verify([{0:Fraction(1,2)}],[{0:Fraction(2)}],None)==(True,0)
 # A complete block survives a missing gzip trailer; a following partial block is ignored.
 fixture=OUT/'modular-vector-parser-fixture.gz'
 text='FP_MODULUS\n101\n'
 for i in range(1,14):text+='FP_INDEX\n'+str(i)+'\nFP_POLYNOMIAL\n'+('1' if i==1 else '0')+'\n'
 text+='FP_VECTOR_END\nFP_MODULUS\n103\nFP_INDEX\n1\nFP_POLYNOMIAL\n'
 fixture.write_bytes(gzip.compress(text.encode())[:-8])
 blocks=list(complete_blocks(fixture));assert len(blocks)==1 and blocks[0][0]==101 and blocks[0][1][0]=={0:1};fixture.unlink()
 assert not export_vector([{0:1}]*13,101,'modular-vector-budget-fixture',1)['exported']
 print('SELFTEST PASS')

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--selftest',action='store_true');parser.add_argument('--scan',type=Path);parser.add_argument('--output-budget-mib',type=int,default=8);a=parser.parse_args()
 resource.setrlimit(resource.RLIMIT_AS,(384*2**20,384*2**20));resource.setrlimit(resource.RLIMIT_CPU,(90,95));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 if a.selftest:selftest()
 if a.scan:scan(a.scan,a.output_budget_mib*2**20)
