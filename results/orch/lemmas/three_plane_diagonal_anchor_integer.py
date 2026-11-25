from pathlib import Path
import json,sympy as s,time,resource,hashlib
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(15,15));job=Path('/tmp/oec/pequalnp-pilot-79');source=job/'three-plane-diagonal-anchor-exact.json';source_sha=hashlib.sha256(source.read_bytes()).hexdigest();d=json.loads(source.read_text());assert hashlib.sha256(source.read_bytes()).hexdigest()==source_sha;M=s.Matrix([[s.Rational(n,q) for n,q in row] for row in d['moment35']]);start=time.monotonic();denominators=[];rows=[]
for row in M.tolist():
 den=s.ilcm(*[x.q for x in row]);denominators.append(int(den));rows.append([int(den*x) for x in row])
A=s.polys.matrices.DomainMatrix.from_list_sympy(35,35,rows).convert_to(s.ZZ);det=int(A.det());assert det!=0
assert hashlib.sha256(source.read_bytes()).hexdigest()==source_sha
out={'classification':'Exact nonzero integer determinant after row-denominator clearing; not Lean checked','exact_input_sha256':source_sha,'row_denominators':denominators,'integer_matrix':rows,'integer_determinant':det,'determinant_bits':abs(det).bit_length(),'mod461':det%461,'seconds':time.monotonic()-start};(job/'three-plane-diagonal-anchor-integer-moment.json').write_text(json.dumps(out,separators=(',',':'))+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['row_denominators','integer_matrix','integer_determinant']}))
