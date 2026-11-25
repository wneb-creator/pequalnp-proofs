from pathlib import Path
import sympy as s,json,hashlib,time
b=Path('/tmp/oec/pequalnp-pilot-78');folder=b/'geometry_search/tracezero_rankdrop';old=json.loads((folder/'matrix.json').read_text());newpath=folder/'shifted-matrix.json';new=json.loads(newpath.read_text());flat=json.loads((b/'construct_search/tracezero-hadamard.json').read_text());v=s.symbols(' '.join(new['variables']));p=v[:6];k,l=v[10:];sub={p[0]:p[0]+3,p[3]:p[3]+3,p[4]:p[4]+3*k,p[5]:p[5]+3*l};inv={p[0]:p[0]-3,p[3]:p[3]-3,p[4]:p[4]-3*k,p[5]:p[5]-3*l};start=time.monotonic()
for oldg,newg in zip(flat['equations'],new['flat_generators']):
 f=s.sympify(oldg.replace('^','**'));g=s.sympify(newg);assert s.expand(f.subs(sub,simultaneous=True)-g)==0;assert s.expand(g.subs(inv,simultaneous=True)-f)==0
for row,nrow in zip(old['matrix'],new['matrix']):
 oldrow=[s.sympify(x) for x in row];shift=[s.expand(x.subs(sub,simultaneous=True)) for x in oldrow];shift[6]=s.expand(shift[6]+3*shift[2]);assert all(s.expand(x-s.sympify(y))==0 for x,y in zip(shift,nrow));back=[s.expand(s.sympify(y).subs(inv,simultaneous=True)) for y in nrow];back[6]=s.expand(back[6]-3*back[2]);assert all(s.expand(x-y)==0 for x,y in zip(back,oldrow))
r={'verdict':'PASS independent forward/inverse symbolic substitution','flat_generators':12,'matrix_entries':63,'source_sha256':hashlib.sha256(newpath.read_bytes()).hexdigest(),'seconds':time.monotonic()-start};(b/'construct_search/rankdrop-shift-audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
