import sympy as s,json,time
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'geometry_search/tracezero_rankdrop';start=time.monotonic()
data=json.loads((base/'construct_search/tracezero-hadamard.json').read_text());m=json.loads((job/'matrix.json').read_text())
vs=s.symbols(' '.join(data['variables']));loc=dict(zip(data['variables'],vs));p0,p1,p2,p3,p4,p5,b0,b1,b2,b3,k,l=vs
forward={p0:p0+3,p3:p3+3,p4:p4+3*k,p5:p5+3*l};inverse={p0:p0-3,p3:p3-3,p4:p4-3*k,p5:p5-3*l}
parse=lambda x:s.sympify(x.replace('^','**'),locals=loc)
polys=[parse(x) for x in data['equations']]
shifted=[s.expand(f.subs(forward,simultaneous=True)) for f in polys]
for f,g in zip(polys,shifted):assert s.expand(g.subs(inverse,simultaneous=True)-f)==0
M=[[parse(x) for x in row] for row in m['matrix']]
N=[[s.expand(x.subs(forward,simultaneous=True)) for x in row] for row in M]
for row in N:row[6]=s.expand(row[6]+3*row[2])
for old,row in zip(M,N):
 restored=list(row);restored[6]=s.expand(restored[6]-3*restored[2]);assert all(s.expand(x.subs(inverse,simultaneous=True)-y)==0 for x,y in zip(restored,old))
fmt=lambda x:str(x).replace('**','^')
incidence=['+'.join('('+fmt(row[i])+')*w'+str(i) for i in range(6))+'+('+fmt(row[6])+')' for row in N]
variables=data['variables']+['w'+str(i) for i in range(6)]
script='ring r=0,('+','.join(variables)+'),dp;\noption(redSB);\noption(prot);\nideal I='+','.join(list(map(fmt,shifted))+incidence)+';\nideal G=std(I);\nprint("SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");G;quit;\n'
(job/'rank3-incidence-shifted-Q.sing').write_text(script)
terms=lambda f:len(s.Poly(f,*vs).terms())
report={'status':'PASS','variables':data['variables'],'base_coordinate_change':'Old P=New R+3D; variable identifiers p0..p5 now denote R coefficients. Inverse verified exactly.','extension_coordinate_change':'Old P_W2=New R_W2+3D_W2; D_W2 normalized1. Other extension P slots unchanged.','old_flat_terms':[terms(f) for f in polys],'new_flat_terms':[terms(f) for f in shifted],'old_matrix_terms':sum(terms(x) if x else 0 for row in M for x in row),'new_matrix_terms':sum(terms(x) if x else 0 for row in N for x in row),'matrix':[[str(x) for x in row] for row in N],'flat_generators':list(map(str,shifted)),'seconds':time.monotonic()-start}
(job/'shifted-matrix.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('matrix','flat_generators')},indent=2))
