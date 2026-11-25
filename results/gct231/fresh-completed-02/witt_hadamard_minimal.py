from pathlib import Path
exec(Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh/witt_hadamard.py').read_text().split('eq=[]')[0])
eq=[]
def add_group(degree,exp,terms):
 den=s.ilcm(*[int(c.denominator) for _,c in terms])
 ints=[(m,int(c*den)) for m,c in terms]
 gg=s.igcd(*[c for _,c in ints]);ints=[(m,c//gg) for m,c in ints]
 eq.append({'degree':degree,'monomial':exp,'terms':[[str(c),list(m)] for m,c in sorted(ints,reverse=True)]})
pp=rr.zero
for p in itertools.permutations(range(4)):
 for selected in itertools.combinations(range(4),3):
  term=rr.one
  for i in selected:term*=TT[i][p[i]]
  pp+=term
groups={}
for mon,coeff in pp.items():groups.setdefault(tuple(mon[-3:]),[]).append((tuple(mon[:12]),coeff))
for exp,terms in sorted(groups.items(),reverse=True):add_group(3,exp,terms)
print('cubic exported',len(eq),flush=True)
small,*pgens=ring(','.join([str(a) for a in params]),QQ)
for column in range(3):
 MM=[[small.from_expr(s.expand(T[i,j]).coeff(X[column])) for j in range(4)] for i in range(4)]
 out=small.zero
 for p in itertools.permutations(range(4)):
  term=small.one
  for i in range(4):term*=MM[i][p[i]]
  out+=term
 exp=tuple(4 if i==column else 0 for i in range(3))
 add_group(4,exp,list(out.items()))
 print('pure quartic',column,'terms',len(out),flush=True)
result={'parameters':[str(p) for p in params],'equations':eq,'scope':'necessary equations only: all10 cubic,3 pure quartic coefficients','chart':'E-coordinate block invertible; normalized to I3','frame':dump}
(base/'witt-hadamard-minimal-equations.json').write_text(json.dumps(result,indent=2))
print('DONE',len(eq),flush=True)
