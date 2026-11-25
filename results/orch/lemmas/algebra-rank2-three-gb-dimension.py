from pathlib import Path
import sympy as s,itertools,time
lines=Path('/tmp/oec/pequalnp-pilot-79/extend-rank2-three.log').read_text().splitlines();i=next(i for i,l in enumerate(lines) if l.startswith('GB '));ws=s.symbols('w:6');start=time.time()
ps=[s.Poly(s.sympify(line),*ws) for line in lines[i+1:]]
lms=[p.LM(order='grevlex').exponents for p in ps]
supports=[set(i for i,e in enumerate(m) if e) for m in lms]
free=[ss for k in range(7) for ss in itertools.combinations(range(6),k) if not any(sup<=set(ss) for sup in supports)]
print('GB size',len(ps),'affine Krull dimension',max(map(len,free)),'maximal free sets',[ss for ss in free if len(ss)==max(map(len,free))],'seconds',time.time()-start)
print('LMs',lms)
