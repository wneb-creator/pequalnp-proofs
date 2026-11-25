import json,time,sympy as s,mpmath as mp
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
d=json.loads((base/'zero-edge-pencil.json').read_text());v=s.symbols(' '.join(d['variables']))
eq=s.Matrix([s.sympify(t) for t in d['equations']]);jac=eq.jacobian(v)
fn=s.lambdify(v,eq,'mpmath',cse=True);jn=s.lambdify(v,jac,'mpmath',cse=True)
seed=json.loads((base/'zero-edge-numeric-strict-roots.json').read_text())[-1]
mp.mp.dps=100
z=[mp.mpc(str(a),str(b)) for a,b in zip(seed['real'],seed['imag'])]
start=time.monotonic()
for step in range(12):
    F=mp.matrix(fn(*z));J=mp.matrix(jn(*z));delta=mp.lu_solve(J,F);z=[z[i]-delta[i] for i in range(12)]
    residual=max(abs(t) for t in fn(*z));print('STEP',step,'RESIDUAL',mp.nstr(residual,12),'CORRECTION',mp.nstr(max(abs(t) for t in delta),12),flush=True)
    if residual<mp.mpf('1e-90'):break
assert residual<mp.mpf('1e-90')
R=mp.inverse(mp.matrix(jn(*z)))
out={'real':[mp.nstr(t.real,92) for t in z],'imag':[mp.nstr(t.imag,92) for t in z],
     'inverse_real':[[mp.nstr(R[i,j].real,75) for j in range(12)] for i in range(12)],
     'inverse_imag':[[mp.nstr(R[i,j].imag,75) for j in range(12)] for i in range(12)],
     'residual':mp.nstr(residual,20),'seconds':time.monotonic()-start}
(base/'zero-edge-high-precision.json').write_text(json.dumps(out,indent=2))
print('HIGH_PRECISION_ONLY_NOT_YET_CERTIFIED','SECONDS',time.monotonic()-start,flush=True)
