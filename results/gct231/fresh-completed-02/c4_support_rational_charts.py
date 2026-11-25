"""Eight rational six-parameter charts for isotropic C4-support3-planes."""
import sympy as s,itertools,json,time,sys,multiprocessing as mp
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
data=json.loads((base/'c4-support-homogeneous.json').read_text())
vs=list(s.symbols('v:7'));Hs={k:s.sympify(data['homogeneous'][str(k)]) for k in [2,3,4]};G=s.hessian(Hs[2],vs)/2
u,v,o1,o2,o3,b1,b3=s.symbols('u v o1 o2 o3 b1 b3');coords=[u,v,o1,o2,o3,b1,b3]
HH=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
SS=s.Matrix([[0,b1,o2,b3],[b1,(u+v)/2,o3,o2],[o2,o3,u,o1],[b3,o2,o1,(u-v)/2]])
TT=HH*SS*HH
assert s.expand(TT[0,2])==0 and s.expand(TT[1,3])==0
vec=s.Matrix([TT[0,0],TT[1,1],TT[2,2],TT[0,1],TT[1,2],TT[2,3],TT[0,3]])
P=vec.jacobian(coords)
qdiag=s.diag(s.Rational(3,2),s.Rational(1,2),2,-4,2,-6,-6)
assert P.T*G*P==qdiag and P.det()!=0
ee=s.Matrix.hstack(s.Matrix([2,0,0,0,0,1,0]),s.Matrix([0,0,1,1,1,0,0]),s.Matrix([0,2,1,0,-1,0,1]))
ff=s.Matrix.hstack(s.Matrix([2,0,0,0,0,-1,0])/12,s.Matrix([0,0,1,-1,1,0,0])/8,s.Matrix([0,2,1,0,-1,0,-1])/12)
zz=s.Matrix([0,4,-1,0,1,0,0])
E=P*ee;F=P*ff;Z=P*zz;dd=s.Integer(12)
assert E.T*G*E==s.zeros(3) and F.T*G*F==s.zeros(3) and E.T*G*F==s.eye(3)
assert Z.T*G*E==s.zeros(1,3) and Z.T*G*F==s.zeros(1,3) and (Z.T*G*Z)[0]==dd
assert s.Matrix.hstack(E,F,Z).det()!=0
print('RATIONAL_FRAME_VERIFIED E',E,'F',F,'Z',Z,'residual',dd,flush=True)
worker_source=(base/'c4_support_charts.py').read_text().split('def worker(chart,queue):')[1].split("if __name__=='__main__':")[0]
worker_source='def worker(chart,queue):'+worker_source
worker_source=worker_source.replace('c4-support-chart-','c4-support-rational-chart-')
exec(worker_source)
if __name__=='__main__':
 charts=list(map(int,sys.argv[1:])) if len(sys.argv)>1 else list(range(8))
 for chart in charts:
  queue=mp.Queue();p=mp.Process(target=worker,args=(chart,queue));p.start();p.join(120)
  if p.is_alive():p.terminate();p.join();print({'chart':chart,'status':'UNKNOWN_TIME_LIMIT'},flush=True)
  elif p.exitcode:print({'chart':chart,'status':'ERROR','exit':p.exitcode},flush=True)
  else:print(queue.get(),flush=True)
