import json,time
from pathlib import Path
import sympy as S
b=Path(__file__).parent;d=json.loads((b/"c4_opposite_recentered.json").read_text())
e,f,h,R,T,U,V=S.symbols("e f h R T U V");a,c,H,X,Y=S.symbols("a b H X Y")
sub={h:H/2,U:(a+c)/2,V:(c-a)/2,R:X/2+(a+c)/4,T:Y/2-(c-a)/4}
Q=S.expand(4*S.sympify(d["2"]).subs(sub,simultaneous=True));C=S.expand(16*S.sympify(d["3"]).subs(sub,simultaneous=True))
q=6*e**2+2*f**2+a**2+c**2-H**2-X**2-Y**2-X*(a+c)+Y*(c-a)
cubic=2*f*a*c-2*H*X*Y+e*(-4*X**2-4*Y**2+4*(a+c)*X+4*(a-c)*Y-a**2-c**2+4*f**2)-4*e**3
assert S.expand(Q-q)==0
assert S.expand(C-cubic)==0
result={"variables":["e","f","a","b","H","X","Y"],"Q4":str(Q),"C16":str(C),"e_zero_cubic_half":str(S.factor(C.subs(e,0)/2)),"scope":"Exact rational change of coordinates for fixed C4 support; no classification claim."}
b.joinpath("c4_factor_coordinates.json").write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result,indent=2))
