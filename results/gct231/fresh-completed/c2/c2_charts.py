import argparse
import itertools
import json
import multiprocessing as mp
import time
import sympy as s


def primitive(vec):
    den = s.ilcm(*[v.q for v in vec])
    vec = den * vec
    return vec / s.igcd(*[int(v) for v in vec])


def hyperbolic(G0):
    R = s.eye(G0.rows)
    EE, FF = [], []
    for step in range(G0.rows // 2):
        G = R.T * G0 * R
        n = G.rows
        if n == 2:
            aa, bb, cc = G[0, 0], G[0, 1], G[1, 1]
            if cc:
                root = s.sqrt(bb * bb - aa * cc)
                e = s.Matrix([1, s.simplify((-bb + root) / cc)])
                f = s.Matrix([1, s.simplify((-bb - root) / cc)])
                f = (f / (e.T * G * f)[0]).applyfunc(s.simplify)
            else:
                e = s.Matrix([0, 1])
                f = s.Matrix([1 / bb, -aa / (2 * bb * bb)])
        else:
            e = None
            gg = list(G)
            for bound in (2, 4, 8, 16):
                vals = [0] + [j for k in range(1, bound + 1) for j in (k, -k)]
                for tup in itertools.product(vals, repeat=n):
                    if any(tup) and sum(gg[i*n+j]*tup[i]*tup[j] for i in range(n) for j in range(n)) == 0:
                        e = s.Matrix(tup)
                        break
                if e is not None:
                    break
            if e is None:
                raise RuntimeError('No rational isotropic vector found')
            j = next(j for j in range(n) if (e.T * G)[j])
            f = s.eye(n)[:, j]
            b = (e.T * G * f)[0]
            f = f/b - (f.T*G*f)[0]/(2*b*b)*e
        EE.append((R*e).applyfunc(s.simplify))
        FF.append((R*f).applyfunc(s.simplify))
        assert s.simplify((e.T * G * e)[0]) == 0
        assert s.simplify((f.T * G * f)[0]) == 0
        assert s.simplify((e.T * G * f)[0] - 1) == 0
        if n > 2:
            R = R*s.Matrix.hstack(*[primitive(v) for v in s.Matrix.vstack(e.T*G, f.T*G).nullspace()])
    if G0.rows % 2:
        Z = R
        dd = (Z.T * G0 * Z)[0]
    else:
        Z, dd = s.zeros(G0.rows, 1), 0
    return s.Matrix.hstack(*EE), s.Matrix.hstack(*FF), Z, dd


def target(which):
    x,y,p,v,w,r,h = s.symbols('x y p v w r h')
    zz = -2*x-y-2*p-4*v-4*w-2*r
    A = s.Matrix([[x,p,v,w],[p,x,v,w],[v,v,y,r],[w,w,r,zz]])
    vars = [p,v,w,r,y,x]
    if which == 'mixed0':
        A = A.subs(x,p)
        vars = [p,v,w,r,y]
    elif which in ('mixed4a', 'mixed4b'):
        A = A.subs(x,p+8*r-8*v-8*w+8*y)
        if which == 'mixed4a':
            A = A.subs(r,w)
            vars = [p,v,w,y]
        else:
            A = A.subs(p,-(19*r-12*v-12*w+17*y)/4)
            vars = [v,w,r,y]
    M = s.ones(4)+h*A
    pp = s.Poly(s.expand(sum(s.prod(M[i,pm[i]] for i in range(4)) for pm in itertools.permutations(range(4)))-24),h)
    assert pp.nth(1) == 0
    H = {k: pp.nth(k) for k in (2,3,4)}
    G = s.hessian(-H[2]/2, vars)/2
    assert G.det() != 0
    E,F,Z,dd = hyperbolic(G)
    B = s.Matrix.hstack(E,F,Z) if len(vars)%2 else s.Matrix.hstack(E,F)
    assert B.det() != 0
    return vars,H,E,F,Z,dd


def worker(which, chart, queue):
    begin = time.monotonic()
    vs,H,E,F,Z,dd = target(which)
    n = len(vs)//2
    X = s.Matrix(s.symbols('X:'+str(n)))
    params = s.symbols('a:'+str(n*(n-1)//2 + (n if len(vs)%2 else 0)))
    S = s.zeros(n)
    j = 0
    for i in range(n):
        for k in range(i+1,n):
            S[i,k],S[k,i] = params[j],-params[j]
            j += 1
    if len(vs)%2:
        rr = s.Matrix(1,n,params[j:])
        Y = (S-dd*rr.T*rr/2)*X
        zz = (rr*X)[0]
    else:
        Y,zz = S*X,0
    left = s.Matrix([Y[i] if chart>>i&1 else X[i] for i in range(n)])
    right = s.Matrix([X[i] if chart>>i&1 else Y[i] for i in range(n)])
    vec = E*left+F*right+Z*zz
    sub = dict(zip(vs,vec))
    assert s.simplify(H[2].subs(sub, simultaneous=True)) == 0
    eq = []
    for k in (3,4):
        expr = s.expand(H[k].subs(sub, simultaneous=True))
        for f in s.Poly(expr,*X).coeffs():
            f = s.Poly(f,*params,extension=True).clear_denoms()[1].as_expr()
            if f != 0:
                eq.append(f)
    basis = s.groebner(eq,*params,order='grevlex',extension=True)
    ans = {'target':which,'chart':chart,'seconds':time.monotonic()-begin,'equations':len(eq),'basis':[str(v.as_expr()) for v in basis.polys], 'unit_ideal':list(basis)==[1]}
    queue.put(ans)


if __name__ == '__main__':
    ap=argparse.ArgumentParser();ap.add_argument('target');ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--chart',type=int,action='append');args=ap.parse_args()
    n={'plus':3,'mixed0':2,'mixed4a':2,'mixed4b':2}[args.target]
    for chart in (args.chart if args.chart is not None else range(2**n)):
        queue=mp.Queue();process=mp.Process(target=worker,args=(args.target,chart,queue));process.start();process.join(args.seconds)
        if process.is_alive():
            process.terminate();process.join();ans={'target':args.target,'chart':chart,'status':'UNKNOWN_TIME_LIMIT'}
        elif process.exitcode:
            ans={'target':args.target,'chart':chart,'status':'ERROR','exit':process.exitcode}
        else:ans=queue.get()
        print(json.dumps(ans),flush=True)
