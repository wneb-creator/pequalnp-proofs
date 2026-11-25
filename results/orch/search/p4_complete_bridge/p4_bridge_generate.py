from pathlib import Path
import hashlib,json
from repair_nearmiss_v3 import CNF

ROOT=Path('/tmp/oec/pequalnp-pilot-64')

class TraceCNF(CNF):
    def __init__(self):
        super().__init__();self.expr={1:('const',True)};self.tags=[('true',)];self.tag=None;self.sources={}
    def add(self,*xs):
        before=len(self.cs);super().add(*xs)
        if len(self.cs)>before:self.tags.append(self.tag)
    def emit(self,tag,*xs):
        old=self.tag;self.tag=tag;self.add(*xs);self.tag=old
    def land(self,a,b):
        if a == -1 or b == -1 or a == -b:return -1
        if a==1:return b
        if b==1 or a==b:return a
        z=self.new();self.expr[z]=('and',a,b)
        for i,cl in enumerate([(-z,a),(-z,b),(z,-a,-b)]):self.emit(('and',z,i,a,b),*cl)
        return z
    def choose(self,ls):
        src=self.sources[tuple(ls)];self.emit(('alo',src,tuple(ls)),*ls);prev=-1;prefix=[]
        for i,x in enumerate(ls):
            self.emit(('amo',src,i,prev,x),-prev,-x)
            prev=self.lor(prev,x);prefix.append(prev)
        return prefix
    def mux(self,selectors,values):
        if all(v==values[0] for v in values):return values[0]
        z=self.new();src=self.sources[tuple(selectors)];self.expr[z]=('mux',src,tuple(values))
        for i,(sel,v) in enumerate(zip(selectors,values)):
            self.emit(('mux',z,src,i,sel,v),-sel,-z,v)
            self.emit(('mux',z,src,i,sel,v),-sel,z,-v)
        return z
    def op(self,op,a,b):
        assert op not in [1,-1]
        z=self.new();self.expr[z]=('op',op,a,b)
        for cl in [(-op,-z,a),(-op,-z,b),(-op,z,-a,-b),(op,z,-a),(op,z,-b),(op,-z,a,b)]:self.emit(('op',z,op,a,b),*cl)
        return z

c=TraceCNF();ops=[];sels=[]
for j in range(5):
    op=c.new();c.expr[op]=('freeop',j);ops.append(op)
    a=[c.new() for _ in range(4+j)];b=[c.new() for _ in range(4+j)]
    for side,ss in [('a',a),('b',b)]:
        src=(j,side);c.sources[tuple(ss)]=src
        for i,v in enumerate(ss):c.expr[v]=('selector',src,i)
    c.choose(a);pref=c.choose(b)
    for i in range(4+j):c.emit(('order',j,i,a[i],pref[i]),-a[i],-pref[i])
    sels.append((a,b))

def ev(mask):
    w=[1 if mask>>i&1 else -1 for i in range(4)];args=[]
    for j in range(5):
        a,b=[c.mux(s,w) for s in sels[j]];args.append((a,b));w.append(c.op(ops[j],a,b))
    return w,args

def der(base,seed,label):
    _,args=ev(1<<base);d=[1 if i==seed else -1 for i in range(4)]
    for j in range(5):
        a,b=[c.mux(s,d) for s in sels[j]];av,bv=args[j]
        z=c.lor(c.land(av,b),c.land(a,bv));o=c.lor(a,b);v=c.new();c.expr[v]=('ite',ops[j],z,o)
        for cl in [(-ops[j],-v,z),(-ops[j],v,-z),(ops[j],-v,o),(ops[j],v,-o)]:c.emit(('ite',v,ops[j],z,o),*cl)
        d.append(v)
    c.emit(('derivative',label,d[-1]),-d[-1]);return d[-1]

outs=[]
for mask in range(16):
    target=any(mask>>a&1 and mask>>b&1 for a,b in [(0,1),(0,2),(1,3)])
    vals,_=ev(mask);outs.append(vals[-1]);c.emit(('output',mask,bool(target),vals[-1]),vals[-1] if target else -vals[-1])
dl=der(0,1,'left');dr=der(1,0,'right')
c.write(ROOT/'p4-bridge-regenerated.cnf')
original=(ROOT/'audit-path-center5.cnf').read_bytes();generated=(ROOT/'p4-bridge-regenerated.cnf').read_bytes()
assert original==generated
assert set(c.expr)==set(range(1,c.n+1)) and len(c.tags)==len(c.cs)
(ROOT/'p4-bridge-trace.json').write_text(json.dumps({'expr':c.expr,'clauses':c.cs,'tags':c.tags,'outputs':outs,'left':dl,'right':dr},indent=2)+'\n')
print(json.dumps({'variables':c.n,'clauses':len(c.cs),'cnf_sha256':hashlib.sha256(generated).hexdigest(),'node_kinds':sorted({x[0] for x in c.expr.values()})}))
