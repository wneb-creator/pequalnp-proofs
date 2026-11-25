import sys,ctypes,random,time
sys.argv=['v','0']; import fresh_meta3773_five_component as new
import fresh_meta3773_five_wide as old
m=new.model
def direct(s,F,p,n):
 z=(ctypes.c_uint64*len(F))(*F);return s.fn(len(F),z,p,n)
F=tuple(sorted((*m.raw,*(m.raw[j] for j in range(m.point_count,m.raw_count) for _ in range(sum(y==j for x,y in m.E)-1)))));assert len(F)==19 and direct(new,F,m.target,m.M^m.target)==direct(old,F,m.target,m.M^m.target)==1
print('ordinary 18-gate two-triple positive control accepted at19 leaves',flush=True)
r=random.Random(5137)
for size in range(13,20):
 for trial in range(4):
  # Inputs omit selected feature/test bits in both obligations to exercise recursive subproblems.
  f=tuple(r.choices((*m.raw,*m.free),k=size));a,b=f[0],f[1]
  for x in f[2::2]:a=(a|x) if r.randrange(2)else(a&x)
  for x in f[3::2]:b=(b|x) if r.randrange(2)else(b&x)
  val=a&b if trial%2==0 else a|b;p=val&r.getrandbits(m.NT);n=(m.M^val)&r.getrandbits(m.NT)
  assert direct(new,f,p,n)==direct(old,f,p,n)==1
 print('formula witness partial-spec comparisons',size,4,flush=True)
