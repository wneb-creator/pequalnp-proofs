#!/usr/bin/env python3
"""Standalone finite-prime-field F4 driver for msolve's GMP-only neogb core."""
import argparse, ctypes as C, json, re, time
from fractions import Fraction
from pathlib import Path
import os, resource
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
for variable in tuple(os.environ):
    if variable not in {'PATH', 'LANG', 'LC_ALL', 'OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'TMPDIR'}:
        os.environ.pop(variable, None)

def parse_input(path):
    lines=Path(path).read_text().splitlines()
    names=[x.strip() for x in lines[0].split(',')]
    if len(set(names))!=len(names) or not all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',x) for x in names):
        raise ValueError('bad variable list')
    prime=int(lines[1]); assert prime==0 or 2<prime<2**31
    positions={x:i for i,x in enumerate(names)}
    body=''.join(lines[2:])
    body=re.sub(r'\s+mod\s+'+str(prime)+r'\b','',body).replace(' ','')
    polynomials=[]
    for raw in body.split(','):
        if not raw: continue
        data={}
        for token in re.findall(r'[+-]?[^+-]+',raw):
            sign=Fraction(-1 if token.startswith('-') else 1) if prime==0 else (-1 if token.startswith('-') else 1)
            token=token.lstrip('+-'); coeff=sign; exp=[0]*len(names)
            for factor in token.split('*'):
                if re.fullmatch(r'\d+(?:/\d+)?',factor):
                    if prime==0: coeff*=Fraction(factor)
                    else:
                        nums=factor.split('/'); coeff=coeff*int(nums[0])%prime
                        if len(nums)==2: coeff=coeff*pow(int(nums[1]),-1,prime)%prime
                else:
                    m=re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*)(?:\^(\d+))?',factor)
                    if m is None or m[1] not in positions: raise ValueError('bad factor '+factor)
                    exp[positions[m[1]]]+=int(m[2] or 1)
            e=tuple(exp); val=data.get(e,0)+coeff; data[e]=val if prime==0 else val%prime
        data={e:c for e,c in data.items() if c}
        if data: polynomials.append(data)
    return names,prime,polynomials

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('-f','--input',required=True)
    p.add_argument('-o','--output',required=True)
    p.add_argument('-t','--threads',type=int,default=2)
    p.add_argument('--info',type=int,choices=[0,1,2],default=2)
    p.add_argument('--la',type=int,choices=[1,2,42,44],default=2)
    p.add_argument('--max-pairs',type=int,default=0)
    p.add_argument('--hash-size',type=int,default=17)
    p.add_argument('--eliminate',type=int,default=0)
    p.add_argument('--no-reduce',action='store_true')
    a=p.parse_args()
    names,prime,polys=parse_input(a.input)
    lens=[]; coeffs=[]; exps=[]
    for poly in polys:
        items=sorted(poly.items(),key=lambda z:(-sum(z[0]),tuple(reversed(z[0]))))
        lens.append(len(items))
        for e,c in items: exps.extend(e); coeffs.append(c)
    print(json.dumps({'stage':'parsed','variables':len(names),'generators':len(lens),'terms':len(coeffs),'prime':prime}),flush=True)
    lib=C.CDLL(str(Path(__file__).with_name('libneogb-rational.so')))
    libc=C.CDLL(None)
    I=C.c_int32; PI=C.POINTER(I)
    f=lib.export_f4
    f.argtypes=[C.c_void_p,PI,C.POINTER(PI),C.POINTER(PI),C.POINTER(C.c_void_p),PI,PI,C.c_void_p,C.c_uint32]+[I]*12
    f.restype=C.c_int64
    bload=I(); blens=PI(); bexps=PI(); bcoeffs=C.c_void_p()
    larr=(I*len(lens))(*lens); earr=(I*len(exps))(*exps)
    class MPZ(C.Structure):
        _fields_=[('alloc',C.c_int),('size',C.c_int),('limbs',C.POINTER(C.c_ulong))]
    if prime==0:
        init=lib.__gmpz_init_set_str; init.argtypes=[C.POINTER(MPZ),C.c_char_p,C.c_int]; init.restype=C.c_int
        get=lib.__gmpz_get_str; get.argtypes=[C.c_void_p,C.c_int,C.POINTER(MPZ)]; get.restype=C.c_void_p
        size=lib.__gmpz_sizeinbase; size.argtypes=[C.POINTER(MPZ),C.c_int]; size.restype=C.c_size_t
        storage=[]
        for c in coeffs:
            for number in [c.numerator,c.denominator]:
                z=MPZ(); assert init(C.byref(z),str(number).encode(),10)==0; storage.append(z)
        carr=(C.POINTER(MPZ)*len(storage))(*(C.pointer(z) for z in storage))
    else: carr=(I*len(coeffs))(*coeffs)
    started=time.time()
    nterms=f(C.cast(libc.malloc,C.c_void_p),C.byref(bload),C.byref(blens),C.byref(bexps),C.byref(bcoeffs),larr,earr,carr,prime,0,a.eliminate,len(names),len(lens),a.hash_size,a.threads,a.max_pairs,0,a.la,not a.no_reduce,0,a.info)
    cptr=C.cast(bcoeffs,C.POINTER(MPZ) if prime==0 else PI)
    def coefficient(k):
        if prime:
            return int(cptr[k])%prime
        z=C.pointer(cptr[k]); buf=C.create_string_buffer(size(z,10)+2); get(buf,10,z)
        return int(buf.value.decode())
    basis=[]; offset=0
    for i in range(bload.value):
        terms=[]
        for j in range(blens[i]):
            k=offset+j
            terms.append({'coefficient':coefficient(k),'exponents':[int(bexps[k*len(names)+v]) for v in range(len(names))]})
        basis.append(terms); offset+=blens[i]
    result={'variables':names,'prime':prime,'basis':basis,'terms':int(nterms),'seconds':time.time()-started}
    Path(a.output).write_text(json.dumps(result))
    unit=any(len(q)==1 and q[0]['coefficient'] and not any(q[0]['exponents']) for q in basis)
    print(json.dumps({'stage':'finished','basis_size':bload.value,'terms':int(nterms),'unit_ideal':unit,'seconds':result['seconds']}),flush=True)

if __name__=='__main__': main()
