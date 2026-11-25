from pathlib import Path
from functools import lru_cache
import gtree_simple_readers as g

def bits(x):return [p for p in range(g.N) if x&(1<<p)]
def verts(A,E):
    V=A
    for e in E:V|=e
    return V
def pin(A,E,p,b):
    bit=1<<p
    if not b:return A&~bit,tuple(e for e in E if not e&bit)
    assert not A&bit
    A1=A
    for e in E:
        if e&bit:A1|=e&~bit
    return A1,tuple(e for e in E if not e&(A1|bit))
def nf(A,E):
    if A:return False
    ns={p:0 for p in bits(verts(A,E))}
    for e in E:
        p,q=bits(e);ns[p]|=1<<q;ns[q]|=1<<p
    if len(set(ns.values()))<len(ns):return False
    return all(not(ns[p]==1<<q and ns[q]==1<<p) for e in E for p,q in [bits(e)])

choices={}
@lru_cache(None)
def cost(A,E,r):
    if r<=verts(A,E).bit_count()-1:
        choices[A,E,r]=('dep',)
        return 1
    opts=[]
    for p in bits(verts(A,E)):
        c0=pin(A,E,p,False)
        if any(c0) and g.lb(*c0)>=r-1:opts.append((1+cost(*c0,r-1),('one',p,False,c0)))
        if A&(1<<p):continue
        c1=pin(A,E,p,True)
        if any(c1) and g.lb(*c1)>=r-1:opts.append((1+cost(*c1,r-1),('one',p,True,c1)))
        if any(c0) and any(c1) and g.lb(*c0)>=r-2 and g.lb(*c1)>=r-2:
            opts.append((1+cost(*c0,r-2)+cost(*c1,r-2),('two',p,c0,c1)))
    if nf(A,E):
        cs=[(p,pin(A,E,p,False),pin(A,E,p,True)) for p in bits(verts(A,E))]
        if all(any(a) and any(b) and g.lb(*a)>=r-3 and g.lb(*b)>=r-4 for p,a,b in cs):
            opts.append((1+sum(cost(*a,r-3)+cost(*b,r-4) for p,a,b in cs),('reader',cs)))
    if not opts:raise ValueError(A,E,r,g.lb(A,E))
    best=min(opts,key=lambda x:x[0]);choices[A,E,r]=best[1]
    return best[0]

@lru_cache(None)
def canon_component(es):
    vs=sorted({p for e in es for p in bits(e)})
    ns={p:set() for p in vs}
    for e in es:
        p,q=bits(e);ns[p].add(q);ns[q].add(p)
    def refine(part):
        while True:
            new=[]
            for cell in part:
                groups={}
                for p in cell:
                    sig=tuple(len(ns[p].intersection(c)) for c in part)
                    groups.setdefault(sig,[]).append(p)
                new.extend(tuple(groups[k]) for k in sorted(groups))
            if new==part:return part
            part=new
    def run(part):
        part=refine(part)
        cs=[(len(c),i) for i,c in enumerate(part) if len(c)>1]
        if not cs:
            order=[c[0] for c in part];mp={p:i for i,p in enumerate(order)}
            code=tuple(sorted((1<<mp[p])|(1<<mp[q]) for e in es for p,q in [bits(e)]))
            return code,tuple(order)
        _,i=min(cs);best=None
        for p in part[i]:
            v=run(part[:i]+[(p,),tuple(q for q in part[i] if q!=p)]+part[i+1:])
            if best is None or v[0]<best[0]:best=v
        return best
    part=[]
    for d in sorted({len(ns[p]) for p in vs}):part.append(tuple(p for p in vs if len(ns[p])==d))
    return run(part)

@lru_cache(None)
def canonical(A,E):
    remaining=set(p for e in E for p in bits(e));comps=[]
    while remaining:
        todo=[next(iter(remaining))];comp=set(todo)
        while todo:
            p=todo.pop()
            for e in E:
                if e&(1<<p):
                    for q in bits(e):
                        if q not in comp:comp.add(q);todo.append(q)
        remaining-=comp
        es=tuple(e for e in E if any(e&(1<<p) for p in comp))
        code,order0=canon_component(es);comps.append((len(comp),code,order0))
    comps.sort()
    order0=bits(A)+[p for _,_,ps in comps for p in ps]
    mp={p:i for i,p in enumerate(order0)}
    canA=(1<<A.bit_count())-1
    canE=tuple(sorted((1<<mp[p])|(1<<mp[q]) for e in E for p,q in [bits(e)]))
    return canA,canE,tuple(mp.get(p,0) for p in range(g.N))

ids={};order=[];records={}
def collect(A,E,r):
    ca,ce,mp=canonical(A,E);key=ca,ce,r
    if key in ids:return ids[key]
    ch=choices[A,E,r]
    def edge(child,req):
        ci=collect(*child,req)
        _,_,cm=canonical(*child)
        inv={mp[p]:p for p in bits(verts(A,E))}
        rename=tuple(cm[inv[p]] if p in inv else 0 for p in range(g.N))
        return ci,rename
    if ch[0]=='dep':newch=ch
    if ch[0]=='one':newch=('one',mp[ch[1]],ch[2],edge(ch[3],r-1))
    if ch[0]=='two':
        newch=('two',mp[ch[1]],edge(ch[2],r-2),edge(ch[3],r-2))
    if ch[0]=='reader':
        newch=('reader',[(mp[p],edge(a,r-3),edge(b,r-4)) for p,a,b in ch[1]])
    i=len(order);ids[key]=i;order.append(key)
    records[key]=newch
    return i

def inp(mask):return f'wi {mask}'
def fnexpr(A,E):
    return ' || '.join([f'x {p}' for p in bits(A)]+[f'(x {a} && x {b})' for a,b in map(bits,E)]) or 'false'
def evalf(A,E,mask):return bool(A&mask) or any(e&mask==e for e in E)
def dpw(A,E,p):
    if A&(1<<p):return 0
    return next(e&~(1<<p) for e in E if e&(1<<p))
def ncw(A,E,p,b):
    a,e=pin(A,E,p,b)
    if a:return a&-a
    return e[0]
def nf_witness(A,E,p,q,a,b):
    for mask in [0]+[1<<k for k in range(g.N)]+list(E):
        def setpq(x,y):return (mask&~((1<<p)|(1<<q)))|(x<<p)|(y<<q)
        z=[evalf(A,E,setpq(1-a,b)),evalf(A,E,setpq(a,1-b)),evalf(A,E,setpq(1-a,1-b))]
        if not(z[0]==z[1]==z[2]):return mask
    raise ValueError('nf witness',A,E,p,q,a,b)

def emit():
    print('computing',g.lb(0,g.E0),'cost',cost(0,g.E0,20),flush=True)
    collect(0,g.E0,20)
    print('DAG nodes',len(order),'readers',sum(records[k][0]=='reader' for k in order),flush=True)
    src=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_5670.lean').read_text().splitlines()
    text='\n'.join(src[:4236]).replace('PEqualNP.Outside.L_meta_5670','PEqualNP.Outside.L_meta_9811_aux').replace('theorem ','lemma ')
    # Strip comments while retaining source layout and all declarations.
    import re
    text=re.sub(r'/\*.*?\*/','',text,flags=re.S)
    text='\n'.join(l for l in text.splitlines() if not l.lstrip().startswith('--'))
    text=text.replace('import PEqualNP.Defs','import PEqualNP.Defs\nimport Mathlib.Tactic.ITauto')
    supp=Path('/tmp/oec/pequalnp-pilot-85/Support9811.lean').read_text()
    supp=supp[supp.index('lemma dep_mem_support'):supp.index('lemma any_eq_of_agree')]
    out=[text,'namespace PEqualNP.Outside.L_meta_9811_aux',supp,
      'open PEqualNP.MetaComplexity',
      'def wi (m : Nat) (i : Fin 14) : Bool := m.testBit i.val']
    for idx,(A,E,r) in enumerate(order):
        V=verts(A,E);ps=bits(V);ch=records[A,E,r]
        f=f'f{idx}';T=f'T{idx}';dep=f'dep{idx}';sup=f'sup{idx}'
        out += [f'def {f} (x : Fin 14 → Bool) : Bool := {fnexpr(A,E)}',
                f'def {T} : Finset (Fin 14) := {{{", ".join(map(str,ps))}}}',
                f'lemma {sup} (x y : Fin 14 → Bool) (h : ∀ i ∈ {T}, x i = y i) : {f} x = {f} y := by',
                '  simp only ['+f+', '+', '.join(f'h {p} (by decide)' for p in ps)+']']
        w=[dpw(A,E,p) if p in ps else 0 for p in range(g.N)]
        wexpr='wi ((['+','.join(map(str,w))+'] : List Nat).getD p.val 0)'
        out += [f'lemma {dep} : ∀ p ∈ {T}, Base.Readers.Dep {f} p := by',
                '  have hc : ∀ p : Fin 14, p ∈ '+T+' → '+f+' (Function.update ('+wexpr+') p (!('+wexpr+') p)) ≠ '+f+' ('+wexpr+') := by decide +kernel',
                '  intro p hp',f'  exact ⟨{wexpr}, hc p hp⟩']
        def eqproof(fi,p,b,fj,mp,indent='    '):
            rex='(fun i : Fin 14 => (['+','.join(map(str,mp))+'] : List (Fin 14)).getD i.val 0)'
            return [indent+f'let ren : Fin 14 → Fin 14 := {rex}',
                    indent+f'have he : (fun x : Fin 14 → Bool => {fi} (Function.update (x ∘ ren) {p} {str(b).lower()})) = {fj} := by',
                    indent+'  funext x',indent+'  apply Bool.eq_iff_iff.mpr',
                    indent+'  simp ['+fi+', '+fj+', Function.update_apply, ren, Function.comp_apply]',indent+'  <;> itauto',
                    indent+'have hc := Base.PermInputs.relabel_size ren _ _ hc',
                    indent+f'change HasCircuitSize 14 (fun x => {fi} (Function.update (x ∘ ren) {p} {str(b).lower()})) _ at hc',
                    indent+'rw [he] at hc']
        if idx==len(order)-1:out += ['set_option maxHeartbeats 0 in']
        out += [f'lemma lower{idx} (s : Nat) (h : HasCircuitSize 14 {f} s) : {r} ≤ s := by']
        if ch[0]=='dep':
            out += [f'  have hc := Base.PermInputs.dep_lower_set 14 {f} {T} {dep} s h',
                    f'  have ht : {T}.card = {len(ps)} := by decide +kernel','  omega']
        elif ch[0]=='one':
            _,p,b,c=ch;ci,mp=c
            out += ['  by_contra hn',f'  have hs : s ≤ {r-1} := by omega',
                    f'  have hbig : HasCircuitSize 14 {f} ({r-2}+1) := by',
                    '    obtain ⟨C,hc,hz,hv⟩ := h',
                    '    exact ⟨C,hc,by omega,hv⟩',
                    f'  have hc := Base.Forest.one_gate_at 13 {f} {p} {str(b).lower()} {r-2}',
                    f'    ({dep} {p} (by decide)) ⟨wi 0, wi {ncw(A,E,p,b)}, by decide +kernel⟩ hbig']
            out += eqproof(f,p,b,f'f{ci}',mp,indent='  ')
            out += [f'  have := lower{ci} {r-2} hc','  omega']
        elif ch[0]=='two':
            _,p,c0,c1=ch
            out += [f'  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 {f} {p} s',
                    f'    ({dep} {p} (by decide)) (by',
                    '      intro b; cases b',
                    f'      · exact ⟨wi 0, wi {ncw(A,E,p,False)}, by decide +kernel⟩',
                    f'      · exact ⟨wi 0, wi {ncw(A,E,p,True)}, by decide +kernel⟩) h',
                    '  cases b']
            for b,c in [(False,c0),(True,c1)]:
                ci,mp=c
                out += ['  · have hh := lower'+str(ci)]
                out += eqproof(f,p,b,f'f{ci}',mp)
                out += [f'    have := hh t hc','    omega']
        elif ch[0]=='reader':
            cs=ch[1]
            # Supply all reader hypotheses with closed witness tables.
            out += [f'  have support : ∀ p, Base.Readers.Dep {f} p → p ∈ {T} :=',
                    f'    fun p hp => dep_mem_support {f} {T} {sup} p hp']
            masks=[ncw(A,E,p,bool(b)) if p in ps else 0 for p in range(g.N) for b in [0,1]]
            wnc='wi ((['+','.join(map(str,masks))+'] : List Nat).getD (p.val*2 + if b then 1 else 0) 0)'
            out += [f'  have hnc : Base.Readers.RestrNC {f} := by',
                    f'    have check : ∀ (p : Fin 14), p ∈ {T} → ∀ b : Bool, {f} (Function.update (wi 0) p b) ≠ {f} (Function.update ({wnc}) p b) := by decide +kernel',
                    f'    intro p hp b; exact ⟨wi 0, {wnc}, check p (support p hp) b⟩']
            masks=[nf_witness(A,E,p,q,a,b) if p in ps and q in ps and p!=q else 0 for p in range(g.N) for q in range(g.N) for a in [0,1] for b in [0,1]]
            wnf='wi ((['+','.join(map(str,masks))+'] : List Nat).getD (((p.val*14+q.val)*2 + if a then 1 else 0)*2 + if b then 1 else 0) 0)'
            out += [f'  have hnf : Base.Readers.NoFunnel {f} := by',
                    f'    let w (p q : Fin 14) (a b : Bool) := {wnf}',
                    f'    have check : ∀ (p q : Fin 14), p ∈ {T} → q ∈ {T} → p ≠ q → ∀ a b : Bool, ¬ ({f} (Base.Readers.set2 (w p q a b) p (!a) q b) = {f} (Base.Readers.set2 (w p q a b) p a q (!b)) ∧ {f} (Base.Readers.set2 (w p q a b) p a q (!b)) = {f} (Base.Readers.set2 (w p q a b) p (!a) q (!b))) := by decide +kernel',
                    '    intro p q hpq hp hq hf',
                    '    obtain ⟨a,b,hab⟩ := hf',
                    '    exact check p q (support p hp) (support q hq) hpq a b (hab (w p q a b))']
            for b,drop in [(False,3),(True,4)]:
                name='lo' if not b else 'hi'
                out += [f'  have {name} (p : Fin 14) (hp : p ∈ {T}) (t : Nat)',
                        f'      (hc : HasCircuitSize 14 (fun x => {f} (Function.update x p {str(b).lower()})) t) : {r-drop} ≤ t := by',
                        '    fin_cases p']
                for p in range(g.N):
                    if p not in ps:
                        out += [f'    · simp [{T}] at hp']
                        continue
                    c=next((cb if b else ca) for pp,ca,cb in cs if pp==p);ci,mp=c
                    out += ['    · have hh := lower'+str(ci)]
                    out += eqproof(f,p,b,f'f{ci}',mp,indent='      ')
                    out += ['      exact hh t hc']
            out += [f'  obtain ⟨p,hp,hpays⟩ := Base.Readers.fanout_step 13 {f} s ⟨{ps[0]}, {dep} {ps[0]} (by decide)⟩ hnc hnf h',
                    '  rcases hpays with ⟨⟨t,ht,hc⟩,_⟩ | ⟨⟨t,ht,hc⟩,_⟩ | ⟨_,⟨t,ht,hc⟩⟩',
                    '  · have := lo p (support p hp) t hc; omega',
                    '  · have := lo p (support p hp) t hc; omega',
                    '  · have := hi p (support p hp) t hc; omega']
    top=len(order)-1
    _,_,rootmap=canonical(0,g.E0)
    rootren='(fun i : Fin 14 => (['+','.join(map(str,rootmap))+'] : List (Fin 14)).getD i.val 0)'
    out += [f'def lowerTarget9811 (x : Fin 14 → Bool) : Bool := {fnexpr(0,g.E0)}',
            'lemma lowerBound20 (s : Nat) (h : HasCircuitSize 14 lowerTarget9811 s) : 20 ≤ s := by',
            f'  let ren : Fin 14 → Fin 14 := {rootren}',
            '  have hh := Base.PermInputs.relabel_size ren lowerTarget9811 s h',
            f'  have he : (fun x : Fin 14 → Bool => lowerTarget9811 (x ∘ ren)) = f{top} := by',
            '    funext x; apply Bool.eq_iff_iff.mpr',
            f'    simp [lowerTarget9811, f{top}, ren, Function.comp_apply]',
            '    <;> itauto',
            '  rw [he] at hh',f'  exact lower{top} s hh',
            'end PEqualNP.Outside.L_meta_9811_aux']
    dest=Path('/tmp/oec/pequalnp-pilot-85/Lower9811.lean')
    dest.write_text('\n'.join(out)+'\n')
    print('wrote',dest,'bytes',dest.stat().st_size,flush=True)

if __name__=='__main__':emit()
