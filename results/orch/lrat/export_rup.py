import argparse
from pathlib import Path

def neg_type(lit):
    a=f'p {abs(lit)-1}'
    return f'({a})' if lit<0 else f'(¬ {a})'

def clause_type(c):
    return ' → '.join([*(neg_type(x) for x in c),'False'])

def parse_cnf(path):
    lines=path.read_text().splitlines();clauses=[];tokens=[]
    for line in lines:
        if not line or line.startswith(('c','p')):continue
        tokens.extend(map(int,line.split()))
    c=[]
    for tok in tokens:
        if tok: c.append(tok)
        else: clauses.append(c);c=[]
    assert not c
    return clauses

def export(cnf,lrat,name):
    clauses={i+1:c for i,c in enumerate(parse_cnf(cnf))}
    lines=['import Mathlib.Tactic','', 'set_option maxRecDepth 100000','set_option maxHeartbeats 0','',f'theorem {name} (p : Nat → Prop)']
    for i,c in clauses.items():lines.append(f'    (c{i} : {clause_type(c)})')
    lines+=['    : False := by','  classical']
    last=None
    for row in lrat.read_text().splitlines():
        toks=row.split()
        if not toks:continue
        if toks[1]=='d':continue
        vals=list(map(int,toks));cid=vals[0];cut=vals.index(0);c=vals[1:cut];hints=vals[cut+1:-1]
        assert all(h>0 for h in hints), 'RAT unsupported'
        lines.append(f'  have c{cid} : {clause_type(c)} := by')
        assign={}
        if c:lines.append('    intro '+' '.join(f'a{i}' for i in range(len(c))))
        for i,lit in enumerate(c):
            assert abs(lit) not in assign
            assign[abs(lit)]=(lit<0,f'a{i}')
        unit=0;closed=False
        for hint in hints:
            hc=clauses[hint];unknown=[];args=[]
            for lit in hc:
                known=assign.get(abs(lit))
                if known is None:unknown.append(lit);args.append('h')
                else:
                    assert known[0] != (lit>0), f'satisfied hint {cid} {hint}'
                    args.append(known[1])
            term=f'c{hint}'+(' '+' '.join(args) if args else '')
            if not unknown:
                lines.append(f'    exact {term}');closed=True;break
            assert len(unknown)==1, f'not unit {cid} {hint}'
            lit=unknown[0];var=abs(lit);uname=f'u{unit}';unit+=1
            if lit>0:
                lines.append(f'    have {uname} : p {var-1} := Classical.byContradiction (fun h => {term})')
            else:
                lines.append(f'    have {uname} : ¬ p {var-1} := fun h => {term}')
            assign[var]=(lit>0,uname)
        assert closed, f'no contradiction {cid}'
        clauses[cid]=c;last=cid
    assert clauses[last]==[]
    lines.append(f'  exact c{last}')
    lines.append(f'\n#print axioms {name}')
    return '\n'.join(lines)+'\n'

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('cnf',type=Path);ap.add_argument('lrat',type=Path);ap.add_argument('out',type=Path);ap.add_argument('--name',default='PEqualNP.Outside.L_meta_2602_aux.rup_unsat')
    a=ap.parse_args();s=export(a.cnf,a.lrat,a.name);a.out.write_text(s);print(f'{len(s.splitlines())} lines, {len(s)} bytes')
