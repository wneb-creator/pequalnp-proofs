"""Mask an input by an independent positive implicant already present in F."""
import json
from pathlib import Path
from blif_validate import Builder, INPUTS, MASK, N, TARGET, translate


def main():
    base=Path(__file__).parent
    original=translate(base/'star25.blif')['gates']
    assert len(original)==25
    values=INPUTS.copy();supports=[{i} for i in range(N)]
    for op,a,b in original:
        values.append(values[a]&values[b] if op==0 else values[a]|values[b] if op==1 else MASK^values[a])
        supports.append(supports[a]|supports[b] if op<2 else supports[a])
    out=base/'masked-seeds';out.mkdir(exist_ok=True)
    rows=[]
    for v in range(N):
        for g in range(N,N+len(original)):
            if original[g-N][0]!=0 or v in supports[g] or values[g]&~TARGET:
                continue
            for negative in [False,True]:
                builder=Builder();done={i:i for i in range(N)};masked=None
                def visit(w):
                    nonlocal masked
                    if w==v:
                        if masked is None:
                            mask=visit(g)
                            masked=builder.conj(v,builder.neg(mask)) if negative else builder.disj(v,mask)
                        return masked
                    if w in done:return done[w]
                    op,a,b=original[w-N]
                    done[w]=builder.emit(op,visit(a),visit(b) if op<2 else -1)
                    return done[w]
                root=visit(N+len(original)-1)
                gates,root=builder.prune(root)
                ws=INPUTS.copy()
                for op,a,b in gates:
                    va=0 if a<0 else ws[a];vb=0 if b<0 else ws[b]
                    ws.append(va&vb if op==0 else va|vb if op==1 else MASK^va)
                assert ws[root]==TARGET
                assert len(gates)==(27 if negative else 26)
                name=f"input-{v:02d}-mask-{g:02d}-{'negative' if negative else 'positive'}"
                result={'gates':gates,'gate_count':len(gates),'output':root,'errors':0,
                        'not_count':sum(op==2 for op,a,b in gates),'masked_input':v,'mask_gate':g,
                        'mask_support':sorted(supports[g]),'negative':negative}
                (out/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
                lines=['.model masked','.inputs '+' '.join(f'x{i}' for i in range(N)),'.outputs y']
                def wire(w):return f'x{w}' if w<N else f'g{w-N}'
                for j,(op,a,b) in enumerate(gates):
                    if op==2:lines.append(f'.gate INV A={wire(a)} Y=g{j}')
                    else:lines.append(f'.gate {"AND2" if op==0 else "OR2"} A={wire(a)} B={wire(b)} Y=g{j}')
                lines+= [f'.gate BUF A={wire(root)} Y=y','.end']
                path=out/(name+'.blif');path.write_text('\n'.join(lines)+'\n')
                checked=translate(path)
                assert checked['errors']==0 and checked['gate_count']==len(gates)
                rows.append({'path':str(out/(name+'.json')),'blif':str(path),
                             **{k:result[k] for k in ['gate_count','not_count','masked_input','mask_gate','mask_support']},
                             'and_count':sum(op==0 for op,a,b in gates),
                             'ands_before_not':next((sum(gates[k][0]==0 for k in range(j)) for j,(op,a,b) in enumerate(gates) if op==2),None)})
    (out/'index.json').write_text(json.dumps(rows,indent=2)+'\n')
    print('validated',len(rows),'masked seeds; count',len(rows)//2,'each26gate monotone and27gate oneNOT')


if __name__=='__main__':main()
