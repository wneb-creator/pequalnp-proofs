import argparse
import json
from pathlib import Path


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--map',type=Path,required=True)
    parser.add_argument('--log',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    d=json.loads(args.map.read_text());s=args.log.read_text()
    if 's SATISFIABLE' not in s.splitlines():
        print('NO SAT MODEL')
        raise SystemExit(1)
    pos={int(x) for line in s.splitlines() if line.startswith('v ') for x in line[2:].split() if int(x)>0}
    var={tuple(a):b for a,b in d['variables']}
    gates=[]
    if 'ands' in d:
        node_wires=[]
        def combine_or(wires):
            assert wires
            current=wires[0]
            for following in wires[1:]:
                gates.append(('or',sorted([current,following])))
                current=d['n']+len(gates)-1
            return current
        for i in range(d['ands']):
            roots=[]
            for side in (0,1):
                selected=[j for j in range(d['n']+i) if var[('s',i,side,j)] in pos]
                wires=[j if j<d['n'] else node_wires[j-d['n']] for j in selected]
                roots.append(combine_or(wires))
            gates.append(('and',sorted(roots)))
            node_wires.append(d['n']+len(gates)-1)
        output=combine_or([node_wires[i] for i in range(d['ands']) if var[('out',i)] in pos])
        assert len(gates)<=d['size']
    else:
        for i in range(d['k']):
            wires=[next(a for a in range(d['n']+i) if var[('s',i,side,a)] in pos) for side in (0,1)]
            gates.append(('and' if var[('op',i)] in pos else 'or',wires))
        output=d['n']+len(gates)-1
    for i,(op,wires) in enumerate(gates):
        assert op in ('and','or') and len(wires)==2 and all(0<=j<d['n']+i for j in wires)
    left_count=max(a for a,b in d['edges'])+1
    tests={(1<<a)|(1<<b) for a,b in d['edges']}
    for left in range(1<<left_count):
        allowed=[v for v in range(left_count,d['n']) if not any(left&(1<<a) and b==v for a,b in d['edges'])]
        tests.add(left+sum(1<<v for v in allowed))
    for t in sorted(tests):
        wires=[bool(t&(1<<a)) for a in range(d['n'])]
        for op,(a,b) in gates:
            wires.append(wires[a] and wires[b] if op=='and' else wires[a] or wires[b])
        target=any(t&(1<<a) and t&(1<<b) for a,b in d['edges'])
        assert wires[output]==target,(t,wires[output],target)
    args.output.write_text(json.dumps(gates))
    print(json.dumps({'gates':len(gates),'output':output,'inputs':d['n'],'verified_tests':len(tests),'ands':sum(op=='and' for op,_ in gates),'tuple_file':str(args.output)}))


if __name__=='__main__':
    main()
