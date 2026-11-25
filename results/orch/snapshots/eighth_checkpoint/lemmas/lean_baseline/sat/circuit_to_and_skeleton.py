import argparse,json
from pathlib import Path
from and_skeleton_sat import normalize,evaluate


def extract(gates,inputs,output):
    cones=[{i} for i in range(inputs)];ands=[]
    for i,(op,a,b) in enumerate(gates):
        assert op in (0,1) and 0<=a<inputs+i and 0<=b<inputs+i
        if op:cones.append(cones[a]|cones[b])
        else:
            ands.append({'left':sorted(cones[a]),'right':sorted(cones[b])})
            cones.append({inputs+len(ands)-1})
    assert 0<=output<len(cones)
    return normalize({'inputs':inputs,'and_gates':ands,'output':sorted(cones[output])})


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('source',type=Path);parser.add_argument('destination',type=Path)
    parser.add_argument('--inputs',type=int,required=True);parser.add_argument('--output',type=int)
    parser.add_argument('--problem',type=Path)
    args=parser.parse_args()
    data=json.loads(args.source.read_text());gates=data if isinstance(data,list) else data['gates']
    output=args.inputs+len(gates)-1 if args.output is None else args.output
    skeleton=extract(gates,args.inputs,output)
    skeleton.update({'and_count':len(skeleton['and_gates']),'input_original':list(range(args.inputs)),
                     'exact_boundary_verified':False,'full_truth_verified':False,'calibration':False,
                     'total_gate_bound_established':False,'status':'extracted phase skeleton; target correctness not asserted'})
    if args.problem:
        problem=json.loads(args.problem.read_text());skeleton['edges']=problem['edges']
        errors=0
        for test in problem['tests']:
            values=[bool(test['mask']>>i&1) for i in range(args.inputs)]
            for op,a,b in gates:values.append(values[a] or values[b] if op else values[a] and values[b])
            got=evaluate(skeleton,test['mask'])[1]
            assert got==values[output]
            errors+=got!=bool(test['label'])
        skeleton['phase_boundary_errors']=errors
    args.destination.write_text(json.dumps(skeleton))
    print('ANDnodes',len(skeleton['and_gates']),'phase_boundary_errors',skeleton.get('phase_boundary_errors'))

if __name__=='__main__':main()
