"""Bounded nearby synthesis with explicit incomplete tests and full candidate replay."""
import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from SearchTriangle9Problem import EDGES,N,POSITIVES,RAW_NEGATIVES,TESTS


def scalar(gates,output,assignment):
    values=[bool(assignment>>j&1) for j in range(N)]
    for operation,(a,b) in gates:
        assert 0<=a<len(values) and 0<=b<len(values)
        values.append(values[a] and values[b] if operation=='and' else values[a] or values[b])
    return values[output]


def decode(cnf,log):
    data=json.loads(cnf.with_suffix('.map.json').read_text())
    assignment={}
    for line in log.read_text().splitlines():
        if line.startswith('v '):
            for value in map(int,line.split()[1:]):
                if value:assignment[abs(value)]=value>0
    variables={tuple(key):value for key,value in data['variables']}
    gates=[]
    for i in range(data['k']):
        inputs=[]
        for side in (0,1):
            selected=[j for j in range(N+i) if assignment[variables[('s',i,side,j)]]]
            assert len(selected)==1
            inputs.append(selected[0])
        assert inputs[0]<inputs[1]
        gates.append(['and' if assignment[variables[('op',i)]] else 'or',inputs])
    return gates,N+len(gates)-1


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--solver',type=Path,required=True)
    parser.add_argument('--statement',type=Path,required=True)
    parser.add_argument('--tests',type=Path,required=True)
    parser.add_argument('--nearby',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--edits',type=int,default=8)
    parser.add_argument('--round-seconds',type=int,default=90)
    parser.add_argument('--rounds',type=int,default=8)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    selected=set(json.loads(args.tests.read_text()))
    assert POSITIVES<=selected and selected<=set(TESTS)
    scripts=Path(__file__).resolve().parent
    started=time.monotonic()
    print(json.dumps({'event':'start','initial_tests':len(selected),'complete_tests':len(TESTS),
                      'edits':args.edits,'round_seconds':args.round_seconds,'rounds':args.rounds}),flush=True)
    for iteration in range(args.rounds):
        prefix=args.output_dir/('round-'+str(iteration))
        tests=prefix.with_suffix('.tests.json');tests.write_text(json.dumps(sorted(selected))+'\n')
        base=prefix.with_suffix('.base.cnf');cnf=prefix.with_suffix('.cnf')
        commands=[
            [sys.executable,str(scripts/'SearchSubset.py'),'--case','plane_local','--points','0,1,2,3,4,5,10,12,19',
             '--statement',str(args.statement),'--gates','52','--no-ordering','--no-pruning','--no-incomparability',
             '--tests-file',str(tests),'--output',str(base)],
            [sys.executable,str(scripts/'SearchNearby.py'),'--cnf',str(base),'--nearby',str(args.nearby),
             '--edits',str(args.edits),'--pad','--output',str(cnf)]]
        with prefix.with_suffix('.generate.log').open('w') as log:
            for command in commands:
                result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=False)
                if result.returncode:raise RuntimeError('generation failed; inspect full log')
        log=prefix.with_suffix('.solver.log')
        with log.open('w') as stream:
            result=subprocess.run([str(args.solver),'-t',str(args.round_seconds),str(cnf)],
                                  stdout=stream,stderr=subprocess.STDOUT,check=False)
        print(json.dumps({'event':'solver','round':iteration,'tests':len(selected),'exit':result.returncode}),flush=True)
        if result.returncode==20:
            print(json.dumps({'event':'UNSAT','scope':'fixed nearby edit neighborhood with selected tests; no general lower bound'}),flush=True)
            return
        if result.returncode!=10:
            print(json.dumps({'event':'NO_VERDICT','round':iteration}),flush=True)
            return
        gates,output=decode(cnf,log)
        assert len(gates)==52
        for assignment in selected:
            assert scalar(gates,output,assignment)==(assignment in POSITIVES)
        mistakes=[]
        for assignment in sorted(POSITIVES|RAW_NEGATIVES):
            actual=scalar(gates,output,assignment)
            expected=assignment in POSITIVES
            if actual!=expected:mistakes.append({'input':assignment,'actual':actual,'expected':expected})
        artifact={'inputs':N,'gates':gates,'output':output,'size':len(gates),'edge_list':EDGES,
                  'round':iteration,'selected_tests':len(selected),'wrong_raw_tests':len(mistakes),
                  'wrong_tests':mistakes,'proof_status':'INVALID partial-test model' if mistakes else 'computational witness; requires Lean verification'}
        prefix.with_suffix('.candidate.json').write_text(json.dumps(artifact,indent=2)+'\n')
        if not mistakes:
            (args.output_dir/'witness.json').write_text(json.dumps(artifact,indent=2)+'\n')
            print(json.dumps({'event':'WITNESS','size':52,'verified_raw_tests':len(POSITIVES|RAW_NEGATIVES)}),flush=True)
            return
        failing=[assignment for assignment in TESTS if assignment not in POSITIVES and scalar(gates,output,assignment)]
        assert failing and not set(failing)&selected
        added=[]
        while failing and len(added)<12:
            chosen=max(failing,key=lambda a:min((a^b).bit_count() for b in selected|set(added)))
            added.append(chosen);failing.remove(chosen)
        selected.update(added)
        print(json.dumps({'event':'INVALID_REFINED','round':iteration,'wrong_raw':len(mistakes),
                          'added_maximal_negatives':len(added),'elapsed':time.monotonic()-started}),flush=True)
    print(json.dumps({'event':'ROUND_CAP','conclusion':'no full witness found'}),flush=True)


if __name__=='__main__':
    main()
