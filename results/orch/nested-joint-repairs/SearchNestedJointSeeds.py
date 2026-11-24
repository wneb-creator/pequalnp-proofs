"""Add a clean joint of the two dirty shared helpers to three INVALID seeds."""
import argparse
import json
from pathlib import Path
import SearchAlternative6PairProblem as problem
from SearchNestedSeeds import generate
from SearchPhysicalRepairPairs import evaluate, scalar_artifact


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    for a,b in ((0,1),(2,3),(4,5)):
        before=generate(a,b)
        assert before['original_size']==26
        gates=list(before['gates'][:26])
        helper_indices=[i for i,(operation,pair) in enumerate(gates) if operation=='and'][:2]
        assert helper_indices==[4,8]
        gates.append(('and',(problem.N+4,problem.N+8)))
        gates.append(('or',(problem.N+25,problem.N+26)))
        state=tuple((operation,tuple(pair)) for operation,pair in gates)
        ev=evaluate(problem,state)
        old=evaluate(problem,tuple((op,tuple(pair)) for op,pair in before['gates']))
        assert ev[2]==old[2] and ev[0]==0 and ev[1]>0
        assert ev[3][problem.N+26] & (problem.ALL_TESTS^problem.TARGET)==0
        artifact=scalar_artifact(problem,state,'INVALID nested dirty-helper joint repair seed')
        artifact.update({'selected_clean_points':[a,b],'augmented_negative_errors':ev[1],
                         'joint_gate_index':26,'original_size':26})
        name='joint-'+str(a)+'-'+str(b)+'.json'
        (args.output_dir/name).write_text(json.dumps(artifact,indent=2)+'\n')
        print(json.dumps({'file':name,'size':len(gates),'raw_errors':artifact['wrong_raw_tests'],
                          'augmented_errors':ev[1],'joint_clean_on_complete_basis':True}),flush=True)
    print('PASS3INVALIDjoint seeds, complete88scalar verification each')


if __name__=='__main__':
    main()
