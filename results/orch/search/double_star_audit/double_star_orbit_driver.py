from pathlib import Path
import argparse,itertools,json,subprocess,sys,time

SCRATCH=Path('/tmp/oec/pequalnp-pilot-64')
EDGES={tuple(sorted(e)) for e in [(0,4),(0,5),(0,6),(0,7),(1,4),(2,4),(3,4)]}

def main():
    p=argparse.ArgumentParser();p.add_argument('--and-count',type=int,required=True);p.add_argument('--seconds',type=int,default=30);p.add_argument('--connected',action='store_true')
    a=p.parse_args();group=[]
    for left in itertools.permutations([1,2,3]):
        for right in itertools.permutations([5,6,7]):
            for swap in [False,True]:
                perm=[0,*left,4,*right]
                if swap:perm=[(x+4)%8 for x in perm]
                assert {tuple(sorted((perm[u],perm[v]))) for u,v in EDGES}==EDGES
                assert {perm[0],perm[4]}=={0,4}
                group.append(perm)
    pairs=list(itertools.combinations(range(8),2))
    representatives=sorted({min(tuple(sorted((p[u],p[v]))) for p in group) for u,v in pairs})
    assert len(group)==72 and len(representatives)==5
    print(json.dumps({'group_size':len(group),'pair_orbit_representatives':representatives,'and_count':a.and_count,'seconds_per_case':a.seconds,'all_gates_used':a.connected}),flush=True)
    results=[]
    for op in [0,1]:
        for u,v in representatives:
            key='double-star-9-and'+str(a.and_count)+'-orbit'+ '-'.join(map(str,[op,u,v]))+('-connected' if a.connected else '')
            args=[sys.executable,str(SCRATCH/'double_star_search_v4.py'),'--gates','9','--seconds',str(a.seconds),'--defect','--basis','--and-count',str(a.and_count),'--first',','.join(map(str,[op,u,v]))]
            if a.connected:args.append('--connected')
            with (SCRATCH/(key+'.log')).open('w') as out:
                code=subprocess.run(args,stdout=out,stderr=subprocess.STDOUT).returncode
            raw=(SCRATCH/(key+'.log')).read_text()
            print(json.dumps({'log':key+'.log','process_code':code,'summary':raw.strip()}),flush=True)
            if code==0:
                rec=json.loads(raw);results.append(rec)
                if rec['solver_code']==10:break
        if results and results[-1]['solver_code']==10:break
    print(json.dumps({'completed':len(results),'unsat':sum(r['solver_code']==20 for r in results),'sat':sum(r['solver_code']==10 for r in results),'unknown':sum(r['solver_code'] not in [10,20] for r in results),'all_cases_unsat':len(results)==10 and all(r['solver_code']==20 for r in results)}),flush=True)

if __name__=='__main__':main()
