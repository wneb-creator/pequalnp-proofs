import hashlib,json,re
from pathlib import Path

BASE=Path('results/orch/lemmas/lean_baseline/sat')

def main():
    assigned=json.loads(Path('/tmp/oec/pequalnp-pilot-57/assigned-gap.json').read_text())
    statement=assigned['gap']['statement']
    assert hashlib.sha256(statement.strip().encode()).hexdigest()=='2f423a13954b274d19d1c8766b82e12bb5ea843a124eebfdc6e995defee5b630'
    edges=sorted({(int(a),int(b)) for a,b in re.findall(r'\((\d+),\s*(\d+)\)',statement)})
    assert len(edges)==52 and all(0<=a<13<=b<26 for a,b in edges)
    adjacent=[sum(1<<(b-13) for a,b in edges if a==point) for point in range(13)]
    assert all(mask.bit_count()==4 for mask in adjacent)
    negatives=set()
    for left in range(1<<13):
        neighbors=0
        for point in range(13):
            if left>>point&1:neighbors|=adjacent[point]
        allowed=((1<<13)-1)^neighbors
        closure=sum(1<<point for point in range(13) if not adjacent[point]&allowed)
        mask=closure|(allowed<<13)
        assert not any(mask>>a&1 and mask>>b&1 for a,b in edges)
        for vertex in range(26):
            if not mask>>vertex&1:
                assert any((a==vertex and mask>>b&1) or (b==vertex and mask>>a&1) for a,b in edges)
        negatives.add(mask)
    assert len(negatives)==704
    tests=[{'mask':(1<<a)|(1<<b),'label':1} for a,b in edges]
    tests.extend({'mask':mask,'label':0} for mask in sorted(negatives))
    problem={'inputs':26,'edges':edges,'tests':tests,'input_original':list(range(26)),
             'boundary_complete':True,'boundary_method':'all13-left-subset closed maximal independent sets'}
    (BASE/'and_skeleton_full_data.json').write_text(json.dumps(problem))
    gates=[{'left':[point],'right':[b for a,b in edges if a==point]} for point in range(13)]
    baseline={'inputs':26,'and_gates':gates,'output':list(range(26,39)),'edges':edges,
              'input_original':list(range(26)),'and_count':13,'exact_boundary_verified':True,
              'full_truth_verified':False,'dirty_input':None,'calibration':True,
              'status':'exact AND13 baseline skeleton; no claimed total gate bound'}
    (BASE/'and_skeleton_baseline13.json').write_text(json.dumps(baseline))
    print('generated52positive/704maxnegative completebasis andAND13starbaseline')

if __name__=='__main__':main()
