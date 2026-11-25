import argparse
import collections
import json
from pathlib import Path
from resynthesize import evaluate
from subset_search import validate_basis


def minimal(terms):
    answer=[]
    for t in sorted(set(terms),key=lambda x:(x.bit_count(),x)):
        if not any(u&t==u for u in answer):answer.append(t)
    return answer


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('case',type=Path)
    parser.add_argument('pool',type=Path)
    parser.add_argument('output',type=Path)
    args=parser.parse_args()
    data=json.loads(args.case.read_text());tests=validate_basis(data)
    edge_masks=[1<<a|1<<b for a,b in data['edges']]
    pool=json.loads(args.pool.read_text());selected=[];stats=collections.Counter()
    for index,item in enumerate(pool):
        gs=item['gates'];wires=[[1<<i] for i in range(data['inputs'])]
        for op,a,b in gs:
            wires.append(minimal(wires[a]+wires[b]) if op else minimal(x|y for x in wires[a] for y in wires[b]))
        terms=wires[-1]
        assert all(any(t&m==t for t in terms)==evaluate(gs,m,data['inputs'])[-1] for m,_ in tests)
        degrees=collections.Counter(t.bit_count() for t in terms)
        if degrees[1]:stats['singleton_output']+=1;continue
        wrong=[t for t in terms if not any(e&t==e for e in edge_masks)]
        higher=sum(v for k,v in degrees.items() if k>=3)
        if not higher and not wrong:stats['plain_graph_minor']+=1;continue
        if higher:stats['higher_prime_terms']+=1
        if wrong:stats['false_prime_terms']+=1
        entry=dict(item)
        entry['prime_degrees']=dict(degrees)
        entry['prime_terms']=terms
        entry['false_prime_terms']=wrong
        entry['source_index']=index
        selected.append(entry)
    args.output.write_text(json.dumps(selected))
    print('Classification',dict(stats),'selected',len(selected),flush=True)
    order=sorted(selected,key=lambda e:e.get('miss',0)+e.get('false',0)/8)
    for item in order[:12]:
        print('seed',item['source_index'],'miss',item.get('miss'),'false',item.get('false'),
              'degrees',item['prime_degrees'],'falseprimedegrees',[t.bit_count() for t in item['false_prime_terms']],flush=True)


if __name__=='__main__':main()
