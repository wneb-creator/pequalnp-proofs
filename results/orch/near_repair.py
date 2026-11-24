import argparse
import itertools
import json
import time

from rectangle_search import Circuit, bits, c4free, edge, mincover, verify


def antichain(terms):
    kept = []
    for t in sorted(set(terms), key=int.bit_count):
        if not any(q & t == q for q in kept):
            kept.append(t)
    return frozenset(kept)


class SemanticCircuit(Circuit):
    def __init__(self, n):
        super().__init__(n)
        self.dnf = [frozenset({1 << i}) for i in range(n)]
        self.known = {f: i for i, f in enumerate(self.dnf)}
        self.known[frozenset()] = -1
        self.known[frozenset({0})] = -2

    def value(self, w):
        return frozenset() if w == -1 else frozenset({0}) if w == -2 else self.dnf[w]

    def gate(self, op, a, b):
        va, vb = self.value(a), self.value(b)
        result = antichain(va | vb) if op == "or" else antichain(x | y for x in va for y in vb)
        if result in self.known:
            return self.known[result]
        assert a >= 0 and b >= 0
        w = super().gate(op, a, b)
        assert w == len(self.dnf)
        self.dnf.append(result)
        self.known[result] = w
        return w


def rebuild(record, edits, n):
    circuit = SemanticCircuit(n)
    mapped = []
    old_n = record["n"]
    for gi, (op, a, b) in enumerate(record["gates"]):
        refs = []
        for side, w in enumerate((a, b)):
            if w < old_n:
                refs.append(edits.get((gi, side), w))
            else:
                refs.append(mapped[w - old_n])
        mapped.append(circuit.gate(op, *refs))
    output = mapped[record["output"] - old_n]
    return circuit, output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source")
    parser.add_argument("--output", required=True)
    parser.add_argument("--max-cofactors", type=int, default=2)
    parser.add_argument("--expose", action="store_true")
    args = parser.parse_args()
    source = json.load(open(args.source))
    n = source["n"]
    occurrences = [(i, j) for i, gate in enumerate(source["gates"])
                   for j, w in enumerate(gate[1:]) if w < n]
    by_vertex = {v: [] for v in range(n)}
    for pos in occurrences:
        by_vertex[source["gates"][pos[0]][pos[1]+1]].append(pos)
    splittable = [ps for ps in by_vertex.values() if len(ps) == 2]
    counts = dict(patterns=0, tested=0, pure_graph=0, c4free=0)
    best = 100
    start = time.time()

    def assess_output(circuit, output, edits, new_n, kind, exposed):
        nonlocal best
        counts["tested"] += 1
        terms = circuit.value(output)
        if not terms or any(t.bit_count() != 2 for t in terms):
            return
        counts["pure_graph"] += 1
        if not c4free(new_n, terms):
            return
        counts["c4free"] += 1
        compact, out = circuit.compact(output)
        cover = mincover(new_n, terms)
        bound = len(terms) + cover.bit_count() - 1
        margin = len(compact.gs) - bound
        if margin < best:
            best = margin
            valid = verify(new_n, terms, compact, out)
            if not valid:
                raise RuntimeError("independent truth-table verification failed")
            result = dict(kind=kind, n=new_n, edits=[list(p)+[v] for p,v in edits.items()],
                          exposed=exposed,
                          edges=sorted(terms), cover=cover, bound=bound,
                          gates=compact.gs, output=out, size=len(compact.gs),
                          margin=margin, verified=valid, counts=counts.copy())
            with open(args.output,"w") as f:
                json.dump(result,f,indent=2)
            print(json.dumps(dict(kind=kind, size=len(compact.gs), bound=bound,
                                  margin=margin, counts=counts.copy())),flush=True)
            if margin < 0:
                raise SystemExit(0)

    def assess(edits, new_n, kind):
        counts["patterns"] += 1
        circuit, output = rebuild(source, edits, new_n)
        assess_output(circuit,output,edits,new_n,kind,[])
        if args.expose:
            output_terms = circuit.value(output)
            candidates = [new_n+j for j,(op,_,_) in enumerate(circuit.gs)
                          if op == "and" and not all(
                              any(q & t == q for q in output_terms)
                              for t in circuit.value(new_n+j))]
            for k in range(1,min(2,len(candidates))+1):
                for exposed in itertools.combinations(candidates,k):
                    new_output = output
                    for w in exposed:
                        new_output = circuit.gate("or",new_output,w)
                    assess_output(circuit,new_output,edits,new_n,kind,list(exposed))

    for mask in range(1 << len(splittable)):
        edits = {}
        new_n = n
        for j, ps in enumerate(splittable):
            if mask >> j & 1:
                edits[ps[1]] = new_n
                new_n += 1
        assess(edits,new_n,"vertex_splits")
    print(json.dumps(dict(stage="splits",counts=counts.copy())),flush=True)
    for k in range(1,args.max_cofactors+1):
        for positions in itertools.combinations(occurrences,k):
            for values in itertools.product([-1,-2],repeat=k):
                assess(dict(zip(positions,values)),n,"local_cofactor")
        print(json.dumps(dict(stage="cofactor",k=k,counts=counts.copy())),flush=True)
    print(json.dumps(dict(final=True,counts=counts,best=best,elapsed=time.time()-start)),flush=True)


if __name__ == "__main__":
    main()
