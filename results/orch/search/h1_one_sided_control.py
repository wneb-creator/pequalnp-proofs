import json


def run():
    gates = [(1,1,3), (0,0,4), (0,1,2), (1,5,6),
             (0,2,3), (1,7,8), (1,7,9)]
    edges = [(0,2),(1,3)]
    mixed = [(1<<0)|(1<<3),(1<<1)|(1<<2)]
    def values(mask):
        vals=[bool(mask&(1<<i)) for i in range(4)]
        for op,a,b in gates:
            assert a != b and 0 <= min(a,b) and max(a,b) < len(vals)
            vals.append((vals[a] and vals[b]) if op else (vals[a] or vals[b]))
        return vals
    for mask in range(16):
        vals=values(mask)
        graph=any(mask&(1<<a) and mask&(1<<b) for a,b in edges)
        point_block=(mask&3)==3
        assert vals[7] == bool(graph or point_block)
        assert vals[9] == bool(graph)
        assert vals[10] == bool(graph)
    assert all(values((1<<a)|(1<<b))[7] for a,b in edges)
    assert all(not values(mask)[7] for mask in mixed)
    assert not values(12)[7]
    assert values(3)[7]
    assert all(not values(1<<i)[7] for i in range(4))
    derivatives=[]
    for a,b in edges:
        edge_values=[]
        for base,seed in [(a,b),(b,a)]:
            vals=values(1<<base)
            d=[i==seed for i in range(4)]
            for op,u,v in gates:
                d.append(((vals[u] and d[v]) or (d[u] and vals[v]))
                         if op else (d[u] or d[v]))
            assert not d[10]
            edge_values.append(d[10])
        derivatives.append(edge_values)
    return dict(inputs=4, factor_gates=4, wrapper_gates=3, total_gates=len(gates),
                gates=gates, factor_output=7, line_or=8, exact_output=9, final_output=10,
                checked_assignments=16, edges=edges, mixed_maximal_independent_sets=mixed,
                pure_line_rejected=True, pure_point_blocking_accepted=True,
                directional_derivatives=derivatives, plane_factor_constructed=False)


if __name__ == '__main__':
    print(json.dumps(run(),indent=2))
