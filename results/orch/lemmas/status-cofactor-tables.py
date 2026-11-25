"""Finite cofactor tables for the accepted and posted Fano labelings."""
import itertools
import json


ACCEPTED_MASKS = [1408, 8832, 12544, 6272, 11264, 5632, 2816,
                  11, 69, 98, 49, 88, 44, 22]
K4_MASKS = [112, 400, 672, 832, 3, 5, 9, 6, 10, 12]
CYCLIC_PERM = [0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 11, 10, 9, 8]


def adjacent(u, v):
    return bool(ACCEPTED_MASKS[u] & (1 << v))


def tables():
    result = []
    for c in range(14):
        originals = [v for v in range(14)
                     if (v < 7) != (c < 7) and not adjacent(c, v)]
        assert len(originals) == 4
        edge_vertices = []
        for a, b in itertools.combinations(originals, 2):
            common = [v for v in range(14) if adjacent(a, v) and adjacent(b, v)]
            assert len(common) == 1 and common[0] != c
            edge_vertices.extend(common)
        free = originals + edge_vertices
        assert len(set(free)) == 10
        assert set(free) == {v for v in range(14) if v != c and not adjacent(c, v)}
        for i in range(10):
            for j in range(10):
                assert adjacent(free[i], free[j]) == bool(K4_MASKS[i] & (1 << j))
        posted_c = CYCLIC_PERM[c]
        posted_free = [CYCLIC_PERM[v] for v in free]
        posted_originals = posted_free[:4]
        for u in range(14):
            for v in range(14):
                posted_edge = ((u < 7 <= v and u in {(v-7) % 7, (v-6) % 7, (v-4) % 7})
                               or (v < 7 <= u and v in {(u-7) % 7, (u-6) % 7, (u-4) % 7}))
                assert posted_edge == adjacent(CYCLIC_PERM[u], CYCLIC_PERM[v])
        result.append({"accepted_center": c, "accepted_cf_iota": free,
                       "posted_center": posted_c, "posted_cf_iota": posted_free,
                       "posted_free_originals": posted_originals})
    return result


if __name__ == "__main__":
    print(json.dumps({"scope": "Finite graph isomorphisms only; no new circuit theorem or SAT claim.",
                      "source": "Accepted hc_adjB and k4_adjB; checked cyclicPerm/cyclic_incidence bridge.",
                      "count": 14, "tables": tables()}, indent=2))
