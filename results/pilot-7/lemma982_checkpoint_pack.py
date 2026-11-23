"""Pack upper checkpoint layers; lower continuations are checked by rejectDepth.

This is certificate data generation only.  Every emitted state is reconstructed
from an incoming parent transition and checked against the original full table.
No original data or proof files are changed.
"""
import argparse
import itertools
import json
from pathlib import Path


def width(n):
    return max(0, (n - 1).bit_length())


def packed(values, bits):
    assert bits > 0 and all(0 <= v < 1 << bits for v in values)
    block = max(1, 1024 // bits)
    chunks = [sum(v << (bits * j) for j, v in enumerate(values[i:i+block]))
              for i in range(0, len(values), block)]
    decoded = [(chunks[i // block] >> ((i % block) * bits)) % (1 << bits)
               for i in range(len(values))]
    assert decoded == values
    return {"width": bits, "block": block, "count": len(values),
            "hex": [hex(c) for c in chunks]}


def step(mask, state, tag):
    if tag < 48:
        i, op = divmod(tag, 4)
        assert op in (2, 3)
        a = state[i]
        return [a ^ mask] + ([a] if op == 3 else []) + state[:i] + state[i+1:]
    x, op = divmod(tag - 48, 8)
    b = 0
    while (b+1)*(b+2)//2 <= x:
        b += 1
    a = x - b*(b+1)//2
    assert a < b < len(state)
    meet, keep = divmod(op, 4)
    va, vb = state[a], state[b]
    val = va & vb if meet else va | vb
    return ([val] + ([va] if keep & 2 else []) + ([vb] if keep & 1 else [])
            + [v for i, v in enumerate(state) if i not in (a, b)])


def transport(k, p, word):
    return (sum(((word >> p[j]) & 1) << j for j in range(k))
            | sum(((word >> (k+p[j])) & 1) << (k+j) for j in range(k)))


def group_recipes(permutations):
    """A minimum-cardinality generating family, with exact composition replay."""
    count = len(permutations)
    k = len(permutations[0])
    assert permutations[0] == list(range(k))
    lookup = {tuple(p): i for i, p in enumerate(permutations)}
    assert len(lookup) == count
    composition = [[lookup[tuple(a[b[j]] for j in range(k))]
                    for b in permutations] for a in permutations]
    def closure(gens):
        order, seen, recipes = [0], {0: 0}, []
        for parent, a in enumerate(order):
            for j, b in enumerate(gens):
                z = composition[a][b]
                if z not in seen:
                    seen[z] = len(order)
                    order.append(z)
                    recipes.append((parent, j))
        return order, seen, recipes
    gens = []
    order, refs, recipes = closure(gens)
    for size in range(1, count):
        if len(order) == count:
            break
        for candidate in itertools.combinations(range(1, count), size):
            order, refs, recipes = closure(candidate)
            if len(order) == count:
                gens = list(candidate)
                break
    assert len(order) == count
    replay = [list(range(k))]
    for parent, g in recipes:
        replay.append([replay[parent][j] for j in permutations[gens[g]]])
    assert [replay[refs[i]] for i in range(count)] == permutations
    pw, gw = width(count), width(max(1, len(gens)))
    return dict(generators=gens, order=order,
                generator_data=packed([v for g in gens for v in permutations[g]], width(k)),
                recipe_data=packed([p+(g << pw) for p, g in recipes], max(1, pw+gw)),
                reference_data=packed([refs[i] for i in range(count)], max(1, pw)),
                parent_width=pw, generator_width=gw,
                all_compositions_exact=True)


def pack_core(path, depth):
    data = json.loads(path.read_text())
    # A max-budget certificate suffices.  Discard components included only for
    # smaller original roots before assigning dense parent/child indices.
    original_states, original_advice = data["states"], data["advice"]
    maximum = len(original_states)-1
    reachable = [set() for _ in original_states]
    maximum_roots = [i for s, i in data["roots"] if s == maximum]
    assert maximum_roots == [0]
    reachable[maximum].add(0)
    for s in range(maximum, 0, -1):
        for i in reachable[s]:
            for entry in original_advice[s][i]:
                reachable[s-1].add((entry//1024-1)//64)
    remap = [{old: new for new, old in enumerate(sorted(layer))} for layer in reachable]
    data["states"] = [[original_states[s][i] for i in sorted(layer)]
                      for s, layer in enumerate(reachable)]
    data["advice"] = [
        [[entry % 1024 + 1024*(1+(entry//1024-1)%64
                              +64*remap[s-1][(entry//1024-1)//64])
          for entry in original_advice[s][i]] for i in sorted(layer)]
        for s, layer in enumerate(reachable)]
    states, advice = data["states"], data["advice"]
    budget, k = len(states)-1, data["K"]
    cut = max(0, budget-depth)
    words = [int(w, 16) for w in data["encoded_words_hex"]]
    exact = [[[words[i] for i in row] for row in layer] for layer in states]
    counts = list(map(len, states))
    gwidth = width(len(data["vertex_perms"]))
    mask = (1 << (2*k)) - 1
    incoming = [{} for _ in states]
    for s in range(cut+1, budget+1):
        for parent, row in enumerate(advice[s]):
            for entry in row:
                tag = entry % 1024
                payload = entry // 1024 - 1
                symmetry, child = payload % 64, payload // 64
                incoming[s-1].setdefault(child, (parent, tag, symmetry))
    recipes = {}
    for s in range(budget-1, cut-1, -1):
        assert len(incoming[s]) == counts[s]
        pw = width(counts[s+1])
        tw = max(1, max((tag.bit_length() for _, tag, _ in incoming[s].values()), default=1))
        values = []
        for i in range(counts[s]):
            parent, tag, g = incoming[s][i]
            reconstructed = sorted(transport(k, data["pair_perms"][g], w)
                                   for w in step(mask, exact[s+1][parent], tag))
            assert reconstructed == exact[s][i], (data["case"], s, i)
            code = parent + (tag + (g << tw)) * (1 << pw)
            assert code % (1 << pw) == parent
            assert (code >> pw) % (1 << tw) == tag
            assert code >> (pw+tw) == g
            values.append(code)
        recipes[str(s)] = dict(parent_width=pw, symmetry_width=gwidth, tag_width=tw,
                              packed=packed(values, pw+tw+gwidth))
    packed_advice = {}
    for s in range(cut+1, budget+1):
        cw = width(counts[s-1])
        tw = max(1, max(((entry % 1024).bit_length() for row in advice[s] for entry in row), default=1))
        values, lengths = [], []
        for row in advice[s]:
            lengths.append(len(row))
            for entry in row:
                tag = entry % 1024
                payload = entry // 1024 - 1
                symmetry, child = payload % 64, payload // 64
                value = tag + ((symmetry + (child << gwidth)) << tw)
                recovered = value % (1 << tw) + 1024*(1+(value >> tw) % (1 << gwidth)
                            +64*(value >> (tw+gwidth)))
                assert recovered == entry
                values.append(value)
        packed_advice[str(s)] = dict(child_width=cw, symmetry_width=gwidth, tag_width=tw,
            lengths=packed(lengths, max(1, max(lengths, default=0).bit_length())),
            packed=packed(values, tw+gwidth+cw))
    assert data["pair_perms"][0] == list(range(k))
    metadata = {
        "rows": packed(data["paired_rows"], data["n"]),
        "pool": packed(data["score_pool_codes"], 60),
        "group": group_recipes(data["pair_perms"]),
        "vertex_perms": packed([v for p in data["vertex_perms"] for v in p], width(data["n"])),
        "inputs": data["inputs_hex"],
        "root_indices": packed([data["inputs_hex"].index(hex(w))
                                for w in exact[budget][0]], width(data["n"])),
    }
    # Count how much repeated work direct DFS below the checkpoint introduces.
    visits = [[0] * len(layer) for layer in states]
    visits[cut] = [1] * len(states[cut])
    for s in range(cut, 0, -1):
        for i, row in enumerate(advice[s]):
            for entry in row:
                visits[s-1][(entry//1024-1)//64] += visits[s][i]
    result = dict(case=data["case"], n=data["n"], K=k, budget=budget, cut=cut,
        counts=counts, symmetry_count=len(data["vertex_perms"]), recipes=recipes,
        advice=packed_advice, metadata=metadata,
        checkpoint_dfs_visits=sum(sum(layer) for layer in visits),
        original_states=sum(counts), retained_states=sum(counts[cut:]),
        retained_advice=sum(len(row) for layer in advice[cut+1:] for row in layer))
    return result


def emit_data(result):
    """Emit compact data declarations; decoder API is documented in the JSON."""
    c = result["case"]
    lines = ["namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData"]
    def decl(name, p):
        lines.append(f"def c{c}{name} : Array Nat := #[" + ",".join(p["hex"]) + "]")
        lines.append(f"def c{c}{name}Info : Nat × Nat × Nat := "
                     f"({p['width']},{p['block']},{p['count']})")
    for s, rec in result["recipes"].items():
        decl("R"+s, rec["packed"])
    for s, adv in result["advice"].items():
        decl("A"+s, adv["packed"])
        decl("L"+s, adv["lengths"])
    for name in ["rows", "pool", "vertex_perms", "root_indices"]:
        decl(name, result["metadata"][name])
    for name in ["generator_data", "recipe_data", "reference_data"]:
        decl(name, result["metadata"]["group"][name])
    for name in ["inputs"]:
        lines.append(f"def c{c}{name} : List Nat := [" + ",".join(result["metadata"][name]) + "]")
    m = result["metadata"]
    g = m["group"]
    gd, rd, refs = g["generator_data"], g["recipe_data"], g["reference_data"]
    lines.append("open PEqualNP.Outside.L_meta_982_aux.Checkpoint")
    lines.append(f"def c{c}K : Nat := {result['K']}")
    lines.append(f"def c{c}Mask : Nat := 2^(c{c}K+c{c}K)-1")
    lines.append(f"def c{c}Gens := generators c{c}K {len(g['generators'])} "
                 f"{gd['width']} {gd['block']} c{c}generator_data")
    lines.append(f"def c{c}Perms := actions {refs['width']} {refs['block']} {result['symmetry_count']} "
                 f"c{c}reference_data (group c{c}K {g['parent_width']} {rd['width']} {rd['block']} "
                 f"{rd['count']} c{c}Gens c{c}recipe_data)")
    for name in ["rows", "pool"]:
        p = m[name]
        lines.append(f"def c{c}{name.title()} := values {p['width']} {p['block']} c{c}{name} {p['count']}")
    p = m["root_indices"]
    lines.append(f"def c{c}Root := (values {p['width']} {p['block']} c{c}root_indices {p['count']}).map "
                 f"(c{c}inputs.getD · 0)")
    b, cut = result["budget"], result["cut"]
    lines.append(f"def c{c}S{b} (i : Nat) := if i=0 then c{c}Root else []")
    for s in range(b-1, cut-1, -1):
        rec = result["recipes"][str(s)]
        p = rec["packed"]
        lines.append(f"def c{c}S{s} := state c{c}K c{c}Mask {rec['parent_width']} {rec['tag_width']} {p['width']} {p['block']} "
                     f"c{c}Perms c{c}S{s+1} c{c}R{s}")
    lines.append(f"def c{c}States (s i : Nat) : List Nat := match s with")
    for s in range(cut, b+1):
        if result["counts"][s]: lines.append(f"| {s} => c{c}S{s} i")
    lines.append("| _ => []")
    lines.append(f"def c{c}Count (s : Nat) : Nat := match s with")
    for s in range(cut, b+1):
        if result["counts"][s]: lines.append(f"| {s} => {result['counts'][s]}")
    lines.append("| _ => 0")
    lines.append(f"def c{c}Advice (s i : Nat) : Array Nat := match s with")
    for s in range(cut+1, b+1):
        if not result["counts"][s]: continue
        adv = result["advice"][str(s)]
        p, q = adv["packed"], adv["lengths"]
        lines.append(f"| {s} => advice {adv['tag_width']} {adv['symmetry_width']} {q['width']} {q['block']} {p['width']} {p['block']} "
                     f"c{c}L{s} c{c}A{s} i")
    lines.append("| _ => #[]")
    lines.append("end PEqualNP.Outside.L_meta_982_aux.CheckpointData")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--case", type=int)
    parser.add_argument("--directory", type=Path, default=Path('/tmp/oec/pequalnp-pilot-7'))
    args = parser.parse_args()
    paths = ([(args.directory/f'term-context-982-seed{args.case}-reduced-data.json'
               if args.case in (0, 8) else args.directory/f'root982-core{args.case}-data.json')]
             if args.case is not None
             else sorted(args.directory.glob('root982-core*-data.json')))
    totals = {"source_bytes": 0, "retained_states": 0, "retained_advice": 0,
              "checkpoint_dfs_visits": 0}
    summaries = []
    for path in paths:
        result = pack_core(path, args.depth)
        source = emit_data(result)
        prefix = args.directory/f'lemma982-checkpoint{args.depth}-core{result["case"]}'
        prefix.with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
        prefix.with_suffix('.lean').write_text(source)
        summary = {k:result[k] for k in ["case", "cut", "original_states", "retained_states",
                                       "retained_advice", "checkpoint_dfs_visits"]}
        summary["source_bytes"] = len(source.encode())
        for k in totals: totals[k] += summary[k]
        summaries.append(summary)
        print(json.dumps(summary), flush=True)
    report = dict(depth=args.depth, totals=totals, cores=summaries,
                  all_state_recipe_reconstructions_exact=True,
                  all_packed_streams_round_trip=True,
                  lean_decoder_not_yet_checked=True)
    (args.directory/f'lemma982-checkpoint{args.depth}-report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({"totals": totals}), flush=True)


if __name__ == '__main__':
    main()
