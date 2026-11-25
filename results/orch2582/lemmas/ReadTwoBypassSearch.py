"""Finite AO2 synthesis with the exact joint READ-2 count-vector recurrence.

This is an external search, not a Lean proof. Count pairs with either entry
above two can be discarded because later AND additions cannot decrease them.
The optional no-bypass predicate requires replacing any one gate by either
operand to change the final function. No color condition is imposed.
"""

import argparse
import ctypes
import itertools
import json
import re
import time


def get_graph(name):
    if name == "p4":
        return 2, 2, {(0, 2), (0, 3), (1, 3)}
    if name == "cycle6":
        return 3, 3, {(0, 3), (0, 4), (1, 4), (1, 5), (2, 5), (2, 3)}
    if name == "theta8":
        return 4, 4, {(0, 4), (0, 5), (0, 6), (1, 4), (1, 7),
                      (2, 5), (2, 7), (3, 6), (3, 7)}
    raise ValueError(name)


def validate(p, l, edges, gates, require_bad):
    n = p + l
    assert all(0 <= a < p and p <= b < n for a, b in edges)
    assert all(not all((a, b) in edges for a in aa for b in bb)
               for aa in itertools.combinations(range(p), 2)
               for bb in itertools.combinations(range(p, n), 2))
    for g, (a, b, op) in enumerate(gates):
        assert 0 <= a <= b < n + g and op in (0, 1)
    for x in range(1 << n):
        values = [bool(x >> a & 1) for a in range(n)]
        for a, b, op in gates:
            values.append(values[a] | values[b] if op else values[a] & values[b])
        assert values[-1] == any(x >> a & 1 and x >> b & 1 for a, b in edges), x
    bad = []
    read_sets = {}
    for u, v in sorted(edges):
        vectors = [{(1, 0)} if a == u else {(0, 1)} if a == v else set()
                   for a in range(n)]
        for a, b, op in gates:
            if op:
                vectors.append(vectors[a] | vectors[b])
            else:
                vectors.append({(x + xx, y + yy)
                                for x, y in vectors[a] for xx, yy in vectors[b]
                                if x + xx <= 2 and y + yy <= 2})
        read_sets[str((u, v))] = sorted(vectors[-1])
        if not vectors[-1]:
            bad.append((u, v))
    assert not require_bad or bad, "claimed non-READ-2 circuit is READ-2"
    return {"non_read2_edges": bad, "joint_read2_vectors": read_sets,
            "full_truth_table_validated": 1 << n}


def bypass_witnesses(p, l, edges, gates):
    witnesses = {}
    for omitted in range(len(gates)):
        for side in (0, 1):
            found = None
            for x in range(1 << (p + l)):
                values = [bool(x >> a & 1) for a in range(p + l)]
                for g, (a, b, op) in enumerate(gates):
                    if g == omitted:
                        values.append(values[a if side == 0 else b])
                    else:
                        values.append(values[a] | values[b] if op else values[a] & values[b])
                target = any(x >> a & 1 and x >> b & 1 for a, b in edges)
                if values[-1] != target:
                    found = x
                    break
            assert found is not None, (omitted, side, "output-preserving bypass")
            witnesses[str((omitted, side))] = found
    return witnesses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", choices=("p4", "cycle6", "theta8"))
    parser.add_argument("gates", type=int)
    parser.add_argument("seconds", type=int)
    parser.add_argument("--non-read2", action="store_true")
    parser.add_argument("--no-bypass", action="store_true")
    parser.add_argument("--fixed-p4", action="store_true",
                        help="Fix the five-gate P4 repetition sanity circuit.")
    args = parser.parse_args()
    p, l, edges = get_graph(args.graph)
    n, k = p + l, args.gates
    assert k > 0 and args.seconds > 0
    target = lambda x: any(x >> a & 1 and x >> b & 1 for a, b in edges)
    positive = sorted((1 << a) | (1 << b) for a, b in edges)
    negative = [x for x in range(1 << n) if not target(x) and
                all(target(x | (1 << a)) for a in range(n) if not x >> a & 1)]
    samples = positive + negative
    m, width = len(samples), (n + k).bit_length()
    bv = lambda x, w: f"(_ bv{x} {w})"

    def select(values, variable):
        result = values[-1]
        for i in reversed(range(len(values) - 1)):
            result = f"(ite (= {variable} {bv(i, width)}) {values[i]} {result})"
        return result

    def joint_and(a, b):
        bits = []
        for total in reversed(range(9)):
            x, y = divmod(total, 3)
            terms = []
            for i in range(x + 1):
                for j in range(y + 1):
                    left, right = 3 * i + j, 3 * (x - i) + y - j
                    terms.append(f"(and (= ((_ extract {left} {left}) {a}) #b1) "
                                 f"(= ((_ extract {right} {right}) {b}) #b1))")
            condition = terms[0] if len(terms) == 1 else "(or " + " ".join(terms) + ")"
            bits.append(f"(ite {condition} #b1 #b0)")
        result = bits[-1]
        for bit in reversed(bits[:-1]):
            result = f"(concat {bit} {result})"
        return result

    lines = [f"(set-option :timeout {args.seconds * 1000})",
             "(set-option :memory_max_size 2048)", "(set-logic QF_BV)"]
    values = [bv(sum((x >> a & 1) << s for s, x in enumerate(samples)), m)
              for a in range(n)]
    reads = [[bv(1 << 3 if a == u else 1 << 1 if a == v else 0, 9)
              for a in range(n)] for u, v in sorted(edges)]
    for g in range(k):
        lines += [f"(declare-fun a{g} () (_ BitVec {width}))",
                  f"(declare-fun b{g} () (_ BitVec {width}))",
                  f"(declare-fun o{g} () Bool)",
                  f"(assert (bvule a{g} b{g}))",
                  f"(assert (bvult b{g} {bv(n + g, width)}))"]
        for side in "ab":
            lines.append(f"(define-fun {side}v{g} () (_ BitVec {m}) "
                         f"{select(values, side + str(g))})")
        lines.append(f"(define-fun v{g} () (_ BitVec {m}) "
                     f"(ite o{g} (bvand av{g} bv{g}) (bvor av{g} bv{g})))")
        values.append(f"v{g}")
        if args.non_read2:
            for e, vectors in enumerate(reads):
                for side in "ab":
                    lines.append(f"(define-fun {side}r{e}_{g} () (_ BitVec 9) "
                                 f"{select(vectors, side + str(g))})")
                ar, br, rr = f"ar{e}_{g}", f"br{e}_{g}", f"r{e}_{g}"
                lines.append(f"(define-fun {rr} () (_ BitVec 9) (ite o{g} "
                             f"{joint_and(ar, br)} (bvor {ar} {br})))")
                vectors.append(rr)
    for g in range(k - 1):
        uses = [f"(= {side}{h} {bv(n + g, width)})"
                for h in range(g + 1, k) for side in "ab"]
        lines.append("(assert (or " + " ".join(uses) + "))")
    lines.append(f"(assert (= v{k - 1} {bv((1 << len(positive)) - 1, m)}))")
    if args.non_read2:
        lines.append("(assert (or " + " ".join(
            f"(= r{e}_{k - 1} {bv(0, 9)})" for e in range(len(edges))) + "))")
    if args.no_bypass:
        wanted = bv((1 << len(positive)) - 1, m)
        for omitted in range(k):
            for side in "ab":
                shadow = values[:n + omitted]
                shadow.append(select(shadow, side + str(omitted)))
                for h in range(omitted + 1, k):
                    prefix = f"s{omitted}_{side}_{h}"
                    for operand in "ab":
                        lines.append(f"(define-fun {prefix}{operand} () (_ BitVec {m}) "
                                     f"{select(shadow, operand + str(h))})")
                    ar, br, rr = prefix + "a", prefix + "b", prefix + "v"
                    lines.append(f"(define-fun {rr} () (_ BitVec {m}) "
                                 f"(ite o{h} (bvand {ar} {br}) (bvor {ar} {br})))")
                    shadow.append(rr)
                lines.append(f"(assert (not (= {shadow[-1]} {wanted})))")
    if args.fixed_p4:
        assert args.graph == "p4" and k == 5
        fixed = [(1, 3, 0), (0, 4, 1), (2, 3, 1), (5, 6, 0), (6, 7, 0)]
        print("fixed sanity", validate(p, l, edges, fixed, True), flush=True)
        for g, (a, b, op) in enumerate(fixed):
            lines += [f"(assert (= a{g} {bv(a, width)}))",
                      f"(assert (= b{g} {bv(b, width)}))",
                      f"(assert (= o{g} {'false' if op else 'true'}))"]
    smt = "\n".join(lines) + "\n"
    print(json.dumps({"graph": args.graph, "n": n, "gates": k, "edges": sorted(edges),
                      "samples": len(samples), "non_read2": args.non_read2, "no_bypass": args.no_bypass,
                      "smt_bytes": len(smt)}), flush=True)
    z = ctypes.CDLL("/usr/lib/x86_64-linux-gnu/libz3.so.4")
    z.Z3_mk_config.restype = ctypes.c_void_p
    z.Z3_mk_context.argtypes = [ctypes.c_void_p]
    z.Z3_mk_context.restype = ctypes.c_void_p
    z.Z3_del_config.argtypes = [ctypes.c_void_p]
    z.Z3_del_context.argtypes = [ctypes.c_void_p]
    z.Z3_eval_smtlib2_string.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    z.Z3_eval_smtlib2_string.restype = ctypes.c_char_p
    cfg = z.Z3_mk_config()
    ctx = z.Z3_mk_context(cfg)
    z.Z3_del_config(cfg)
    evaluate = lambda text: z.Z3_eval_smtlib2_string(ctx, text.encode()).decode()
    start = time.monotonic()
    result = evaluate(smt + "(check-sat)\n").strip()
    print("result", result, "elapsed", time.monotonic() - start, flush=True)
    if result == "sat":
        names = [f"{side}{g}" for g in range(k) for side in "abo"]
        model = evaluate("(get-value (" + " ".join(names) + "))")
        print(model, flush=True)
        pairs = re.findall(r"\(([abo]\d+)\s+(true|false|#x[0-9a-f]+|#b[01]+|\(_ bv\d+ \d+\))\)", model)

        def decode(value):
            if value in ("true", "false"):
                return value == "true"
            if value.startswith("#x"):
                return int(value[2:], 16)
            if value.startswith("#b"):
                return int(value[2:], 2)
            return int(value.split()[1][2:])

        mapping = {name: decode(value) for name, value in pairs}
        gates = [(mapping[f"a{g}"], mapping[f"b{g}"], 0 if mapping[f"o{g}"] else 1)
                 for g in range(k)]
        print("gates", gates, flush=True)
        print(json.dumps(validate(p, l, edges, gates, args.non_read2)), flush=True)
        if args.no_bypass:
            print("bypass_witnesses", json.dumps(bypass_witnesses(p, l, edges, gates)), flush=True)
    else:
        print(evaluate("(get-info :reason-unknown)"), flush=True)
    z.Z3_del_context(ctx)


if __name__ == "__main__":
    main()
