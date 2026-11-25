"""Emit exact polynomial certificates; no geometric completeness claim."""

import argparse
import json
from pathlib import Path
import sympy as sp


def lean(expr):
    if expr.is_Integer:
        return str(expr) if expr >= 0 else "(" + str(expr) + ")"
    if expr.is_Symbol:
        return str(expr)
    if expr.is_Add:
        return "(" + " + ".join(lean(term) for term in expr.args) + ")"
    if expr.is_Mul:
        return "(" + " * ".join(lean(term) for term in expr.args) + ")"
    if expr.is_Pow and expr.exp.is_Integer and expr.exp >= 0:
        return "(" + lean(expr.base) + " ^ " + str(expr.exp) + ")"
    raise ValueError(expr)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    args = parser.parse_args()
    records = json.loads(Path(args.input).read_text())[:2]
    r, s, t, u = sp.symbols("r s t u")
    variables = (r, s, t, u)
    lines = ["import PEqualNP.Defs", "", "set_option maxHeartbeats 2000000", "",
             "namespace PEqualNP.Outside.L_gct_231.rowzero", ""]
    for record in records:
        equations = [sp.expand(sp.sympify(p).subs(sp.I, r/sp.sqrt(2)))
                     for p in record["equations"]]
        multipliers = [sp.expand(sp.sympify(p).subs(sp.I, r/sp.sqrt(2)))
                       for p in record["multipliers"]]
        denominator = sp.ilcm(*[sp.denom(c) for p in multipliers
                               for c in sp.Poly(p, *variables).coeffs()])
        integers = [sp.expand(denominator*p) for p in multipliers]
        expression = sp.expand(sum(h*f for h, f in zip(integers, equations)) - denominator)
        quotient, remainder = sp.div(expression, r*r+2, r)
        assert remainder == 0
        assert all(c.is_Integer for p in equations+integers+[quotient]
                   for c in sp.Poly(p, *variables).coeffs())
        name = "even_chart_empty" if record["chart"] == 0 else "odd_chart_empty"
        lines.append("lemma " + name + " (r s t u : ℂ) (hr : r ^ 2 + 2 = 0)")
        for i, polynomial in enumerate(equations):
            lines.append("    (h"+str(i)+" : "+lean(polynomial)+" = 0)")
        lines.append("    : False := by")
        lines.append("  have hbad : ("+str(denominator)+" : ℂ) = 0 := by")
        terms = ["("+lean(h)+") * h"+str(i) for i, h in enumerate(integers) if h != 0]
        terms.append("(-("+lean(quotient)+")) * hr")
        lines.append("    linear_combination " + " + ".join(terms))
        lines.append("  norm_num at hbad")
        lines.append("")
        print(json.dumps({"chart": record["chart"], "integer_denominator": str(denominator),
                          "certificate_identity_verified": True}))
    lines.append("end PEqualNP.Outside.L_gct_231.rowzero")
    Path(args.output).write_text("\n".join(lines)+"\n")


if __name__ == "__main__":
    main()
