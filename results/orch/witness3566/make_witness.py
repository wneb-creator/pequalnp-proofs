#!/usr/bin/env python3
import argparse
import json
from pathlib import Path


def render(data, strategy='kernel'):
    helper_source = Path(__file__).with_name('GraphSemantics.lean').read_text()
    namespace = 'PEqualNP.Outside.L_meta_3566'
    graph_helpers = helper_source.split(f'namespace {namespace}', 1)[1].rsplit(
        f'end {namespace}', 1)[0].strip()
    n = data['n']
    gates = data['gates']
    edges = data['edges']
    assert type(n) is int and 0 < n <= 32
    assert len(gates) == data['size']
    assert all(type(u) is int and type(v) is int and 0 <= u < n and
               0 <= v < n and u != v for u, v in edges)
    for j, (op, a, b) in enumerate(gates):
        assert op in ('and', 'or')
        assert type(a) is int and type(b) is int and 0 <= a < n+j and 0 <= b < n+j
    output = data.get('output', n + len(gates) - 1)
    assert type(output) is int and 0 <= output < n+len(gates)
    bool_args = ' '.join(f'b{i}' for i in range(n))
    x_args = ' '.join(f'(x {i})' for i in range(n))
    edge_list = ', '.join(f'({u}, {v})' for u, v in edges)
    circuit_gates = ',\n    '.join(f'⟨.{op}, [{a}, {b}]⟩' for op, a, b in gates)
    wire_name = lambda w: f'b{w}' if w < n else f'g{w-n}'
    expr_lines = '\n'.join(f'  let g{j} := {wire_name(a)} '
                           f'{"&&" if op == "and" else "||"} {wire_name(b)}'
                           for j, (op, a, b) in enumerate(gates))
    graph_expr = ' || '.join(f'(b{u} && b{v})' for u, v in edges) or 'false'
    local_wire = lambda w: f'(x {w})' if w < n else f'g{w-n}'
    local_expr = '\n'.join(f'  let g{j} := {local_wire(a)} '
                          f'{"&&" if op == "and" else "||"} {local_wire(b)}'
                          for j, (op, a, b) in enumerate(gates))
    wire_list = lambda count: '[' + ', '.join(
        [f'x {i}' for i in range(n)] + [f'g{j}' for j in range(count)]) + ']'
    wire_steps = '\n'.join(
        f'  have h{j} : witnessStep {wire_list(j)} ⟨.{op}, [{a}, {b}]⟩ =\n'
        f'      {wire_list(j+1)} := by rw [witnessStep_{op}]; rfl'
        for j, (op, a, b) in enumerate(gates))
    wire_rewrites = '\n'.join(f'  rw [List.foldl_cons, h{j}]' for j in range(len(gates)))
    if strategy == 'kernel':
        formula_proof = f'  revert {bool_args}\n  decide +kernel'
    else:
        formula_proof = '''  simp [witnessExpr, witnessGraphExpr, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
    Bool.and_assoc, Bool.and_comm, Bool.and_left_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]'''
    return f'''import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

{graph_helpers}

abbrev witnessGraph : SimpleGraph (Fin {n}) :=
  PEqualNP.EdgeOwnership.edgeGraph {n} [{edge_list}]

def witnessCircuit : Circuit :=
  ⟨[{circuit_gates}], {output}⟩

def witnessExpr ({bool_args} : Bool) : Bool :=
{expr_lines}
  {wire_name(output)}

def witnessGraphExpr ({bool_args} : Bool) : Bool :=
  {graph_expr}

def witnessStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem witnessStep_and (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.and, [a, b]⟩ = w ++ [w.getD a false && w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witnessStep_or (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.or, [a, b]⟩ = w ++ [w.getD a false || w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witness_ao : PEqualNP.TopForm.IsAO2 {n} witnessCircuit := by
  decide

theorem witness_size : witnessCircuit.size = {len(gates)} := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_formula ({bool_args} : Bool) :
    witnessExpr {bool_args} = witnessGraphExpr {bool_args} := by
{formula_proof}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_eval (x : Fin {n} → Bool) :
    circuitFun {n} witnessCircuit x = witnessExpr {x_args} := by
{local_expr}
  have hinput : List.ofFn x = {wire_list(0)} := by rfl
{wire_steps}
  unfold circuitFun Circuit.eval Circuit.wires witnessCircuit
  change (List.foldl witnessStep (List.ofFn x) _).getD {output} false = _
  rw [hinput]
{wire_rewrites}
  rw [List.foldl_nil]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_graph_eval (x : Fin {n} → Bool) :
    graphFun witnessGraph ∅ x = witnessGraphExpr {x_args} := by
  have hv : ∀ e ∈ ([{edge_list}] : List (ℕ × ℕ)),
      e.1 < {n} ∧ e.2 < {n} ∧ e.1 ≠ e.2 := by decide
  rw [edgeList_graph_eval {n} _ hv x]
  simp [witnessGraphExpr, List.getD_eq_getElem?_getD, Bool.or_assoc]

theorem witness_correct : circuitFun {n} witnessCircuit = graphFun witnessGraph ∅ := by
  funext x
  rw [witness_eval, witness_graph_eval]
  exact witness_formula {x_args}

end PEqualNP.Outside.L_meta_3566
'''


def main():
    p = argparse.ArgumentParser(description='Generate a kernel-checked Lean witness proof.')
    p.add_argument('json_file', type=Path)
    p.add_argument('lean_file', type=Path)
    p.add_argument('--strategy', choices=['simp', 'kernel'], default='kernel')
    args = p.parse_args()
    data = json.loads(args.json_file.read_text())
    args.lean_file.write_text(render(data, args.strategy))
    print(f'Generated {args.lean_file}: n={data["n"]}, gates={data["size"]}')


if __name__ == '__main__':
    main()
