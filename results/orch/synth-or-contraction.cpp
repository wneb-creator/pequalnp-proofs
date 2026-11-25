#include "cadical.hpp"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <random>
#include <set>
#include <vector>

using namespace std;

// Witness search only. An UNSAT response is not a Lean lower-bound certificate.
// Mode 0 identifies x1 with NOT x0; mode 1 identifies x2 with x0.
// Gates are AND, OR, AND-NOT, NOT-AND; complementation is free in this model.
struct Timer : CaDiCaL::Terminator {
  chrono::steady_clock::time_point end;
  bool terminate() override { return chrono::steady_clock::now() > end; }
};

struct Synth {
  CaDiCaL::Solver solver;
  int variables = 0, gates, mode;
  vector<array<int, 4>> operation;
  vector<vector<int>> left, right;
  set<int> rows;

  int fresh() { return ++variables; }
  void clause(const vector<int>& literals) {
    for (int literal : literals) solver.add(literal);
    solver.add(0);
  }
  void one(const vector<int>& choices) {
    clause(choices);
    for (size_t i = 0; i < choices.size(); ++i)
      for (size_t j = i + 1; j < choices.size(); ++j)
        clause({-choices[i], -choices[j]});
  }
  static bool apply(int op, bool a, bool b) {
    if (op == 0) return a && b;
    if (op == 1) return a || b;
    if (op == 2) return a && !b;
    return !a && b;
  }
  Synth(int count, int target, int seed) : gates(count), mode(target) {
    solver.set("quiet", 1);
    solver.set("seed", seed);
    operation.resize(gates);
    left.resize(gates);
    right.resize(gates);
    for (int i = 0; i < gates; ++i) {
      for (int& v : operation[i]) v = fresh();
      one(vector<int>(operation[i].begin(), operation[i].end()));
      left[i].resize(9 + i);
      right[i].resize(9 + i);
      for (int& v : left[i]) v = fresh();
      for (int& v : right[i]) v = fresh();
      one(left[i]);
      one(right[i]);
      for (int a = 0; a < 9 + i; ++a)
        for (int b = 0; b <= a; ++b)
          clause({-left[i][a], -right[i][b]});
    }
    for (int i = 0; i + 1 < gates; ++i) {
      vector<int> uses;
      for (int j = i + 1; j < gates; ++j) {
        uses.push_back(left[j][9 + i]);
        uses.push_back(right[j][9 + i]);
      }
      clause(uses);
    }
  }
  bool goal(int input) const {
    bool x[10];
    x[0] = (input & 1) != 0;
    if (mode == 0) {
      x[1] = !x[0];
      for (int i = 2; i < 10; ++i) x[i] = ((input >> (i - 1)) & 1) != 0;
    } else {
      x[1] = ((input >> 1) & 1) != 0;
      x[2] = x[0];
      for (int i = 3; i < 10; ++i) x[i] = ((input >> (i - 1)) & 1) != 0;
    }
    const int edges[15][2] = {{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},
      {3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
    for (const auto& edge : edges) if (x[edge[0]] && x[edge[1]]) return true;
    return false;
  }
  void row(int input) {
    if (!rows.insert(input).second) return;
    vector<int> values;
    for (int i = 0; i < gates; ++i) {
      int a = fresh(), b = fresh(), y = fresh();
      for (int j = 0; j < 9 + i; ++j) {
        if (j < 9) {
          clause({-left[i][j], ((input >> j) & 1) ? a : -a});
          clause({-right[i][j], ((input >> j) & 1) ? b : -b});
        } else {
          clause({-left[i][j], -a, values[j - 9]});
          clause({-left[i][j], a, -values[j - 9]});
          clause({-right[i][j], -b, values[j - 9]});
          clause({-right[i][j], b, -values[j - 9]});
        }
      }
      for (int op = 0; op < 4; ++op)
        for (int av = 0; av < 2; ++av)
          for (int bv = 0; bv < 2; ++bv) {
            bool expected = apply(op, av, bv);
            clause({-operation[i][op], av ? -a : a, bv ? -b : b, expected ? y : -y});
          }
      values.push_back(y);
    }
    clause({goal(input) ? values.back() : -values.back()});
  }
  vector<array<int, 3>> model() {
    vector<array<int, 3>> result(gates);
    for (int i = 0; i < gates; ++i) {
      for (int op = 0; op < 4; ++op) if (solver.val(operation[i][op]) > 0) result[i][0] = op;
      for (int j = 0; j < 9 + i; ++j) {
        if (solver.val(left[i][j]) > 0) result[i][1] = j;
        if (solver.val(right[i][j]) > 0) result[i][2] = j;
      }
    }
    return result;
  }
  bool eval(const vector<array<int, 3>>& circuit, int input) const {
    vector<bool> values;
    for (int i = 0; i < 9; ++i) values.push_back((input >> i) & 1);
    for (const auto& gate : circuit) values.push_back(apply(gate[0], values[gate[1]], values[gate[2]]));
    return values.back();
  }
};

int main(int argc, char** argv) {
  int mode = argc > 1 ? atoi(argv[1]) : 0;
  int gates = argc > 2 ? atoi(argv[2]) : 16;
  int budget = argc > 3 ? atoi(argv[3]) : 600;
  int seed = argc > 4 ? atoi(argv[4]) : 0;
  if ((mode != 0 && mode != 1) || gates < 1 || budget < 1) return 2;
  Synth syn(gates, mode, seed);
  mt19937 random(seed);
  for (int x = 0; x < 512; ++x)
    if (x == 0 || x == 511 || (__builtin_popcount((unsigned)x) == 2 && syn.goal(x)) ||
        (__builtin_popcount((unsigned)x) == 4 && !syn.goal(x))) syn.row(x);
  Timer timer;
  syn.solver.connect_terminator(&timer);
  auto start = chrono::steady_clock::now();
  int iteration = 0;
  while (chrono::steady_clock::now() - start < chrono::seconds(budget)) {
    timer.end = min(start + chrono::seconds(budget), chrono::steady_clock::now() + chrono::seconds(60));
    int result = syn.solver.solve();
    cout << "mode " << mode << " gates " << gates << " round " << iteration << " rows " <<
      syn.rows.size() << " result " << result << " seconds " <<
      chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now() - start).count() << endl;
    if (result == 20) return 0;
    if (result == 0) continue;
    auto circuit = syn.model();
    vector<int> errors;
    for (int x = 0; x < 512; ++x) if (syn.eval(circuit, x) != syn.goal(x)) errors.push_back(x);
    cout << "errors " << errors.size() << endl;
    if (errors.empty()) {
      cout << "FOUND\n";
      for (const auto& gate : circuit) cout << gate[0] << ' ' << gate[1] << ' ' << gate[2] << '\n';
      return 10;
    }
    shuffle(errors.begin(), errors.end(), random);
    for (int i = 0; i < min((int)errors.size(), 32); ++i) syn.row(errors[i]);
    ++iteration;
  }
  return 1;
}
