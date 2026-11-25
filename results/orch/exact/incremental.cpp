#include "cadical-2.1.2.hpp"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdlib>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>

using Clock = std::chrono::steady_clock;
using VI = std::vector<int>;
static const std::array<std::array<int, 2>, 15> edges = {{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};

bool target(int x) {
  for (auto e : edges) if (((x >> e[0]) & (x >> e[1]) & 1) != 0) return true;
  return false;
}

struct Deadline : CaDiCaL::Terminator {
  Clock::time_point end;
  explicit Deadline(int seconds) : end(Clock::now() + std::chrono::seconds(seconds)) {}
  bool terminate() override { return Clock::now() >= end; }
};

struct Gate { int op, a, b; };

struct Synth {
  CaDiCaL::Solver solver;
  int n = 0, m;
  long long clauses = 0;
  std::vector<VI> L, R, O;
  std::set<int> samples;

  int var() { return ++n; }
  void clause(const VI &xs) {
    for (int x : xs) solver.add(x);
    solver.add(0); ++clauses;
  }
  void clause(std::initializer_list<int> xs) { clause(VI(xs)); }
  VI vars(int count) { VI out; while (count--) out.push_back(var()); return out; }
  void one(const VI &xs) {
    clause(xs);
    for (int i = 0; i < (int)xs.size(); ++i)
      for (int j = 0; j < i; ++j) clause({-xs[i], -xs[j]});
  }
  void subsets(const VI &xs, int k, int sign, int off = 0, VI chosen = {}) {
    if (!k) { clause(chosen); return; }
    for (int i = off; i + k <= (int)xs.size(); ++i) {
      chosen.push_back(sign * xs[i]); subsets(xs, k - 1, sign, i + 1, chosen); chosen.pop_back();
    }
  }
  void mux(int v, const VI &selectors, const VI &values) {
    for (int j = 0; j < (int)selectors.size(); ++j) {
      clause({-selectors[j], -v, values[j]});
      clause({-selectors[j], v, -values[j]});
    }
  }

  Synth(int size, int notcount, int first, int seed, Deadline &deadline) : m(size) {
    solver.set("quiet", 1);
    solver.set("seed", seed);
    solver.configure("sat");
    solver.connect_terminator(&deadline);
    for (int i = 0; i < m; ++i) {
      int width = 10 + i;
      L.push_back(vars(width)); R.push_back(vars(width)); O.push_back(vars(3));
      one(L[i]); one(R[i]); one(O[i]);
      for (int a = 0; a < width; ++a) for (int b = 0; b < width; ++b) {
        if (a >= b) clause({O[i][2], -L[i][a], -R[i][b]});
        if (a != b) clause({-O[i][2], -L[i][a], -R[i][b]});
      }
    }
    VI nots; for (auto &op : O) nots.push_back(op[2]);
    if (!notcount) for (int x : nots) clause({-x});
    else if (notcount == 1) one(nots);
    else {
      subsets(nots, notcount + 1, -1);
      subsets(nots, m - notcount + 1, 1);
    }
    if (first == -2) {
      clause({L[0][0]});
      clause({R[0][0], R[0][1], R[0][2]});
      for (int i = 1; i < m; ++i) for (int k = 0; k < 10; ++k)
        clause({-O[i][2], -L[i][k], O[0][2]});
      for (int i = 0; i < m; ++i) for (auto e : edges) {
        int a = std::min(e[0], e[1]), b = std::max(e[0], e[1]);
        clause({O[0][2], -L[i][a], -R[i][b], R[0][1]});
      }
    } else if (first >= 0) {
      if (first == 4) { clause({O[0][2]}); clause({L[0][0]}); clause({R[0][0]}); }
      else { clause({O[0][first / 2]}); clause({L[0][0]}); clause({R[0][1 + first % 2]}); }
    }
    for (int i = 0; i + 1 < m; ++i) {
      VI users;
      for (int j = i + 1; j < m; ++j) { users.push_back(L[j][10+i]); users.push_back(R[j][10+i]); }
      clause(users);
      for (int b = 0; b < 10+i; ++b) {
        for (int d = 0; d < b; ++d) clause({-R[i][b], -R[i+1][d]});
        for (int a = 0; a <= b; ++a) for (int aa = 0; aa < a; ++aa)
          clause({-R[i][b], -R[i+1][b], -L[i][a], -L[i+1][aa]});
      }
    }
    if (notcount == 1) {
      clause({-O.back()[2]});
      positive_paths();
    } else if (notcount >= 2) {
      signed_paths();
    } else {
      for (int k = 0; k < 10; ++k) {
        VI uses; for (int i = 0; i < m; ++i) { uses.push_back(L[i][k]); uses.push_back(R[i][k]); }
        clause(uses);
      }
    }
    for (int i = 0; i < m; ++i) {
      for (int v : L[i]) solver.freeze(v);
      for (int v : R[i]) solver.freeze(v);
      for (int v : O[i]) solver.freeze(v);
    }
  }

  void positive_paths() {
    for (int k = 0; k < 10; ++k) {
      VI reach = vars(10+m);
      for (int j = 0; j < 10; ++j) clause({j == k ? reach[j] : -reach[j]});
      for (int i = 0; i < m; ++i) {
        int a = var(), b = var(), z = reach[10+i], opnot = O[i][2];
        mux(a, L[i], reach); mux(b, R[i], reach);
        clause({-opnot, -z});
        clause({opnot, z, -a}); clause({opnot, z, -b}); clause({opnot, -z, a, b});
      }
      clause({reach.back()});
    }
  }

  void signed_paths() {
    for (int k = 0; k < 10; ++k) {
      VI pos = vars(10+m), neg = vars(10+m);
      for (int j = 0; j < 10; ++j) {
        clause({j == k ? pos[j] : -pos[j]}); clause({-neg[j]});
      }
      for (int i = 0; i < m; ++i) {
        int ap = var(), bp = var(), an = var(), bn = var();
        int zp = pos[10+i], zn = neg[10+i], opnot = O[i][2];
        mux(ap, L[i], pos); mux(bp, R[i], pos);
        mux(an, L[i], neg); mux(bn, R[i], neg);
        clause({-opnot, -zp, an}); clause({-opnot, zp, -an});
        clause({-opnot, -zn, ap}); clause({-opnot, zn, -ap});
        clause({opnot, zp, -ap}); clause({opnot, zp, -bp}); clause({opnot, -zp, ap, bp});
        clause({opnot, zn, -an}); clause({opnot, zn, -bn}); clause({opnot, -zn, an, bn});
      }
      clause({pos.back()});
    }
  }

  void sample(int x) {
    if (!samples.insert(x).second) return;
    VI values = vars(10+m);
    for (int k = 0; k < 10; ++k) clause({((x >> k) & 1) ? values[k] : -values[k]});
    for (int i = 0; i < m; ++i) {
      int a = var(), b = var(), z = values[10+i];
      mux(a, L[i], values); mux(b, R[i], values);
      int opand = O[i][0], opor = O[i][1], opnot = O[i][2];
      clause({-opand, -z, a}); clause({-opand, -z, b}); clause({-opand, z, -a, -b});
      clause({-opor, z, -a}); clause({-opor, z, -b}); clause({-opor, -z, a, b});
      clause({-opnot, -z, -a}); clause({-opnot, z, a});
    }
    clause({target(x) ? values.back() : -values.back()});
  }

  std::vector<Gate> model() {
    std::vector<Gate> gs;
    auto selected = [&](const VI &xs) {
      for (int i = 0; i < (int)xs.size(); ++i) if (solver.val(xs[i]) > 0) return i;
      std::cerr << "invalid selector model\n"; std::exit(2);
    };
    for (int i = 0; i < m; ++i) gs.push_back({selected(O[i]), selected(L[i]), selected(R[i])});
    return gs;
  }
};

VI bad_inputs(const std::vector<Gate> &gs) {
  VI bad;
  for (int x = 0; x < 1024; ++x) {
    VI v; for (int k = 0; k < 10; ++k) v.push_back((x >> k) & 1);
    for (auto g : gs) v.push_back(g.op == 0 ? (v[g.a] & v[g.b]) : (g.op == 1 ? (v[g.a] | v[g.b]) : 1-v[g.a]));
    if ((bool)v.back() != target(x)) bad.push_back(x);
  }
  return bad;
}

void write_candidate(const std::filesystem::path &path, const std::vector<Gate> &gs, const VI &bad) {
  std::ofstream out(path);
  const char *names[] = {"and", "or", "not"};
  out << "{\"gates\":[";
  for (int i = 0; i < (int)gs.size(); ++i) {
    if (i) out << ',';
    auto g = gs[i]; out << "{\"op\":\"" << names[g.op] << "\",\"a\":" << g.a << ",\"b\":" << g.b << '}';
  }
  out << "],\"bad\":[";
  for (int i = 0; i < (int)bad.size(); ++i) { if (i) out << ','; out << bad[i]; }
  out << "]}\n";
}

int main(int argc, char **argv) {
  if (argc < 6) {
    std::cerr << "usage: incremental gates notcount first-orbit seconds output-dir [seed] [small|edges|all]\n";
    return 2;
  }
  int m = std::stoi(argv[1]), notcount = std::stoi(argv[2]), first = std::stoi(argv[3]), seconds = std::stoi(argv[4]);
  if (m <= 0 || notcount < 0 || notcount > m || first < -2 || first > 4 || seconds <= 0) {
    std::cerr << "invalid size, NOT count, orbit, or time limit\n";
    return 2;
  }
  std::filesystem::path outdir(argv[5]); std::filesystem::create_directories(outdir);
  int seed = argc > 6 ? std::stoi(argv[6]) : 98;
  std::string initial = argc > 7 ? argv[7] : "small";
  Deadline deadline(seconds); auto started = Clock::now();
  Synth c(m, notcount, first, seed, deadline);
  if (argc > 8) {
    std::ifstream fixed(argv[8]);
    for (int i = 0; i < m; ++i) {
      int op, a, b;
      if (!(fixed >> op >> a >> b)) { std::cerr << "invalid fixed circuit\n"; return 2; }
      if (op < 0 || op > 2 || a < 0 || b < 0 || a >= 10+i || b >= 10+i) {
        std::cerr << "fixed gate outside source domain\n"; return 2;
      }
      c.clause({c.O[i][op]}); c.clause({c.L[i][a]}); c.clause({c.R[i][b]});
    }
  }
  std::mt19937 rng(seed);
  c.sample(0); c.sample(1023);
  if (initial == "all") for (int x = 0; x < 1024; ++x) c.sample(x);
  else if (initial == "edges") {
    for (int k = 0; k < 10; ++k) c.sample(1 << k);
    for (auto e : edges) c.sample((1 << e[0]) | (1 << e[1]));
    for (int x : {116,201,402,554,773}) c.sample(x);
  } else for (int i = 0; i < 6; ++i) c.sample(rng() % 1024);
  int round = 0, segments = 0;
  while (!deadline.terminate()) {
    double elapsed = std::chrono::duration<double>(Clock::now()-started).count();
    std::cout << "round " << round << " segment " << segments << " samples " << c.samples.size() << " vars " << c.n << " clauses " << c.clauses << " wall " << elapsed << " cpu " << (double)std::clock()/CLOCKS_PER_SEC << std::endl;
    c.solver.limit("conflicts", 200000);
    int res = c.solver.solve();
    std::cout << "solve " << res << std::endl;
    if (res == 20) {
      std::cout << "UNSAT restricted normal-form model; wall " << std::chrono::duration<double>(Clock::now()-started).count() << " cpu " << (double)std::clock()/CLOCKS_PER_SEC << '\n';
      return 0;
    }
    if (res == 0) { ++segments; continue; }
    auto gs = c.model(); auto bad = bad_inputs(gs);
    for (int x : bad) if (c.samples.count(x)) {
      std::cerr << "model fails encoded sample " << x << '\n'; return 3;
    }
    write_candidate(outdir / ("candidate-" + std::to_string(round) + ".json"), gs, bad);
    std::cout << "candidate " << round << " errors " << bad.size() << std::endl;
    if (bad.empty()) {
      std::cout << "WITNESS full 1024 inputs verified; wall " << std::chrono::duration<double>(Clock::now()-started).count() << " cpu " << (double)std::clock()/CLOCKS_PER_SEC << '\n';
      write_candidate(outdir / "WITNESS.json", gs, bad); return 0;
    }
    std::stable_sort(bad.begin(), bad.end(), [](int a, int b) {
      int wa = __builtin_popcount((unsigned)a), wb = __builtin_popcount((unsigned)b);
      if (wa != wb) return wa < wb;
      return target(a) < target(b);
    });
    int added = 0;
    for (int x : bad) {
      c.sample(x); if (++added == 4) break;
    }
    ++round; segments = 0;
  }
  std::cout << "UNKNOWN global wall deadline; wall " << std::chrono::duration<double>(Clock::now()-started).count() << " cpu " << (double)std::clock()/CLOCKS_PER_SEC << '\n';
  return 0;
}
