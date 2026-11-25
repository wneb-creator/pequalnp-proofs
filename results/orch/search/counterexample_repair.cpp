#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
#include "cadical.hpp"

class Watch final : public CaDiCaL::Terminator {
public:
  std::chrono::steady_clock::time_point end;
  bool terminate() override { return std::chrono::steady_clock::now() >= end; }
};

int main(int argc, char** argv) {
  if (argc != 5) {
    std::cout << "usage: repair CNF SEED PHASES SECONDS\n";
    return 2;
  }
  CaDiCaL::Solver solver;
  int variables = 0;
  const char* error = solver.read_dimacs(argv[1], variables);
  if (error) { std::cerr << error << '\n'; return 2; }
  std::vector<std::array<int,3>> seed;
  std::ifstream inp(argv[2]);
  std::array<int,3> row;
  while (inp >> row[0] >> row[1] >> row[2]) seed.push_back(row);
  std::ifstream phases(argv[3]);
  int lit;
  while (phases >> lit) solver.phase(lit);
  Watch watch;
  const auto start = std::chrono::steady_clock::now();
  watch.end = start + std::chrono::seconds(std::stoi(argv[4]));
  solver.connect_terminator(&watch);
  std::mt19937 rng(76);
  int trials = 0, unsat = 0, unknown = 0;
  while (!watch.terminate()) {
    std::vector<int> order(seed.size());
    std::iota(order.begin(), order.end(), 0);
    std::shuffle(order.begin(), order.end(), rng);
    int free_count = 8 + trials % 9;
    for (int i = free_count; i < (int)order.size(); ++i)
      for (int x : seed[order[i]]) solver.assume(x);
    solver.limit("conflicts", 20000);
    const int result = solver.solve();
    ++trials;
    const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout << "trial " << trials << " free " << free_count << " result " << result << " seconds " << seconds << std::endl;
    if (result == 10) {
      std::cout << "s SATISFIABLE\nv ";
      for (int v = 1; v <= variables; ++v) std::cout << solver.val(v) << ' ';
      std::cout << "0\n";
      return 10;
    }
    if (result == 20) ++unsat; else ++unknown;
  }
  std::cout << "finished trials " << trials << " unsat_neighborhoods " << unsat << " unknown " << unknown << std::endl;
  return 0;
}
