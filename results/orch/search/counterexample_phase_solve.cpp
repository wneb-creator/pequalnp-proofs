#include <chrono>
#include <fstream>
#include <iostream>
#include "cadical.hpp"
class Watch final : public CaDiCaL::Terminator {
public:
  std::chrono::steady_clock::time_point end;
  bool terminate() override { return std::chrono::steady_clock::now() >= end; }
};
int main(int argc, char** argv) {
  if (argc != 5) {
    std::cout << "usage: phase_solve CNF PHASES SECONDS CONFLICTS\n";
    return 2;
  }
  CaDiCaL::Solver solver;
  int variables = 0;
  const char* error = solver.read_dimacs(argv[1], variables);
  if (error) { std::cerr << error << '\n'; return 2; }
  std::ifstream phases(argv[2]);
  if (!phases) { std::cerr << "cannot read phases\n"; return 2; }
  int literal;
  while (phases >> literal) solver.phase(literal);
  Watch watch;
  watch.end = std::chrono::steady_clock::now() + std::chrono::seconds(std::stoi(argv[3]));
  solver.connect_terminator(&watch);
  solver.limit("conflicts",std::stoi(argv[4]));
  const int result = solver.solve();
  solver.statistics();
  std::cout << "s " << (result == 10 ? "SATISFIABLE" : result == 20 ? "UNSATISFIABLE" : "UNKNOWN") << '\n';
  if (result == 10) {
    std::cout << "v ";
    for (int v = 1; v <= variables; ++v) std::cout << solver.val(v) << ' ';
    std::cout << "0\n";
  }
  return result;
}
