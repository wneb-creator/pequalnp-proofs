#include "cadical.hpp"
#include <cerrno>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

class Deadline final : public CaDiCaL::Terminator {
  using Clock = std::chrono::steady_clock;
  Clock::time_point start_ = Clock::now();
  double seconds_;
public:
  explicit Deadline(double seconds) : seconds_(seconds) {}
  bool terminate() override {
    return seconds_ >= 0 &&
      std::chrono::duration<double>(Clock::now() - start_).count() >= seconds_;
  }
};

static int fail(const std::string &message) {
  std::cerr << "cadical-phase: " << message << '\n';
  return 1;
}

int main(int argc, char **argv) {
  std::string profile = "default", input, phases;
  double seconds = -1;
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--help" || arg == "-h") {
      std::cout << "usage: cadical-phase [--default|--sat|--unsat] [-t seconds] "
                   "input.cnf [--phase-file signed-literals.txt]\n";
      return 0;
    } else if (arg == "--default" || arg == "--sat" || arg == "--unsat") {
      profile = arg.substr(2);
    } else if (arg == "-t") {
      if (++i == argc) return fail("-t needs a nonnegative finite number");
      char *end = nullptr;
      errno = 0;
      seconds = std::strtod(argv[i], &end);
      if (errno || end == argv[i] || *end || !std::isfinite(seconds) || seconds < 0)
        return fail("invalid time limit");
    } else if (arg == "--phase-file") {
      if (++i == argc) return fail("--phase-file needs a path");
      phases = argv[i];
    } else if (!arg.empty() && arg[0] == '-') {
      return fail("unsupported option " + arg);
    } else if (input.empty()) {
      input = arg;
    } else {
      return fail("multiple CNF inputs");
    }
  }
  if (input.empty()) return fail("missing CNF input");

  std::vector<int> hints;
  if (!phases.empty()) {
    std::ifstream stream(phases);
    if (!stream) return fail("cannot open phase file");
    std::string token;
    while (stream >> token) {
      char *end = nullptr;
      errno = 0;
      long value = std::strtol(token.c_str(), &end, 10);
      if (errno || end == token.c_str() || *end || value == 0 ||
          value < -INT_MAX || value > INT_MAX)
        return fail("phase file must contain nonzero signed integer literals");
      hints.push_back(static_cast<int>(value));
    }
    if (stream.bad()) return fail("phase file read failed");
  }

  Deadline deadline(seconds);
  CaDiCaL::Solver solver;
  if (!solver.configure(profile.c_str())) return fail("invalid solver profile");
  solver.set("quiet", 0);
  solver.set("stats", 5);
  solver.connect_terminator(&deadline);
  int variables = 0;
  const char *error = solver.read_dimacs(input.c_str(), variables);
  if (error) {
    if (!deadline.terminate()) return fail(error);
    std::cout << "s UNKNOWN\n";
    solver.statistics();
    solver.disconnect_terminator();
    return 0;
  }
  for (int hint : hints) {
    if (std::abs(hint) > variables) return fail("phase literal exceeds CNF variable count");
    solver.phase(hint);
  }
  std::cout << "c phase hints " << hints.size() << '\n';
  std::cout << "c profile " << profile << '\n';
  int result = solver.solve();
  if (result == 10) {
    std::cout << "s SATISFIABLE\n";
    for (int variable = 1; variable <= variables; ++variable) {
      if ((variable - 1) % 20 == 0) std::cout << "v";
      std::cout << ' ' << solver.val(variable);
      if (variable % 20 == 0) std::cout << '\n';
    }
    if (variables == 0 || variables % 20 == 0) std::cout << "v";
    std::cout << " 0\n";
  } else if (result == 20) {
    std::cout << "s UNSATISFIABLE\n";
  } else {
    std::cout << "s UNKNOWN\n";
  }
  solver.statistics();
  solver.disconnect_terminator();
  return result;
}
