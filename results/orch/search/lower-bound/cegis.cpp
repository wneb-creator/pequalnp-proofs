#include "cadical.hpp"
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Clock = std::chrono::steady_clock;

struct Deadline : CaDiCaL::Terminator {
  Clock::time_point until;
  explicit Deadline(int seconds) : until(Clock::now() + std::chrono::seconds(seconds)) {}
  bool terminate() override { return Clock::now() >= until; }
};

struct Row { unsigned mask; bool expected; bool active; int output; };
struct GateVars { int op; std::vector<int> left, right; };
struct Gate { int left, right; bool is_or; };

static const std::pair<int,int> edges[] = {
  {0,7},{0,8},{0,10},{1,7},{1,9},{1,13},{2,8},{2,12},{2,13},
  {3,7},{3,11},{3,12},{4,10},{4,11},{4,13},{5,9},{5,10},{5,12},
  {6,8},{6,9},{6,11}
};

bool target(unsigned mask) {
  for (auto edge : edges)
    if (((mask >> edge.first) & 1u) && ((mask >> edge.second) & 1u)) return true;
  return false;
}

bool evaluate(const std::vector<Gate>& gates, unsigned mask) {
  std::vector<bool> values;
  for (int i = 0; i < 14; ++i) values.push_back((mask >> i) & 1u);
  for (auto gate : gates) {
    if (gate.left < 0 || gate.right < 0 || gate.left >= (int) values.size() ||
        gate.right >= (int) values.size()) throw std::runtime_error("invalid predecessor");
    const bool a = values[gate.left], b = values[gate.right];
    values.push_back(gate.is_or ? (a || b) : (a && b));
  }
  return values.back();
}

int selected(CaDiCaL::Solver& solver, const std::vector<int>& variables) {
  int choice = -1;
  for (int i = 0; i < (int) variables.size(); ++i) {
    if (solver.val(variables[i]) > 0) {
      if (choice != -1) throw std::runtime_error("multiple selector choices");
      choice = i;
    }
  }
  if (choice == -1) throw std::runtime_error("missing selector choice");
  return choice;
}

void save_model(const std::string& path, const std::vector<Gate>& gates,
                const std::vector<int>& violations, bool checked_all) {
  std::ofstream file(path);
  if (!file) throw std::runtime_error("cannot open model output");
  file << "{\"gates\":[";
  for (int i = 0; i < (int) gates.size(); ++i) {
    auto gate = gates[i];
    if (i) file << ',';
    file << '[' << (gate.is_or ? 1 : 0) << ',' << gate.left << ',' << gate.right << ']';
  }
  file << "],\"packed\":[";
  for (int i = 0; i < (int) gates.size(); ++i) {
    auto gate = gates[i];
    if (i) file << ',';
    file << gate.left + 64 * gate.right + (gate.is_or ? 4096 : 0);
  }
  file << "],\"output\":" << 13 + gates.size() << ",\"violating_rows\":[";
  for (int i = 0; i < (int) violations.size(); ++i) {
    if (i) file << ',';
    file << violations[i];
  }
  file << "],\"checked_all_16384\":" << (checked_all ? "true" : "false") << "}\n";
}

int main(int argc, char** argv) {
  if (argc != 5) {
    std::cerr << "usage: cegis base.cnf metadata seconds output-prefix\n";
    return 2;
  }
  try {
    const int seconds = std::stoi(argv[3]);
    if (seconds <= 0) throw std::runtime_error("positive time budget required");
    std::ifstream metadata(argv[2]);
    int n_gates, n_rows, n_variables;
    if (!(metadata >> n_gates >> n_rows >> n_variables)) throw std::runtime_error("bad metadata");
    if (n_gates < 2 || n_rows != 58) throw std::runtime_error("unexpected instance shape");
    std::vector<Row> rows(n_rows);
    for (auto& row : rows) {
      if (!(metadata >> row.mask >> row.expected >> row.active >> row.output))
        throw std::runtime_error("bad row metadata");
      if (row.mask >= (1u << 14) || row.expected != target(row.mask))
        throw std::runtime_error("wrong target row");
    }
    std::vector<GateVars> structure(n_gates);
    for (int i = 0; i < n_gates; ++i) {
      int n_inputs;
      if (!(metadata >> structure[i].op >> n_inputs) || n_inputs != 14 + i)
        throw std::runtime_error("bad gate metadata");
      structure[i].left.resize(n_inputs);
      structure[i].right.resize(n_inputs);
      for (int& v : structure[i].left) if (!(metadata >> v)) throw std::runtime_error("bad left map");
      for (int& v : structure[i].right) if (!(metadata >> v)) throw std::runtime_error("bad right map");
    }
    CaDiCaL::Solver solver;
    solver.configure("sat");
    int variables = 0;
    if (const char* error = solver.read_dimacs(argv[1], variables)) throw std::runtime_error(error);
    if (variables != n_variables) throw std::runtime_error("variable count mismatch");
    int active = 0;
    for (auto row : rows) {
      solver.freeze(row.output);
      if (row.active) { solver.clause(row.expected ? row.output : -row.output); ++active; }
    }
    const auto started = Clock::now();
    Deadline deadline(seconds);
    solver.connect_terminator(&deadline);
    for (int iteration = 0; iteration <= n_rows; ++iteration) {
      std::cout << "iteration " << iteration << " active " << active << std::endl;
      const int result = solver.solve();
      const auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(Clock::now() - started).count();
      std::cout << "result " << result << " elapsed_ms " << elapsed << std::endl;
      if (result != 10) {
        solver.statistics(); solver.resources();
        std::cout << "s " << (result == 20 ? "UNSATISFIABLE_SUBSET" : "UNKNOWN") << std::endl;
        return result;
      }
      std::vector<Gate> gates;
      for (auto& gate : structure)
        gates.push_back({selected(solver, gate.left), selected(solver, gate.right), solver.val(gate.op) > 0});
      std::vector<int> violations;
      for (int r = 0; r < n_rows; ++r) {
        const bool computed = evaluate(gates, rows[r].mask);
        if (computed != (solver.val(rows[r].output) > 0))
          throw std::runtime_error("decoded circuit disagrees with encoded row");
        if (computed != rows[r].expected) {
          if (rows[r].active) throw std::runtime_error("active row violated");
          violations.push_back(r);
        }
      }
      const std::string prefix(argv[4]);
      const std::string model_path = prefix + ".iteration-" + std::to_string(iteration) + ".json";
      std::cout << "new_violations " << violations.size() << std::endl;
      if (violations.empty()) {
        for (unsigned mask = 0; mask < (1u << 14); ++mask)
          if (evaluate(gates, mask) != target(mask))
            throw std::runtime_error("boundary solution failed exhaustive validation");
        save_model(model_path, gates, violations, true);
        save_model(prefix + ".witness.json", gates, violations, true);
        solver.statistics(); solver.resources();
        std::cout << "s SATISFIABLE_FULL_CHECKED_16384" << std::endl;
        return 10;
      }
      save_model(model_path, gates, violations, false);
      int chosen = -1, chosen_weight = -1, chosen_distance = -1;
      for (int r : violations) {
        if (rows[r].expected) throw std::runtime_error("positive row unexpectedly unconstrained");
        const int weight = __builtin_popcount(rows[r].mask);
        int distance = 14;
        for (auto old : rows)
          if (old.active && !old.expected)
            distance = std::min(distance, __builtin_popcount(rows[r].mask ^ old.mask));
        if (weight > chosen_weight || (weight == chosen_weight && distance > chosen_distance)) {
          chosen = r;
          chosen_weight = weight;
          chosen_distance = distance;
        }
      }
      if (chosen < 0) throw std::runtime_error("missing refinement row");
      std::cout << "selected_row " << chosen << " mask " << rows[chosen].mask
                << " weight " << chosen_weight << " distance " << chosen_distance << std::endl;
      solver.clause(-rows[chosen].output);
      rows[chosen].active = true;
      ++active;
    }
    throw std::runtime_error("iteration bound exceeded");
  } catch (const std::exception& error) {
    std::cerr << "ERROR: " << error.what() << std::endl;
    return 2;
  }
}
