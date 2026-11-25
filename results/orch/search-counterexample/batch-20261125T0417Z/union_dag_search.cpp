#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <utility>
#include <vector>

// Pure union gates; outputs take the free conjunction of all supersets of their
// required four singleton samples.  The score is a finite set-cover potential.
struct Gate { int a, b; };
using Network = std::vector<Gate>;
struct Search {
  int n, m;
  std::vector<int> targets, required, forbidden;
  std::vector<uint16_t> contrib;
  std::array<uint8_t, 65536> cost{};
  std::mt19937_64 rng;
  uint64_t evaluations = 0;
  explicit Search(const std::string& path, uint64_t seed): rng(seed) {
    std::ifstream f(path); f >> n >> m;
    if (!f || n != 13 || m <= 0) throw std::runtime_error("bad data");
    targets.resize(n); for (auto& x : targets) f >> x;
    required.resize(m); forbidden.resize(m);
    for (int j = 0; j < m; ++j) f >> required[j] >> forbidden[j];
    if (!f) throw std::runtime_error("incomplete data");
    for (int a = 0; a < 65536; ++a) {
      int v = 4;
      if (a & (1 << 15)) v = 1;
      else {
        for (int s = 1; s < 16; ++s) if (a & (1 << s)) {
          if (std::popcount(unsigned(s)) >= 2) v = std::min(v, 3);
          for (int t = s; t < 16; ++t)
            if ((a & (1 << t)) && (s | t) == 15) v = 2;
        }
      }
      cost[a] = v;
    }
    contrib.resize((1 << n) * m);
    for (int u = 0; u < (1 << n); ++u) for (int j = 0; j < m; ++j) {
      int s = 0, b = 0;
      for (int i = 0; i < n; ++i) if ((required[j] >> i) & 1) {
        if ((u >> i) & 1) s |= 1 << b;
        ++b;
      }
      contrib[u*m+j] = (u & forbidden[j]) ? 0 : uint16_t(1 << s);
    }
  }
  std::vector<int> masks(const Network& net) const {
    std::vector<int> wire(n + net.size());
    for (int i = 0; i < n; ++i) wire[i] = 1 << i;
    for (int g = 0; g < int(net.size()); ++g) {
      if (net[g].a < 0 || net[g].a >= n+g || net[g].b < 0 || net[g].b >= n+g)
        throw std::runtime_error("invalid forward edge");
      wire[n+g] = wire[net[g].a] | wire[net[g].b];
    }
    return wire;
  }
  // Singleton wires are always false on every relevant negative sample.
  std::pair<int,int> evaluate(const Network& net) {
    ++evaluations;
    auto wire = masks(net);
    std::vector<uint16_t> available(m, (1<<1)|(1<<2)|(1<<4)|(1<<8));
    for (int g = n; g < int(wire.size()); ++g) {
      const auto* row = contrib.data() + wire[g]*m;
      for (int j = 0; j < m; ++j) available[j] |= row[j];
    }
    int deficit = 0, uncovered = 0;
    for (int j = 0; j < m; ++j) {
      deficit += cost[available[j]] - 1;
      uncovered += !(available[j] & (1<<15));
    }
    return {deficit, uncovered};
  }
  Network baseline() {
    Network net;
    auto order = targets; std::shuffle(order.begin(), order.end(), rng);
    for (int target : order) {
      std::vector<int> bits;
      for (int i = 0; i < n; ++i) if ((target >> i) & 1) bits.push_back(i);
      std::shuffle(bits.begin(), bits.end(), rng);
      int start = n + net.size();
      net.push_back({bits[0], bits[1]});
      net.push_back({bits[2], bits[3]});
      net.push_back({start, start+1});
    }
    return net;
  }
  Network remove(const Network& input, int deleted, int side) {
    Network net;
    int oldwire = n+deleted;
    int replacement = side ? input[deleted].a : input[deleted].b;
    for (int g = 0; g < int(input.size()); ++g) if (g != deleted) {
      auto fix = [&](int i) { if (i == oldwire) i = replacement; if (i > oldwire) --i; return i; };
      net.push_back({fix(input[g].a), fix(input[g].b)});
    }
    return net;
  }
  void write(const std::string& path, const Network& net, std::pair<int,int> score) {
    auto wire = masks(net);
    std::ofstream f(path);
    f << "{\"model\":\"pure_union_DAG_free_intersection_outputs\",\"input_count\":13,\"or_count\":"
      << net.size() << ",\"cover_deficit\":" << score.first << ",\"uncovered_requirements\":"
      << score.second << ",\"is_counterexample\":" << (score.first == 0 ? "true" : "false") << ",\"ors\":[";
    for (int g = 0; g < int(net.size()); ++g) {
      if (g) f << ',';
      f << '[' << net[g].a << ',' << net[g].b << ']';
    }
    f << "],\"gate_masks\":[";
    for (int g = n; g < int(wire.size()); ++g) { if (g != n) f << ','; f << wire[g]; }
    f << "]}\n";
  }
};
int main(int argc, char** argv) {
  if (argc != 6 || std::string(argv[1]) == "--help") {
    std::cout << "usage: union_dag_search DATA SECONDS SEED BEST_JSON MODE(search|control)\n";
    return argc == 2 ? 0 : 2;
  }
  std::string data = argv[1], output = argv[4], mode = argv[5];
  double seconds = std::stod(argv[2]); uint64_t seed = std::stoull(argv[3]);
  Search search(data, seed);
  Network control = search.baseline(); auto check = search.evaluate(control);
  std::cout << "control39 deficit=" << check.first << " uncovered=" << check.second << " requirements=" << search.m << std::endl;
  if (check.first || check.second) return 3;
  if (mode == "control") { search.write(output, control, check); return 0; }
  auto start = std::chrono::steady_clock::now();
  auto elapsed = [&]() { return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count(); };
  int best = 1000000, best_deficit = 1000000;
  Network best_net;
  uint64_t restarts = 0;
  while (elapsed() < seconds) {
    Network net = search.remove(search.baseline(), search.rng()%39, search.rng()%2);
    auto sc = search.evaluate(net); int energy = sc.first*4 + sc.second;
    double top = 2.0 + (search.rng()%8)*3.0;
    int steps = 8000;
    for (int step = 0; step < steps; ++step) {
      if ((step & 255) == 0 && elapsed() >= seconds) break;
      Network trial = net;
      int g = search.rng()%trial.size();
      int type = search.rng()%100;
      if (type < 82) {
        int& operand = (search.rng()%2) ? trial[g].a : trial[g].b;
        operand = search.rng()%(search.n+g);
      } else if (type < 95) {
        trial[g].a = search.rng()%(search.n+g);
        trial[g].b = search.rng()%(search.n+g);
      } else {
        // Rewire uses of one existing wire; this permits coherent sharing moves.
        int old = search.rng()%(search.n+int(trial.size()));
        int replacement = search.rng()%(search.n+int(trial.size()));
        for (int h = 0; h < int(trial.size()); ++h) if (replacement < search.n+h) {
          if (trial[h].a == old) trial[h].a = replacement;
          if (trial[h].b == old) trial[h].b = replacement;
        }
      }
      auto ts = search.evaluate(trial); int te = ts.first*4+ts.second;
      double temp = top*(1.0-double(step)/steps)+0.15;
      if (te <= energy || std::generate_canonical<double,53>(search.rng) < std::exp((energy-te)/temp)) {
        net.swap(trial); sc=ts; energy=te;
      }
      if (energy < best) {
        best=energy; best_deficit=sc.first; best_net=net;
        search.write(output, net, sc);
        std::cout << "best seconds=" << elapsed() << " deficit=" << sc.first << " uncovered=" << sc.second << " evaluations=" << search.evaluations << std::endl;
        if (!sc.first) return 0;
      }
    }
    ++restarts;
    if (restarts%20 == 0) std::cout << "progress seconds=" << elapsed() << " restarts=" << restarts << " evaluations=" << search.evaluations << " best_deficit=" << best_deficit << std::endl;
  }
  std::cout << "finished seconds=" << elapsed() << " restarts=" << restarts << " evaluations=" << search.evaluations << " best_deficit=" << best_deficit << " result=heuristic_no_witness" << std::endl;
  return 0;
}
