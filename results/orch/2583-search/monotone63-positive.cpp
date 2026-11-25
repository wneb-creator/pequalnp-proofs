#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>

constexpr int N = 26, G = 63, W = 12;
using TT = std::array<uint64_t, W>;
struct Gate { int op, a, b; };
using Circuit = std::array<Gate, G>;
std::array<TT, N + G> initial{};
TT target{}, valid{}, positive{};
std::array<std::array<int, 4>, 13> lines{};
std::vector<std::pair<int, int>> edges;
std::mt19937_64 rng;
int rr(int n) { return rng() % n; }

int edgeWeight = 1024;
struct Score { int miss, extra; int cost() const { return edgeWeight * miss + extra; } };
Score evaluate(const Circuit &c) {
    auto wires = initial;
    for (int i = 0; i < G; ++i) {
        auto g = c[i];
        if (g.op == 0)
            for (int k = 0; k < W; ++k) wires[N+i][k] = wires[g.a][k] & wires[g.b][k];
        else
            for (int k = 0; k < W; ++k) wires[N+i][k] = wires[g.a][k] | wires[g.b][k];
    }
    Score score{0,0};
    for (int k = 0; k < W; ++k) {
        uint64_t diff = (wires[N+G-1][k] ^ target[k]) & valid[k];
        score.miss += __builtin_popcountll(diff & positive[k]);
        score.extra += __builtin_popcountll(diff & ~positive[k]);
    }
    return score;
}

void save(const Circuit &c, Score s, uint64_t steps, const std::string &path) {
    std::ofstream out(path);
    out << "{\"inputs\":26,\"output\":88,\"miss\":" << s.miss
        << ",\"extra\":" << s.extra << ",\"steps\":" << steps << ",\"gates\":[\n";
    for (int i = 0; i < G; ++i)
        out << "{\"op\":\"" << (c[i].op == 0 ? "and" : "or") << "\",\"a\":"
            << c[i].a << ",\"b\":" << c[i].b << "}" << (i+1 < G ? ",\n" : "\n");
    out << "]}\n";
}

Circuit seed() {
    std::array<std::vector<int>,N> ns;
    bool side = rr(2);
    for (auto [a,b] : edges) {
        if (side) std::swap(a,b);
        ns[a].push_back(b);
    }
    // Occasionally split stars between both sides, allowing a different topology.
    for (int trial = 0, lim = rr(4) == 0 ? rr(5) : 0; trial < lim; ++trial) {
        int v = rr(N);
        for (auto [a,b] : edges) {
            if (b == v) std::swap(a,b);
            if (a != v) continue;
            auto &old = ns[b];
            auto it = std::find(old.begin(),old.end(),v);
            if (it != old.end()) { old.erase(it); ns[v].push_back(b); }
        }
    }
    std::vector<int> centers;
    for (int v = 0; v < N; ++v) if (!ns[v].empty()) centers.push_back(v);
    std::shuffle(centers.begin(),centers.end(),rng);
    std::vector<Gate> gs;
    std::vector<int> outputs;
    for (int v : centers) {
        auto adj = ns[v];
        std::shuffle(adj.begin(),adj.end(),rng);
        while (adj.size() > 1) {
            int a = rr(adj.size()), x = adj[a]; adj.erase(adj.begin()+a);
            int b = rr(adj.size()), y = adj[b]; adj.erase(adj.begin()+b);
            gs.push_back({1,x,y}); adj.push_back(N+gs.size()-1);
        }
        gs.push_back({0,v,adj[0]}); outputs.push_back(N+gs.size()-1);
        if (outputs.size() > 1 && rr(2)) {
            int a = outputs.back(); outputs.pop_back();
            int b = outputs.back(); outputs.pop_back();
            gs.push_back({1,a,b}); outputs.push_back(N+gs.size()-1);
        }
    }
    while (outputs.size() > 1) {
        int a = rr(outputs.size()), x = outputs[a]; outputs.erase(outputs.begin()+a);
        int b = rr(outputs.size()), y = outputs[b]; outputs.erase(outputs.begin()+b);
        gs.push_back({1,x,y}); outputs.push_back(N+gs.size()-1);
    }
    while (gs.size() > G) {
        int j = rr(gs.size()-1);
        while (gs[j].op != 0) j = rr(gs.size()-1);
        int replacement = rr(2) ? gs[j].a : gs[j].b;
        gs.erase(gs.begin()+j);
        for (auto &g : gs) for (int *p : {&g.a,&g.b}) {
            if (*p == N+j) *p = replacement;
            else if (*p > N+j) --*p;
        }
    }
    Circuit c;
    std::copy(gs.begin(),gs.end(),c.begin());
    return c;
}

int main(int argc, char **argv) {
    if (argc < 5 || argc > 6) { std::cerr << "usage: monotone63 problem.dat seconds seed output.json [edgeWeight]\n"; return 2; }
    std::ifstream in(argv[1]); int n,l,p,f;
    in >> n >> l >> p >> f;
    if (!in || n != N || l != 13 || p+f > W*64) return 2;
    for (int j = 0; j < 13; ++j) for (int &v : lines[j]) { in >> v; edges.push_back({v,13+j}); }
    for (int row = 0; row < p+f; ++row) {
        unsigned x; int y; in >> x >> y;
        uint64_t bit = uint64_t(1) << (row%64); valid[row/64] |= bit;
        if (y) { target[row/64] |= bit; positive[row/64] |= bit; }
        for (int j = 0; j < N; ++j) if (x>>j&1) initial[j][row/64] |= bit;
    }
    int seconds = std::stoi(argv[2]); rng.seed(std::stoull(argv[3]));
    if (argc == 6) edgeWeight = std::stoi(argv[5]);
    auto start = std::chrono::steady_clock::now();
    auto elapsed = [&] { return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count(); };
    int best = 100000, bestPositive = 100000; uint64_t steps = 0, runs = 0;
    while (elapsed() < seconds) {
        Circuit c = seed(); auto score = evaluate(c); ++runs;
        for (int epoch = 0; epoch < 24; ++epoch) for (int it = 0; it < 12000; ++it) {
            Circuit next = c;
            int edits = 1 + (rr(100) < 12) + (rr(100) < 2);
            for (int e = 0; e < edits; ++e) {
                int j = rr(G), what = rr(7); auto &g = next[j];
                if (what == 0) g.op = 1-g.op;
                else if (what <= 3) g.a = rr(N+j);
                else g.b = rr(N+j);
            }
            auto trial = evaluate(next); ++steps;
            double temperature = 0.3 + 4.0 * std::pow(1.0-epoch/24.0,2);
            if (trial.cost() <= score.cost() ||
                std::generate_canonical<double,64>(rng) < std::exp((score.cost()-trial.cost())/temperature)) {
                c = next; score = trial;
            }
            if (trial.miss == 0 && trial.extra < bestPositive) {
                bestPositive = trial.extra; save(next,trial,steps,std::string(argv[4])+".positive.json");
                std::cout << "positivebest " << trial.extra << " steps " << steps << " restarts " << runs << " elapsed " << elapsed() << std::endl;
            }
            if (trial.cost() < best) {
                best = trial.cost(); save(next,trial,steps,argv[4]);
                std::cout << "best " << best << " missedges " << trial.miss << " falsepositives " << trial.extra
                          << " steps " << steps << " restarts " << runs << " elapsed " << elapsed() << std::endl;
            }
            if (trial.cost() == 0) return 0;
            if (steps%100000 == 0 && elapsed() >= seconds) goto done;
        }
    }
done:
    std::cout << "END cost " << best << " steps " << steps << " restarts " << runs << " elapsed " << elapsed() << std::endl;
}
