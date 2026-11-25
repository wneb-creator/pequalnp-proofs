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

constexpr int N = 26, G = 63, W = 14;
using TT = std::array<uint64_t, W>;
struct Gate { int op, a, b; };
using Circuit = std::array<Gate, G>;
std::array<TT, N + G> initial{};
TT target{}, valid{}, positive{}, badpair{};
Circuit base{}; bool hasBase=false;
std::array<std::array<int, 4>, 13> lines{};
std::vector<std::pair<int, int>> edges;
std::mt19937_64 rng;
int rr(int n) { return rng() % n; }

int edgeWeight = 1000000;
struct Score { int miss, extra, side, pair; int cost() const { return edgeWeight * (miss+side) + 1024*pair + extra; } };
Score evaluate(const Circuit &c) {
    auto wires = initial;
    for (int i = 0; i < G; ++i) {
        auto g = c[i];
        if (g.op == 0)
            for (int k = 0; k < W; ++k) wires[N+i][k] = wires[g.a][k] & wires[g.b][k];
        else
            for (int k = 0; k < W; ++k) wires[N+i][k] = wires[g.a][k] | wires[g.b][k];
    }
    Score score{0,0,0,0};
    for (int k = 0; k < W; ++k) {
        uint64_t diff = (wires[N+G-1][k] ^ target[k]) & valid[k];
        score.miss += __builtin_popcountll(diff & positive[k]);
        score.extra += __builtin_popcountll(diff & ~positive[k]);
        score.pair += __builtin_popcountll(wires[N+G-1][k] & badpair[k]);
    }
    score.side = bool(wires[N+G-1][52/64] & (uint64_t(1)<<(52%64))) + bool(wires[N+G-1][755/64] & (uint64_t(1)<<(755%64)));
    return score;
}

void save(const Circuit &c, Score s, uint64_t steps, const std::string &path) {
    std::ofstream out(path);
    out << "{\"inputs\":26,\"output\":88,\"miss\":" << s.miss
        << ",\"extra\":" << s.extra << ",\"pure_side_errors\":" << s.side << ",\"bad_pairs\":" << s.pair << ",\"steps\":" << steps << ",\"gates\":[\n";
    for (int i = 0; i < G; ++i)
        out << "{\"op\":\"" << (c[i].op == 0 ? "and" : "or") << "\",\"a\":"
            << c[i].a << ",\"b\":" << c[i].b << "}" << (i+1 < G ? ",\n" : "\n");
    out << "]}\n";
}

Circuit seed() {
    if(hasBase && rr(2))return base;
    std::array<std::vector<int>,N> ns;
    bool side = rr(2);
    for (auto [a,b] : edges) {
        if (!side) std::swap(a,b);
        ns[a].push_back(b);
    }
    std::vector<int> centers;
    for (int v=0; v<N; ++v) if (!ns[v].empty()) centers.push_back(v);
    std::shuffle(centers.begin(),centers.end(),rng);
    std::vector<std::vector<int>> groups{{centers[0],centers[1]}};
    for (int j=2; j<13; ++j) groups.push_back({centers[j]});
    std::shuffle(groups.begin(),groups.end(),rng);
    std::vector<Gate> gs; std::vector<int> outputs;
    auto disj = [&](std::vector<int> ws) {
        std::shuffle(ws.begin(),ws.end(),rng);
        while(ws.size()>1) {
            int j=rr(ws.size()),a=ws[j];ws.erase(ws.begin()+j);
            j=rr(ws.size());int b=ws[j];ws.erase(ws.begin()+j);
            gs.push_back({1,a,b});ws.push_back(N+gs.size()-1);
        }
        return ws[0];
    };
    for (auto group:groups) {
        std::vector<int> adj;
        for(int a:group)for(int b:ns[a]) if(std::find(adj.begin(),adj.end(),b)==adj.end())adj.push_back(b);
        int a=disj(adj),b=disj(group);
        gs.push_back({0,a,b});outputs.push_back(N+gs.size()-1);
        if(outputs.size()>1 && rr(2)) {
            a=outputs.back();outputs.pop_back();b=outputs.back();outputs.pop_back();
            gs.push_back({1,a,b});outputs.push_back(N+gs.size()-1);
        }
    }
    disj(outputs);
    if(gs.size()!=G) {std::cerr<<"bad seed size "<<gs.size()<<std::endl;std::exit(2);}
    Circuit c;std::copy(gs.begin(),gs.end(),c.begin());return c;
}

int main(int argc, char **argv) {
    if (argc < 5 || argc > 7) { std::cerr << "usage: monotone63 problem.dat seconds seed output.json [edgeWeight] [seed.dat]\n"; return 2; }
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
    int row=p+f;
    for(int a=0;a<13;++a)for(int b=13;b<26;++b) {
        if(std::find(edges.begin(),edges.end(),std::pair<int,int>{a,b})!=edges.end())continue;
        uint64_t bit=uint64_t(1)<<(row%64);badpair[row/64]|=bit;
        initial[a][row/64]|=bit;initial[b][row/64]|=bit;++row;
    }
    if(row!=873)return 2;
    if(argc==7){std::ifstream seedfile(argv[6]);for(auto &g:base)seedfile>>g.op>>g.a>>g.b;if(!seedfile)return 2;hasBase=true;}
    int seconds = std::stoi(argv[2]); rng.seed(std::stoull(argv[3]));
    if (argc >= 6) edgeWeight = std::stoi(argv[5]);
    auto start = std::chrono::steady_clock::now();
    auto elapsed = [&] { return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count(); };
    int best = 1000000000, bestPositive = 1000000000; uint64_t steps = 0, runs = 0;
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
            double temperature = 0.3 + 250.0 * std::pow(1.0-epoch/24.0,2);
            if (trial.cost() <= score.cost() ||
                std::generate_canonical<double,64>(rng) < std::exp((score.cost()-trial.cost())/temperature)) {
                c = next; score = trial;
            }
            if (trial.miss == 0 && trial.side == 0 && 1024*trial.pair+trial.extra < bestPositive) {
                bestPositive = 1024*trial.pair+trial.extra; save(next,trial,steps,std::string(argv[4])+".positive.json");
                std::cout << "positivebest_pairs " << trial.pair << " MISerrors " << trial.extra << " steps " << steps << " restarts " << runs << " elapsed " << elapsed() << std::endl;
            }
            if (trial.cost() < best) {
                best = trial.cost(); save(next,trial,steps,argv[4]);
                save(next,trial,steps,std::string(argv[4])+".step-"+std::to_string(steps)+".json");
                if(trial.miss==0 && trial.side==0){base=next;hasBase=true;}
                std::cout << "best " << best << " missedges " << trial.miss << " pure_side_errors " << trial.side << " bad_pairs " << trial.pair << " falsepositives " << trial.extra
                          << " steps " << steps << " restarts " << runs << " elapsed " << elapsed() << std::endl;
            }
            if (trial.cost() == 0) return 0;
            if (steps%100000 == 0 && elapsed() >= seconds) goto done;
        }
    }
done:
    std::cout << "END cost " << best << " steps " << steps << " restarts " << runs << " elapsed " << elapsed() << std::endl;
}
