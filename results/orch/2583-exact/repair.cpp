#include "cadical-2.1.2.hpp"
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <vector>

using VI = std::vector<int>;
using Clock = std::chrono::steady_clock;
struct Gate { int op, a, b; }; // AND = 0, OR = 1.
struct Row { uint64_t input; bool value; };
struct Problem {
  int inputs, output;
  std::vector<Gate> gates;
  std::vector<Row> rows;
  explicit Problem(const char *path) {
    std::ifstream in(path);
    int m, nr;
    if (!(in >> inputs >> m >> output >> nr) || inputs < 1 || inputs > 60 ||
        m < 1 || nr < 1 || output < 0 || output >= inputs+m)
      throw std::runtime_error("invalid problem header");
    for (int i=0; i<m; ++i) {
      Gate g;
      if (!(in >> g.op >> g.a >> g.b) || g.op < 0 || g.op > 1 ||
          g.a < 0 || g.b < 0 || g.a >= inputs+i || g.b >= inputs+i)
        throw std::runtime_error("invalid seed gate");
      if (g.a > g.b) std::swap(g.a,g.b);
      gates.push_back(g);
    }
    std::set<uint64_t> seen;
    for (int i=0; i<nr; ++i) {
      uint64_t x; int value;
      if (!(in >> x >> value) || (value != 0 && value != 1) ||
          x >= (uint64_t(1)<<inputs) || !seen.insert(x).second)
        throw std::runtime_error("invalid or duplicate test row");
      rows.push_back({x, bool(value)});
    }
  }
};
struct Deadline : CaDiCaL::Terminator {
  Clock::time_point end;
  explicit Deadline(int seconds) : end(Clock::now()+std::chrono::seconds(seconds)) {}
  bool terminate() override { return Clock::now() >= end; }
};
struct Synth {
  const Problem &p;
  CaDiCaL::Solver solver;
  int variables=0;
  uint64_t clauses=0;
  std::vector<VI> left, right;
  VI op, changes;
  std::set<int> samples;
  int var() { return ++variables; }
  VI vars(int n) { VI v; while(n--) v.push_back(var()); return v; }
  void clause(const VI &xs) { for (int x:xs) solver.add(x); solver.add(0); ++clauses; }
  void clause(std::initializer_list<int> xs) { clause(VI(xs)); }
  // Exact-one selectors with a linear prefix counter.  Prefix[k] means one of
  // selectors[0..k] is true; forbidding previous-prefix AND selector gives AMO.
  VI one(const VI &selectors) {
    VI prefix=vars(selectors.size());
    for (int i=0; i<int(selectors.size()); ++i) {
      clause({-selectors[i],prefix[i]});
      if (!i) clause({-prefix[i],selectors[i]});
      else {
        clause({-prefix[i-1],prefix[i]});
        clause({-prefix[i],prefix[i-1],selectors[i]});
        clause({-prefix[i-1],-selectors[i]});
      }
    }
    clause({prefix.back()}); return prefix;
  }
  void at_most(const VI &xs, int k) {
    if (k<0) { clause({}); return; }
    if (!k) { for (int x:xs) clause({-x}); return; }
    if (k>=int(xs.size())) return;
    VI previous;
    for (int i=0; i<int(xs.size()); ++i) {
      VI current=vars(std::min(i+1,k));
      clause({-xs[i],current[0]});
      for (int j=0; j<int(previous.size()); ++j) {
        clause({-previous[j],current[j]});
        if (j+1<int(current.size())) clause({-xs[i],-previous[j],current[j+1]});
        else clause({-xs[i],-previous[j]});
      }
      previous=std::move(current);
    }
  }
  void mux(int result, const VI &selectors, const VI &values) {
    for (int j=0; j<int(selectors.size()); ++j) {
      clause({-selectors[j],-result,values[j]});
      clause({-selectors[j],result,-values[j]});
    }
  }
  Synth(const Problem &problem, int distance, int seed, Deadline &deadline) : p(problem) {
    solver.set("quiet",1); solver.set("seed",seed); solver.configure("sat");
    solver.connect_terminator(&deadline);
    for (int i=0; i<int(p.gates.size()); ++i) {
      left.push_back(vars(p.inputs+i)); right.push_back(vars(p.inputs+i));
      VI lp=one(left.back()); one(right.back());
      // Commutativity only: left <= right.  Equal-source identity gates remain
      // allowed, as do unused gates, so this search includes padded shorter DAGs.
      for (int j=0; j<p.inputs+i; ++j) clause({-right[i][j],lp[j]});
      int a=var(), c=var(); op.push_back(a); changes.push_back(c);
      Gate g=p.gates[i];
      int sameop=g.op==0 ? a : -a, samel=left[i][g.a], samer=right[i][g.b];
      clause({c,sameop}); clause({c,samel}); clause({c,samer});
      clause({-c,-sameop,-samel,-samer});
    }
    at_most(changes,distance);
    for (int i=0; i<int(p.gates.size()); ++i) {
      for (int v:left[i]) solver.freeze(v);
      for (int v:right[i]) solver.freeze(v);
      solver.freeze(op[i]);
    }
  }
  void sample(int index) {
    if (!samples.insert(index).second) return;
    Row row=p.rows[index]; VI values=vars(p.inputs+p.gates.size());
    for (int k=0; k<p.inputs; ++k) clause({(row.input>>k)&1 ? values[k] : -values[k]});
    for (int i=0; i<int(p.gates.size()); ++i) {
      int a=var(),b=var(),z=values[p.inputs+i],o=op[i];
      mux(a,left[i],values); mux(b,right[i],values);
      clause({-o,-z,a}); clause({-o,-z,b}); clause({-o,z,-a,-b});
      clause({o,z,-a}); clause({o,z,-b}); clause({o,-z,a,b});
    }
    clause({row.value ? values[p.output] : -values[p.output]});
  }
  std::vector<Gate> model() {
    auto selected=[&](const VI &xs) {
      for (int i=0; i<int(xs.size()); ++i) if (solver.val(xs[i])>0) return i;
      throw std::runtime_error("invalid selector model");
    };
    std::vector<Gate> gs;
    for (int i=0; i<int(op.size()); ++i)
      gs.push_back({solver.val(op[i])>0 ? 0 : 1,selected(left[i]),selected(right[i])});
    return gs;
  }
};
VI bad_rows(const Problem &p, const std::vector<Gate> &gs) {
  VI bad;
  for (int i=0; i<int(p.rows.size()); ++i) {
    VI values;
    for (int k=0; k<p.inputs; ++k) values.push_back((p.rows[i].input>>k)&1);
    for (Gate g:gs) values.push_back(g.op==0 ? values[g.a]&values[g.b] : values[g.a]|values[g.b]);
    if (bool(values[p.output])!=p.rows[i].value) bad.push_back(i);
  }
  return bad;
}
void write_candidate(const std::filesystem::path &path,const Problem &p,
                     const std::vector<Gate> &gs,const VI &bad) {
  std::ofstream out(path);
  out << "{\"inputs\":" << p.inputs << ",\"output\":" << p.output << ",\"gates\":[";
  for (int i=0; i<int(gs.size()); ++i) {
    if(i) out << ',';
    out << "{\"op\":\"" << (gs[i].op==0 ? "and" : "or") << "\",\"a\":" << gs[i].a
        << ",\"b\":" << gs[i].b << '}';
  }
  out << "],\"bad_rows\":[";
  for (int i=0; i<int(bad.size()); ++i) { if(i) out << ','; out << bad[i]; }
  out << "]}\n";
}
int main(int argc,char **argv) {
  try {
    if(argc<5) { std::cerr << "usage: repair problem.txt max-changed-gates seconds output-dir [seed] [all|edges]\n"; return 2; }
    Problem p(argv[1]); int distance=std::stoi(argv[2]),seconds=std::stoi(argv[3]);
    int seed=argc>5 ? std::stoi(argv[5]) : 98;
    if(distance<0 || distance>int(p.gates.size()) || seconds<1) throw std::runtime_error("invalid limits");
    std::filesystem::path out(argv[4]); std::filesystem::create_directories(out);
    auto start=Clock::now(); Deadline deadline(seconds); Synth c(p,distance,seed,deadline);
    if(argc>6 && std::string(argv[6])=="all") for(int i=0;i<int(p.rows.size());++i)c.sample(i);
    else {
      std::mt19937 rng(seed);
      for(int value=0;value<2;++value) {
        VI rows; for(int i=0;i<int(p.rows.size());++i)if(p.rows[i].value==bool(value))rows.push_back(i);
        std::shuffle(rows.begin(),rows.end(),rng);
        int count=(argc>6 && std::string(argv[6])=="edges" && value==1) ? int(rows.size()) : std::min(8,int(rows.size()));
        for(int j=0;j<count;++j)c.sample(rows[j]);
      }
    }
    int round=0;
    auto metrics=[&]() {
      std::cout << " wall " << std::chrono::duration<double>(Clock::now()-start).count()
                << " cpu " << double(std::clock())/CLOCKS_PER_SEC << std::endl;
    };
    while(!deadline.terminate()) {
      std::cout << "round " << round << " samples " << c.samples.size() << " vars " << c.variables << " clauses " << c.clauses; metrics();
      c.solver.limit("conflicts",100000); int result=c.solver.solve();
      std::cout << "solve " << result; metrics();
      if(result==20) { std::cout << "UNSAT bounded gate-edit neighborhood\n"; return 0; }
      if(!result)continue;
      auto gs=c.model(); VI bad=bad_rows(p,gs);
      for(int row:bad)if(c.samples.count(row))throw std::runtime_error("model fails encoded row");
      write_candidate(out/("candidate-"+std::to_string(round)+".json"),p,gs,bad);
      std::cout << "candidate " << round << " basis_errors " << bad.size() << std::endl;
      if(bad.empty()) { write_candidate(out/"WITNESS.json",p,gs,bad); std::cout << "WITNESS complete supplied basis verified";metrics();return 0; }
      int added[2]={0,0};
      for(int row:bad)if(added[p.rows[row].value]<4) { ++added[p.rows[row].value];c.sample(row); }
      ++round;
    }
    std::cout << "UNKNOWN wall deadline"; metrics(); return 0;
  } catch(const std::exception &e) { std::cerr << e.what() << '\n'; return 2; }
}
