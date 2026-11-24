#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

// Candidate heuristic only. No failed run implies UNSAT or shard exhaustion.
namespace {
constexpr int N=11, OFFSET=13, GATES=21;
constexpr std::array<std::array<int,2>,16> EDGES={{{0,9},{0,10},{1,4},{1,8},
 {2,5},{2,10},{3,6},{3,7},{4,8},{4,10},{5,8},{5,9},{6,7},{6,10},{7,9},{8,9}}};
struct Gate { int op,a,b; }; // 1=AND, 0=OR; constants are wires 11 and 12.
struct Circuit { std::array<Gate,GATES> gates; int output; };
struct Baseline { std::array<Gate,22> gates; int output; };
struct Score { int fn,fp,live; double energy; };
volatile std::sig_atomic_t stopped=0;
void stop(int) { stopped=1; }
bool target(int mask) {
 for (auto e:EDGES) if ((mask&(1<<e[0])) && (mask&(1<<e[1]))) return true;
 return false;
}
bool scalar(const Gate* gates,int count,int output,int mask) {
 std::array<bool,35> w{};
 for(int i=0;i<N;++i) w[i]=(mask&(1<<i))!=0;
 w[12]=true;
 for(int g=0;g<count;++g) {
  auto t=gates[g];
  if(t.op<0 || t.op>1 || t.a<0 || t.b<0 || t.a>=OFFSET+g || t.b>=OFFSET+g)
   throw std::runtime_error("Invalid gate in scalar evaluation");
  w[OFFSET+g]=t.op ? w[t.a]&&w[t.b] : w[t.a]||w[t.b];
 }
 if(output<0 || output>=OFFSET+count) throw std::runtime_error("Invalid output");
 return w[output];
}
bool scalar_with_alias(const Baseline& b,int removed,int alias,int mask) {
 std::array<bool,35> w{};
 for(int i=0;i<N;++i)w[i]=(mask&(1<<i))!=0;
 w[12]=true;
 for(int g=0;g<22;++g) {
  auto t=b.gates[g];
  w[OFFSET+g]=g==removed?w[alias]:(t.op?w[t.a]&&w[t.b]:w[t.a]||w[t.b]);
 }
 return w[b.output];
}
std::vector<int> boundary_rows() {
 std::vector<int> rows;
 for(auto e:EDGES) rows.push_back((1<<e[0])|(1<<e[1]));
 for(int mask=0;mask<(1<<N);++mask) if(!target(mask)) {
  bool maximal=true;
  for(int v=0;v<N;++v) if(!(mask&(1<<v)) && !target(mask|(1<<v))) maximal=false;
  if(maximal) rows.push_back(mask);
 }
 if(rows.size()!=40) throw std::runtime_error("Unexpected boundary size");
 return rows;
}
struct Engine {
 std::mt19937_64 rng;
 std::array<uint64_t,OFFSET> inputs{};
 const uint64_t positives=(uint64_t(1)<<16)-1;
 const uint64_t all=(uint64_t(1)<<40)-1;
 explicit Engine(uint64_t seed):rng(seed) {
  auto rows=boundary_rows();
  for(int v=0;v<N;++v) for(size_t i=0;i<rows.size();++i)
   if(rows[i]&(1<<v)) inputs[v]|=uint64_t(1)<<i;
  inputs[12]=all;
 }
 int pick(int n) { if(n<=0)throw std::runtime_error("Empty random choice"); return int(rng()%uint64_t(n)); }
 double uniform() { return double(rng()>>11)*0x1.0p-53; }
 uint64_t vector_eval(const Gate* gates,int count,int output) const {
  std::array<uint64_t,35> w{};std::copy(inputs.begin(),inputs.end(),w.begin());
  for(int g=0;g<count;++g) {
   auto t=gates[g];w[OFFSET+g]=t.op ? w[t.a]&w[t.b] : w[t.a]|w[t.b];
  }
  return w[output];
 }
 std::array<bool,GATES> live(const Circuit& c) const {
  std::array<bool,GATES> bits{};
  if(c.output>=OFFSET) bits[c.output-OFFSET]=true;
  for(int g=GATES-1;g>=0;--g) if(bits[g])
   for(int a:{c.gates[g].a,c.gates[g].b}) if(a>=OFFSET) bits[a-OFFSET]=true;
  return bits;
 }
 Score score(const Circuit& c,int weight) const {
  uint64_t v=vector_eval(c.gates.data(),GATES,c.output);
  int fn=__builtin_popcountll(positives&~v);
  int fp=__builtin_popcountll((all^positives)&v);
  auto bits=live(c);int count=std::count(bits.begin(),bits.end(),true);
  // A strict fractional tie-breaker; one boundary error always dominates it.
  return {fn,fp,count,double(weight*fn+fp)+0.02*count};
 }
 Circuit remove_gate(const Baseline& b,int remove,int alias) const {
  Circuit c{};
  auto map=[&](int wire) {
   if(wire==OFFSET+remove) wire=alias;
   if(wire>OFFSET+remove)--wire;
   return wire;
  };
  int j=0;
  for(int g=0;g<22;++g) if(g!=remove) {
   Gate t=b.gates[g];t.a=map(t.a);t.b=map(t.b);
   if(t.a>t.b)std::swap(t.a,t.b);
   c.gates[j++]=t;
  }
  c.output=map(b.output);return c;
 }
 Circuit initial(const Baseline& b) {
  int g=pick(22),mode=pick(3);
  int alias=mode==0?b.gates[g].a:mode==1?b.gates[g].b:pick(OFFSET+g);
  return remove_gate(b,g,alias);
 }
 Circuit mutate(const Circuit& c) {
  Circuit next=c;int move=pick(100);
  if(move<4) {next.output=pick(OFFSET+GATES);return next;}
  int g=pick(GATES);
  if(pick(5)!=0) {
   auto bits=live(c);std::array<int,GATES> candidates{};int count=0;
   for(int i=0;i<GATES;++i)if(bits[i])candidates[count++]=i;
   if(count)g=candidates[pick(count)];
  }
  auto &t=next.gates[g];
  if(move<17)t.op^=1;
  else if(move<52)t.a=pick(OFFSET+g);
  else if(move<87)t.b=pick(OFFSET+g);
  else {t.op=pick(2);t.a=pick(OFFSET+g);t.b=pick(OFFSET+g);}
  if(t.a>t.b)std::swap(t.a,t.b);
  return next;
 }
};
std::vector<Baseline> load(const std::string& path) {
 std::ifstream f(path);std::string magic;int version=0,count=0;
 if(!(f>>magic>>version>>count) || magic!="COVER_ANNEAL" || version!=1 || count<1 || count>10000)
  throw std::runtime_error("Invalid seed pack header");
 std::vector<Baseline> all(count);
 for(auto& b:all) {
  int gates=0;if(!(f>>gates>>b.output) || gates!=22)throw std::runtime_error("Invalid baseline header");
  for(auto& t:b.gates)if(!(f>>t.op>>t.a>>t.b))throw std::runtime_error("Truncated baseline");
  for(int x=0;x<(1<<N);++x)if(scalar(b.gates.data(),22,b.output,x)!=target(x))
   throw std::runtime_error("Seed baseline fails all-input validation");
 }
 std::string extra;if(f>>extra)throw std::runtime_error("Trailing pack content");
 return all;
}
void write_result(const std::string& path,const Circuit& c,const Score& score,
 const std::string& status,uint64_t seed,uint64_t iterations,int restarts,double elapsed,int weight) {
 std::ofstream f(path);if(!f)throw std::runtime_error("Cannot write result");
 f<<"{\n  \"status\": \""<<status<<"\",\n  \"inputs\": 11,\n  \"candidate_only\": true,\n"
  <<"  \"assigned_shard_exhaustion\": false,\n  \"requires_Lean_proof\": true,\n"
  <<"  \"seed\": "<<seed<<",\n  \"iterations\": "<<iterations<<",\n  \"restarts\": "<<restarts
  <<",\n  \"elapsed_seconds\": "<<elapsed<<",\n  \"positive_weight\": "<<weight
  <<",\n  \"false_negatives\": "<<score.fn<<",\n  \"false_positives\": "<<score.fp
  <<",\n  \"live_gates\": "<<score.live<<",\n  \"size\": 21,\n  \"output\": "<<c.output
  <<",\n  \"gate_wire_offset\": 13,\n  \"gates\": [\n";
 for(int g=0;g<GATES;++g) {auto t=c.gates[g];f<<"    [\""<<(t.op?"and":"or")<<"\", "<<t.a<<", "<<t.b<<"]"<<(g+1<GATES?",":"")<<"\n";}
 f<<"  ]\n}\n";if(!f)throw std::runtime_error("Result write failed");
}
}
int main(int argc,char** argv) try {
 std::string pack,output;uint64_t seed=1342,max_iterations=100000000;
 double seconds=60;int period=100000,weight=4;bool selftest=false;
 for(int i=1;i<argc;++i) {
  std::string arg=argv[i];
  if(arg=="--help") {
   std::cout<<"circuit_anneal --pack FILE --output NEWFILE [--seed N] [--seconds N] [--iterations N] [--restart N] [--weight 1..16] [--self-test]\n";return 0;
  }
  if(arg=="--self-test") {selftest=true;continue;}
  if(i+1==argc)throw std::runtime_error("Missing option value");
  std::string value=argv[++i];
  if(arg=="--pack")pack=value;else if(arg=="--output")output=value;
  else if(arg=="--seed")seed=std::stoull(value);else if(arg=="--seconds")seconds=std::stod(value);
  else if(arg=="--iterations")max_iterations=std::stoull(value);
  else if(arg=="--restart")period=std::stoi(value);else if(arg=="--weight")weight=std::stoi(value);
  else throw std::runtime_error("Unknown option");
 }
 if(pack.empty() || output.empty() || !std::isfinite(seconds) || seconds<=0 || seconds>3600 ||
    max_iterations==0 || max_iterations>1000000000000ULL || period<100 || period>10000000 || weight<1 || weight>16)
  throw std::runtime_error("Invalid bounded configuration");
 {std::ifstream existing(output);if(existing.good())throw std::runtime_error("Output must be fresh");}
 std::signal(SIGINT,stop);std::signal(SIGTERM,stop);
 auto start=std::chrono::steady_clock::now();
 auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 auto baselines=load(pack);Engine engine(seed);
 if(selftest) {
  uint64_t comparisons=0,mutations=0;
  for(const auto& b:baselines) {
   if(engine.vector_eval(b.gates.data(),22,b.output)!=engine.positives)throw std::runtime_error("Baseline vector mismatch");
   for(int g=0;g<22;++g)for(int alias:{b.gates[g].a,b.gates[g].b,0,11,12}) {
    Circuit c=engine.remove_gate(b,g,alias);auto rows=boundary_rows();uint64_t scalar_bits=0;
    for(size_t i=0;i<rows.size();++i) {
     bool value=scalar(c.gates.data(),GATES,c.output,rows[i]);
     if(value!=scalar_with_alias(b,g,alias,rows[i]))throw std::runtime_error("Deletion renumbering mismatch");
     if(value)scalar_bits|=uint64_t(1)<<i;
    }
    if(scalar_bits!=engine.vector_eval(c.gates.data(),GATES,c.output))throw std::runtime_error("Deletion/vector mismatch");
    ++comparisons;
    c=engine.mutate(c);scalar_bits=0;
    for(size_t i=0;i<rows.size();++i)if(scalar(c.gates.data(),GATES,c.output,rows[i]))scalar_bits|=uint64_t(1)<<i;
    if(scalar_bits!=engine.vector_eval(c.gates.data(),GATES,c.output))throw std::runtime_error("Mutation/vector mismatch");
    ++mutations;
   }
  }
  std::ofstream f(output);f<<"{\"status\":\"SELF_TEST_PASS\",\"baselines\":"<<baselines.size()<<",\"deletion_controls\":"<<comparisons<<",\"mutation_controls\":"<<mutations<<"}\n";
  std::cout<<"SELF_TEST_PASS baselines="<<baselines.size()<<" deletion_controls="<<comparisons<<" mutation_controls="<<mutations<<"\n";return 0;
 }
 Circuit current=engine.initial(baselines[engine.pick(int(baselines.size()))]);
 Score current_score=engine.score(current,weight);Circuit best=current;Score best_score=current_score;
 uint64_t iteration=0;int restarts=0,best_serial=0;std::string status="UNKNOWN";
 auto snapshot=[&]() {
  std::string path=output+".best-"+std::to_string(best_serial++)+".json";
  write_result(path,best,best_score,"BEST_PARTIAL_NOT_A_WITNESS",seed,iteration,restarts,elapsed(),weight);
  std::cout<<"BEST_FILE "<<path<<"\n"<<std::flush;
 };
 snapshot();
 for(;iteration<max_iterations;++iteration) {
  if((iteration&1023)==0 && (stopped || elapsed()>=seconds)) {status=stopped?"ABORTED":"UNKNOWN";break;}
  if(current_score.fn==0 && current_score.fp==0) {
   for(int x=0;x<(1<<N);++x)if(scalar(current.gates.data(),GATES,current.output,x)!=target(x))
    throw std::runtime_error("Boundary candidate fails full truth table");
   best=current;best_score=current_score;status="CANDIDATE_NEEDS_INDEPENDENT_VALIDATION";break;
  }
  if(iteration && iteration%uint64_t(period)==0) {
   ++restarts;
   if(engine.pick(4)==0) {current=best;for(int k=0;k<3;++k)current=engine.mutate(current);}
   else current=engine.initial(baselines[engine.pick(int(baselines.size()))]);
   current_score=engine.score(current,weight);
   if(current_score.energy<best_score.energy) {best=current;best_score=current_score;snapshot();}
   if(current_score.fn==0 && current_score.fp==0) {best=current;best_score=current_score;break;}
  }
  Circuit next=engine.mutate(current);Score next_score=engine.score(next,weight);
  double fraction=double(iteration%uint64_t(period))/period;
  double temperature=0.08+2.5*(1.0-fraction)*(1.0-fraction);
  double delta=next_score.energy-current_score.energy;
  if(delta<=0 || engine.uniform()<std::exp(-delta/temperature)) {current=next;current_score=next_score;}
  if(current_score.energy<best_score.energy) {
   best=current;best_score=current_score;
   snapshot();
  }
 }
 // A candidate on the final permitted mutation must not be lost at the limit.
 if(best_score.fn==0 && best_score.fp==0) {
  for(int x=0;x<(1<<N);++x)if(scalar(best.gates.data(),GATES,best.output,x)!=target(x))
   throw std::runtime_error("Best candidate fails full truth table");
  status="CANDIDATE_NEEDS_INDEPENDENT_VALIDATION";
 }
 write_result(output,best,best_score,status,seed,iteration,restarts,elapsed(),weight);
 if(status=="CANDIDATE_NEEDS_INDEPENDENT_VALIDATION")std::cout<<output<<"\n";
 else std::cout<<status<<" iterations="<<iteration<<" restarts="<<restarts<<" elapsed="<<elapsed()<<"\n";
 return status=="CANDIDATE_NEEDS_INDEPENDENT_VALIDATION"?10:0;
} catch(const std::exception& error) {std::cerr<<"ERROR: "<<error.what()<<"\n";return 2;}
