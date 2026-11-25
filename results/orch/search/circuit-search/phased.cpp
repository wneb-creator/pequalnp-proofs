#include "cadical.hpp"
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>

struct Deadline : CaDiCaL::Terminator {
  std::chrono::steady_clock::time_point until;
  explicit Deadline(int seconds) : until(std::chrono::steady_clock::now()+std::chrono::seconds(seconds)) {}
  bool terminate() override { return std::chrono::steady_clock::now()>=until; }
};

int main(int argc,char** argv) {
  if(argc!=4) { std::fprintf(stderr,"usage: phased cnf phases seconds\n"); return 2; }
  CaDiCaL::Solver solver;
  solver.configure("sat");
  int vars=0;
  if(const char* err=solver.read_dimacs(argv[1],vars)) { std::fprintf(stderr,"%s\n",err);return 2; }
  std::ifstream phases(argv[2]);
  int lit;
  while(phases>>lit) solver.phase(lit);
  Deadline deadline(std::atoi(argv[3]));
  solver.connect_terminator(&deadline);
  int result=solver.solve();
  solver.statistics();solver.resources();
  std::printf("s %s\n",result==10 ? "SATISFIABLE" : result==20 ? "UNSATISFIABLE" : "UNKNOWN");
  if(result==10) {
    for(int i=1;i<=vars;i++) {
      if((i-1)%100==0) std::printf("v ");
      std::printf("%d ",solver.val(i));
      if(i%100==0 || i==vars) std::printf("0\n");
    }
  }
  return result;
}
