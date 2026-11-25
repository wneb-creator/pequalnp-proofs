#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include "cadical.hpp"
class Watch final : public CaDiCaL::Terminator {
public:
  std::chrono::steady_clock::time_point end;
  bool terminate() override { return std::chrono::steady_clock::now() >= end; }
};
int main(int argc,char** argv) {
  if(argc!=4) {std::cout<<"usage: phase_server CNF PHASES FROZEN\n";return 2;}
  CaDiCaL::Solver solver;
  int variables=0;
  const char* error=solver.read_dimacs(argv[1],variables);
  if(error){std::cerr<<error<<'\n';return 2;}
  std::ifstream phases(argv[2]),frozen(argv[3]);
  if(!phases||!frozen){std::cerr<<"cannot read phases or frozen variables\n";return 2;}
  int literal;
  while(phases>>literal)solver.phase(literal);
  std::vector<int> model_variables;
  while(frozen>>literal){solver.freeze(literal);model_variables.push_back(std::abs(literal));}
  Watch watch;solver.connect_terminator(&watch);
  std::string command;
  while(std::cin>>command) {
    if(command=="quit")break;
    if(command=="add") {
      int clauses;std::cin>>clauses;
      for(int i=0;i<clauses;++i) {
        do {
          if(!(std::cin>>literal)){std::cerr<<"incomplete clause command\n";return 2;}
          solver.add(literal);variables=std::max(variables,std::abs(literal));
        } while(literal);
      }
    } else if(command=="phase") {
      int count;std::cin>>count;
      for(int i=0;i<count;++i) {
        if(!(std::cin>>literal)){std::cerr<<"incomplete phase command\n";return 2;}
        solver.phase(literal);
      }
    } else if(command=="solve") {
      int seconds,conflicts;std::cin>>seconds>>conflicts;
      watch.end=std::chrono::steady_clock::now()+std::chrono::seconds(seconds);
      solver.limit("conflicts",conflicts);
      int result=solver.solve();solver.statistics();
      std::cout<<"c OEC_RESULT "<<result<<' '<<variables<<'\n';
      if(result==10) {
        std::cout<<"c OEC_MODEL_FROZEN_ONLY "<<model_variables.size()<<'\n';
        std::cout<<"v ";
        for(int v:model_variables)std::cout<<solver.val(v)<<' ';
        std::cout<<"0\n";
      }
      std::cout<<"c OEC_DONE\n"<<std::flush;
    } else {std::cerr<<"unknown command\n";return 2;}
  }
  return 0;
}
