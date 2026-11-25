#include <array>
#include <cstdint>
#include <iostream>
#include <string>

struct Gate { int op, a, b; };
std::array<uint32_t,10> values;
std::array<std::array<unsigned,4>,10> reads;
std::array<Gate,5> gates;
uint32_t target;
uint64_t visited, solutions, bad, fixed_bad, improper;
bool printed;

bool below(int w) { return !(values[w]&~target); }

void search(int depth, int limit) {
  const int w=5+depth;
  for (int a=0;a<w;a++) for (int b=a+1;b<w;b++) for (int op=0;op<2;op++) {
    const uint32_t value=op ? (values[a]|values[b]) : (values[a]&values[b]);
    if (depth+1==limit && value!=target) continue;
    bool redundant=false;
    for (int k=0;k<w;k++) if (values[k]==value) redundant=true;
    if (redundant) continue;
    visited++;
    values[w]=value;
    gates[depth]={op,a,b};
    for (int e=0;e<4;e++) {
      const unsigned x=reads[a][e],y=reads[b][e];
      reads[w][e]=op ? (x|y) : ((((x&1)&&(y&2))||((x&2)&&(y&1))) ? 4 : 0);
    }
    if (depth+1==limit) {
      solutions++;
      bool nonread=false,lift=false,and_below=false;
      for (int e=0;e<4;e++) if (!(reads[w][e]&4)) nonread=true;
      for (int k=0;k<limit;k++) {
        Gate g=gates[k];
        if (g.op && !below(5+k) && (below(g.a)||below(g.b))) lift=true;
        if (!g.op && (below(g.a)||below(g.b))) and_below=true;
      }
      if (and_below) improper++;
      if (nonread) bad++;
      if (nonread && !lift) {
        fixed_bad++;
        if (!printed) {
          printed=true;
          std::cout<<"NONREAD1_FIXED size="<<limit<<"\n";
          for (int k=0;k<limit;k++) std::cout<<gates[k].op<<" "<<gates[k].a<<" "<<gates[k].b<<"\n";
        }
      }
    } else search(depth+1,limit);
  }
}

int main(int argc,char**argv) {
  int edges[4][2]={{0,1},{1,2},{2,3},{3,4}};
  if (argc>1 && std::string(argv[1])=="fork") { edges[3][0]=2;edges[3][1]=4; }
  for (int i=0;i<5;i++) {
    values[i]=0;
    for (int x=0;x<32;x++) if (x&(1<<i)) values[i]|=uint32_t(1u<<x);
    for (int e=0;e<4;e++) reads[i][e]=(i==edges[e][0]?1:0)|(i==edges[e][1]?2:0);
  }
  target=0;
  for (int e=0;e<4;e++) target|=values[edges[e][0]]&values[edges[e][1]];
  for (int limit=1;limit<=5;limit++) {
    visited=solutions=bad=fixed_bad=improper=0;printed=false;
    search(0,limit);
    std::cout<<"size="<<limit<<" visited="<<visited<<" solutions="<<solutions
      <<" nonread1="<<bad<<" nonread1_fixed="<<fixed_bad<<" and_operand_below="<<improper<<"\n";
    if (solutions) break;
  }
}
