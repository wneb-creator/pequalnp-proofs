#include <array>
#include <cstdint>
#include <iostream>

struct Gate { int op, a, b; };
std::array<uint16_t,8> values;
std::array<std::array<unsigned,3>,8> reads;
std::array<Gate,4> gates;
uint16_t target;
uint64_t visited, solutions, bad;
bool printed;

void search(int depth, int limit) {
  const int w=4+depth;
  for (int a=0;a<w;a++) for (int b=a+1;b<w;b++) for (int op=0;op<2;op++) {
    const uint16_t value=op ? (values[a]|values[b]) : (values[a]&values[b]);
    bool redundant=false;
    for (int k=0;k<w;k++) if (values[k]==value) redundant=true;
    if (redundant) continue;
    visited++;
    values[w]=value;
    gates[depth]={op,a,b};
    for (int e=0;e<3;e++) {
      const unsigned x=reads[a][e],y=reads[b][e];
      reads[w][e]=op ? (x|y) : ((((x&1)&&(y&2))||((x&2)&&(y&1))) ? 4 : 0);
    }
    if (depth+1==limit) {
      if (value!=target) continue;
      solutions++;
      if (!(reads[w][0]&4)||!(reads[w][1]&4)||!(reads[w][2]&4)) {
        bad++;
        if (!printed) {
          printed=true;
          std::cout<<"NONREAD1 size="<<limit<<"\n";
          for (int k=0;k<limit;k++) std::cout<<gates[k].op<<" "<<gates[k].a<<" "<<gates[k].b<<"\n";
        }
      }
    } else search(depth+1,limit);
  }
}

int main() {
  const int edges[3][2]={{0,1},{0,2},{3,1}};
  for (int i=0;i<4;i++) {
    values[i]=0;
    for (int x=0;x<16;x++) if (x&(1<<i)) values[i]|=uint16_t(1<<x);
    for (int e=0;e<3;e++) reads[i][e]=(i==edges[e][0]?1:0)|(i==edges[e][1]?2:0);
  }
  target=(values[0]&values[1])|(values[0]&values[2])|(values[3]&values[1]);
  for (int limit=1;limit<=4;limit++) {
    visited=solutions=bad=0;printed=false;
    search(0,limit);
    std::cout<<"size="<<limit<<" visited="<<visited<<" solutions="<<solutions<<" nonread1="<<bad<<"\n";
  }
}
