#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using U = std::uint64_t;
struct Gate { int op, a, b; };
int main(int argc, char **argv) {
  std::ifstream in(argv[1]);
  int n,m,out,R; in>>n>>m>>out>>R;
  std::vector<U> inputs(n);
  U target=0, mask=R==64?~U(0):(U(1)<<R)-1;
  for(int t=0;t<R;t++) {
    unsigned row; int y; in>>row>>y;
    if(y) target|=U(1)<<t;
    for(int i=0;i<n;i++) if(row>>i&1) inputs[i]|=U(1)<<t;
  }
  std::vector<Gate> gates(m);
  for(auto &g:gates) in>>g.op>>g.a>>g.b;
  auto eval=[&](int del,int alias,int cut,U val) {
    auto v=inputs;
    for(int j=0;j<m;j++) {
      auto g=gates[j];
      v.push_back(j==cut ? val : j==del ? v[alias] :
                  g.op ? v[g.a]|v[g.b] : v[g.a]&v[g.b]);
    }
    return v;
  };
  if(eval(-1,0,-1,0)[out]!=target) return 2;
  std::uint64_t checked=0, contexts=0;
  for(int del=0;del<m;del++) for(int alias=0;alias<n+del;alias++) {
    auto base=eval(del,alias,-1,0);
    for(int cut=0;cut<m;cut++) if(cut!=del) {
      U lo=eval(del,alias,cut,0)[out],hi=eval(del,alias,cut,mask)[out];
      if((lo&~target)||(target&~hi)) continue;
      U need1=target&~lo,need0=(~target)&hi&mask;
      contexts++;
      for(int a=0;a<n+cut;a++) for(int b=a;b<n+cut;b++) for(int op=0;op<2;op++) {
        U h=op?base[a]|base[b]:base[a]&base[b]; checked++;
        if((h&need1)==need1 && (h&need0)==0) {
          std::cout<<"WITNESS delete "<<del<<" alias "<<alias
                   <<" change "<<cut<<" op "<<op<<" a "<<a<<" b "<<b<<"\n";
          std::cout<<"contexts "<<contexts<<" candidates "<<checked<<"\n";
          return 0;
        }
      }
    }
  }
  std::cout<<"NO REWRITE contexts "<<contexts<<" candidates "<<checked<<"\n";
}
