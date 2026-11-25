#include "cadical.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <array>
#include <chrono>
#include <string>
using namespace std;
struct Timer : CaDiCaL::Terminator { chrono::steady_clock::time_point end; Timer(int s):end(chrono::steady_clock::now()+chrono::seconds(s)){} bool terminate() override {return chrono::steady_clock::now()>end;} };
int main(int argc,char**argv){
 if(argc<5){cerr<<"usage: phase-fano CNF CANDIDATE ROWS SECONDS\n";return 2;}
 const int n=14,s=26;vector<int>rows;ifstream rf(argv[3]);int r;while(rf>>r)rows.push_back(r);const int A=rows.size()+n+s+1;
 auto p=[&](int kd,int j,int a){return (kd*(s+1)+j)*A+a+1;};
 vector<array<int,3>> c;ifstream cand(argv[2]);string line;getline(cand,line);int j,op,a,b;
 while(cand>>j>>op>>a>>b){if(a>b)swap(a,b);c.push_back({op,a,b});}
 if(c.size()!=s||rows.size()!=58){cerr<<"bad candidate or rows\n";return 3;}
 CaDiCaL::Solver solver;solver.set("quiet",1);solver.set("seed",31);solver.configure("sat");
 int vars=0;auto err=solver.read_dimacs(argv[1],vars);if(err){cerr<<err<<"\n";return 4;}
 for(int j=0;j<s;j++){
  for(int q=0;q<3;q++)solver.phase(q==c[j][0]?p(0,j,q):-p(0,j,q));
  for(int q=0;q<=n+j;q++){
   solver.phase(q==c[j][1]?p(1,j,q):-p(1,j,q));
   solver.phase(q==c[j][2]?p(2,j,q):-p(2,j,q));
  }
  solver.phase(c[j][0]==2?p(7,j,0):-p(7,j,0));
 }
 for(int ri=0;ri<(int)rows.size();ri++){
  int r=rows[ri];vector<bool>w;for(int k=0;k<n;k++)w.push_back((r>>k)&1);
  for(int j=0;j<s;j++){
   auto [o,a,b]=c[j];bool av=a<(int)w.size()?w[a]:false,bv=b<(int)w.size()?w[b]:false;
   bool v=o==0?av&&bv:o==1?av||bv:true;w.push_back(v);
   solver.phase(av?p(4,j,ri):-p(4,j,ri));solver.phase(bv?p(5,j,ri):-p(5,j,ri));solver.phase(v?p(3,j,ri):-p(3,j,ri));
  }
 }
 for(int q=0;q<=n+s;q++)solver.phase(q==n+s-1?p(6,0,q):-p(6,0,q));
 Timer timer(atoi(argv[4]));solver.connect_terminator(&timer);int result=solver.solve();cout<<"result "<<result<<"\n";
 if(result==10){
  for(int v=1;v<=vars;v++){
   if((v-1)%16==0)cout<<"v ";cout<<(solver.val(v)>0?v:-v)<<" ";if(v%16==0||v==vars)cout<<"0\n";
  }
 }
 return result;
}
