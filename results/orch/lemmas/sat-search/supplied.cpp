#include "cadical.hpp"
#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <chrono>
#include <cstdlib>
using namespace std;
struct Timer : CaDiCaL::Terminator {chrono::steady_clock::time_point until;bool terminate() override{return chrono::steady_clock::now()>until;}};
struct Gate {int op,a,b;};
struct Supplied {
 int n=13,s=7,vars=0,config;CaDiCaL::Solver sat;Timer timer;
 vector<Gate> base;vector<array<int,3>> ops;vector<vector<int>> as,bs;
 int var(){return ++vars;}
 void one(const vector<int>&v){sat.clause(v);for(size_t i=0;i<v.size();i++)for(size_t j=i+1;j<v.size();j++)sat.clause(-v[i],-v[j]);}
 array<bool,4> target(int x){bool a=x&1,b=x>>1&1,c=x>>2&1,d=x>>3&1,e=x>>4&1,f=x>>5&1,t=x>>6&1;return{b||d||f,a||b||c,a||e||f,(t&&(d||c||e))||(a&&d)||(b&&e)||(c&&f)};}
 Supplied(int cfg,int seed,int gates=7,string hint=""):s(gates),config(cfg){
  sat.set("quiet",1);sat.set("seed",seed);sat.connect_terminator(&timer);
  int triples[3][3]={{1,3,5},{0,1,2},{0,4,5}},pair[3][3]={{0,1,2},{0,2,1},{1,2,0}};
  for(int k=0;k<3;k++){int choice=cfg%3;cfg/=3;int a=triples[k][pair[choice][0]],b=triples[k][pair[choice][1]],c=triples[k][pair[choice][2]];base.push_back({1,a,b});base.push_back({1,c,7+2*k});}
  ops.resize(s);as.resize(s);bs.resize(s);
  for(int i=0;i<s;i++){
   for(int j=0;j<3;j++){ops[i][j]=var();sat.freeze(ops[i][j]);}one({ops[i][0],ops[i][1],ops[i][2]});
   for(int j=0;j<n+i;j++){as[i].push_back(var());bs[i].push_back(var());sat.freeze(as[i][j]);sat.freeze(bs[i][j]);}one(as[i]);one(bs[i]);
   for(int a=0;a<n+i;a++)for(int b=0;b<n+i;b++){
    if(a>b)sat.clause(-as[i][a],-bs[i][b]);
    if(a==b)sat.clause(-as[i][a],-bs[i][b],ops[i][2]);else sat.clause(-ops[i][2],-as[i][a],-bs[i][b]);
   }
  }
  vector<int> nots;for(auto op:ops)nots.push_back(op[2]);one(nots);sat.clause(-ops[s-1][2]);
  for(int i=0;i<s-1;i++){vector<int> use;for(int j=i+1;j<s;j++){use.push_back(as[j][n+i]);use.push_back(bs[j][n+i]);}sat.clause(use);}
  if(hint.empty())for(int i=0;i<s-1;i++)for(int a=0;a<n+i;a++)for(int b=0;b<a;b++)sat.clause(-bs[i][a],-bs[i+1][b]);
  if(!hint.empty()){ifstream f(hint);for(int i=0;i<s;i++){int out,op,a,b;f>>out>>op>>a>>b;if(op==2)b=a;else if(a>b)swap(a,b);sat.clause(ops[i][op]);sat.clause(as[i][a]);sat.clause(bs[i][b]);}}
  for(int x=0;x<128;x++)instance(x);
 }
 void instance(int x){
  bool input[13];for(int i=0;i<7;i++)input[i]=x>>i&1;for(int i=0;i<6;i++)input[7+i]=input[base[i].a]||input[base[i].b];
  vector<int> val(n+s,0);
  for(int i=0;i<s;i++){
   int l=var(),r=var(),v=var();val[n+i]=v;
   for(int j=0;j<n+i;j++)for(int z=0;z<2;z++){
    int sel=z?bs[i][j]:as[i][j],zval=z?r:l;
    if(j<n)sat.clause(-sel,input[j]?zval:-zval);else{sat.clause(-sel,-zval,val[j]);sat.clause(-sel,zval,-val[j]);}
   }
   int a=ops[i][0],o=ops[i][1],neg=ops[i][2];
   sat.clause(-a,-l,-r,v);sat.clause(-a,l,-v);sat.clause(-a,r,-v);
   sat.clause(-o,l,r,-v);sat.clause(-o,-l,v);sat.clause(-o,-r,v);
   sat.clause(-neg,l,v);sat.clause(-neg,-l,-v);
  }
  sat.clause(target(x)[3]?val.back():-val.back());
 }
 void run(int seconds){
  auto start=chrono::steady_clock::now();timer.until=start+chrono::seconds(seconds);
  cout<<"SOLVE supplied-config="<<config<<" unknown-gates="<<s<<" vars="<<vars<<endl;int result=sat.solve();
  cout<<"RESULT "<<result<<" elapsed="<<chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-start).count()<<endl;
  if(result!=10)return;
  vector<Gate> gs=base;
  for(int i=0;i<s;i++){Gate g={-1,-1,-1};for(int j=0;j<3;j++)if(sat.val(ops[i][j])>0)g.op=j;for(int j=0;j<n+i;j++){if(sat.val(as[i][j])>0)g.a=j;if(sat.val(bs[i][j])>0)g.b=j;}gs.push_back(g);}
  vector<int> os={8,10,12,n+s-1};int bad=0;
  for(int x=0;x<128;x++){bool v[100];for(int i=0;i<7;i++)v[i]=x>>i&1;for(int i=0;i<(int)gs.size();i++){auto g=gs[i];v[7+i]=g.op==0?v[g.a]&&v[g.b]:g.op==1?v[g.a]||v[g.b]:!v[g.a];}auto t=target(x);for(int k=0;k<4;k++)bad+=v[os[k]]!=t[k];}
  cout<<"INDEPENDENT_CHECK_ERRORS "<<bad<<endl;
  for(int i=0;i<(int)gs.size();i++){auto g=gs[i];cout<<7+i<<" "<<g.op<<" "<<g.a<<" "<<g.b<<"\n";}cout<<"OUTPUTS";for(int o:os)cout<<" "<<o;cout<<endl;
 }
};
int main(int argc,char**argv){int config=argc>1?atoi(argv[1]):0;int seed=argc>2?atoi(argv[2]):1;int seconds=argc>3?atoi(argv[3]):60;int gates=argc>4?atoi(argv[4]):7;string hint=argc>5?argv[5]:"";Supplied(config,seed,gates,hint).run(seconds);}
