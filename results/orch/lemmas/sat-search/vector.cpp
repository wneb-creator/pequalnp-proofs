#include "cadical.hpp"
#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <chrono>
#include <algorithm>
#include <numeric>
#include <string>
#include <cstdlib>
using namespace std;
struct Timer : CaDiCaL::Terminator {chrono::steady_clock::time_point until;bool terminate() override{return chrono::steady_clock::now()>until;}};
struct Gate {int op,a,b;};
struct VectorSynth {
 int n=6,s,vars=0;CaDiCaL::Solver sat;Timer timer;
 vector<array<int,3>> ops;vector<vector<int>> as,bs,outs;
 int var(){return ++vars;}
 void one(const vector<int>&v){sat.clause(v);for(size_t i=0;i<v.size();i++)for(size_t j=i+1;j<v.size();j++)sat.clause(-v[i],-v[j]);}
 void atmost(const vector<int>&lits,int budget){
  int m=lits.size();if(budget>=m)return;if(budget==0){for(int x:lits)sat.clause(-x);return;}
  vector<vector<int>> count(m+1,vector<int>(budget+2,0));
  for(int i=1;i<=m;i++)for(int j=1;j<=min(i,budget+1);j++){
   count[i][j]=var();if(j==1)sat.clause(-lits[i-1],count[i][j]);
   if(count[i-1][j])sat.clause(-count[i-1][j],count[i][j]);
   if(j>1&&count[i-1][j-1])sat.clause(-lits[i-1],-count[i-1][j-1],count[i][j]);
  }sat.clause(-count[m][budget+1]);
 }
 array<bool,5> target(int x){bool a=x&1,b=x>>1&1,c=x>>2&1,d=x>>3&1,e=x>>4&1,f=x>>5&1;return{b||d||f,a||b||c,a||e||f,d||c||e,(a&&d)||(b&&e)||(c&&f)};}
 VectorSynth(int gates,int first,int maxnot,int seed,string hint=""):s(gates){
  sat.set("quiet",1);sat.set("seed",seed);sat.connect_terminator(&timer);
  ops.resize(s);as.resize(s);bs.resize(s);outs.resize(5);
  for(int i=0;i<s;i++){
   for(int j=0;j<3;j++){ops[i][j]=var();sat.freeze(ops[i][j]);}one({ops[i][0],ops[i][1],ops[i][2]});
   for(int j=0;j<n+i;j++){as[i].push_back(var());bs[i].push_back(var());sat.freeze(as[i][j]);sat.freeze(bs[i][j]);}one(as[i]);one(bs[i]);
   for(int a=0;a<n+i;a++)for(int b=0;b<n+i;b++){
    if(a>b)sat.clause(-as[i][a],-bs[i][b]);
    if(a==b)sat.clause(-as[i][a],-bs[i][b],ops[i][2]);else sat.clause(-ops[i][2],-as[i][a],-bs[i][b]);
   }
  }
  for(int k=0;k<5;k++){for(int j=0;j<n+s;j++){outs[k].push_back(var());sat.freeze(outs[k][j]);}one(outs[k]);}
  if(abs(maxnot)==1)for(int k=0;k<5;k++)for(int i=0;i<s;i++)sat.clause(-outs[k][n+i],-ops[i][2]);
  vector<int> nots;for(auto op:ops)nots.push_back(op[2]);if(maxnot!=0)sat.clause(nots);atmost(nots,abs(maxnot));
  if(maxnot<0){vector<int> negs;for(int x:nots)negs.push_back(-x);atmost(negs,s-abs(maxnot));}
  for(int i=0;i<s;i++){vector<int> use;for(int j=i+1;j<s;j++){use.push_back(as[j][n+i]);use.push_back(bs[j][n+i]);}for(int k=0;k<5;k++)use.push_back(outs[k][n+i]);sat.clause(use);}
  if(hint.empty())for(int i=0;i<s-1;i++)for(int a=0;a<n+i;a++)for(int b=0;b<a;b++)sat.clause(-bs[i][a],-bs[i+1][b]);
  if(first>=0){int op=first/2,a=0,b=first%2?1:3;if(first==4){op=2;b=0;}sat.clause(ops[0][op]);sat.clause(as[0][a]);sat.clause(bs[0][b]);}
  if(!hint.empty()){
   ifstream f(hint);int out,op,a,b;for(int i=0;i<s;i++){f>>out>>op>>a>>b;if(op==2)b=a;else if(a>b)swap(a,b);sat.clause(ops[i][op]);sat.clause(as[i][a]);sat.clause(bs[i][b]);}
   for(int k=0;k<5;k++){f>>out;sat.clause(outs[k][out]);}
  }
  for(int x=0;x<64;x++)instance(x);
 }
 void instance(int x){
  vector<int> val(n+s,0);
  for(int i=0;i<s;i++){
   int l=var(),r=var(),v=var();val[n+i]=v;
   for(int j=0;j<n+i;j++)for(int z=0;z<2;z++){
    int sel=z?bs[i][j]:as[i][j],zval=z?r:l;
    if(j<n)sat.clause(-sel,(x>>j&1)?zval:-zval);else{sat.clause(-sel,-zval,val[j]);sat.clause(-sel,zval,-val[j]);}
   }
   int a=ops[i][0],o=ops[i][1],neg=ops[i][2];
   sat.clause(-a,-l,-r,v);sat.clause(-a,l,-v);sat.clause(-a,r,-v);
   sat.clause(-o,l,r,-v);sat.clause(-o,-l,v);sat.clause(-o,-r,v);
   sat.clause(-neg,l,v);sat.clause(-neg,-l,-v);
  }
  auto t=target(x);
  for(int k=0;k<5;k++)for(int j=0;j<n+s;j++){
   if(j<n){if(t[k]!=bool(x>>j&1))sat.clause(-outs[k][j]);}
   else sat.clause(-outs[k][j],t[k]?val[j]:-val[j]);
  }
 }
 void run(int seconds){
  auto start=chrono::steady_clock::now();timer.until=start+chrono::seconds(seconds);
  cout<<"SOLVE n=6 outputs=5 gates="<<s<<" vars="<<vars<<endl;int result=sat.solve();
  cout<<"RESULT "<<result<<" elapsed="<<chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-start).count()<<endl;
  if(result!=10)return;
  vector<Gate> gs;vector<int> os;
  for(int i=0;i<s;i++){Gate g={-1,-1,-1};for(int j=0;j<3;j++)if(sat.val(ops[i][j])>0)g.op=j;for(int j=0;j<n+i;j++){if(sat.val(as[i][j])>0)g.a=j;if(sat.val(bs[i][j])>0)g.b=j;}gs.push_back(g);}
  for(int k=0;k<5;k++)for(int j=0;j<n+s;j++)if(sat.val(outs[k][j])>0)os.push_back(j);
  int bad=0;for(int x=0;x<64;x++){bool v[100];for(int i=0;i<n;i++)v[i]=x>>i&1;for(int i=0;i<s;i++){auto g=gs[i];v[n+i]=g.op==0?v[g.a]&&v[g.b]:g.op==1?v[g.a]||v[g.b]:!v[g.a];}auto t=target(x);for(int k=0;k<5;k++)bad+=v[os[k]]!=t[k];}
  cout<<"INDEPENDENT_CHECK_ERRORS "<<bad<<endl;
  for(int i=0;i<s;i++){auto g=gs[i];cout<<n+i<<" "<<g.op<<" "<<g.a<<" "<<g.b<<"\n";}cout<<"OUTPUTS";for(int o:os)cout<<" "<<o;cout<<endl;
 }
};
int main(int argc,char**argv){int s=argc>1?atoi(argv[1]):11;int first=argc>2?atoi(argv[2]):-1;int maxnot=argc>3?atoi(argv[3]):1;int seed=argc>4?atoi(argv[4]):1;int sec=argc>5?atoi(argv[5]):600;string hint=argc>6?argv[6]:"";VectorSynth(s,first,maxnot,seed,hint).run(sec);}
