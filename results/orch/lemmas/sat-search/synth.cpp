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
struct Timer : CaDiCaL::Terminator {
  chrono::steady_clock::time_point until;
  bool terminate() override { return chrono::steady_clock::now() > until; }
};
struct Gate { int op,a,b; };
struct Synth {
 int n=10,s=19,vars=0,first=-1,maxnot=1;
 CaDiCaL::Solver sat; Timer timer;
 vector<array<int,3>> ops;
 vector<vector<int>> as,bs;
 vector<int> used;
 vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
 int var(){return ++vars;}
 void clause(vector<int> v){sat.clause(v);}
 void one(const vector<int>& v){clause(v); for(size_t i=0;i<v.size();i++)for(size_t j=i+1;j<v.size();j++)sat.clause(-v[i],-v[j]);}
 void atmost(const vector<int>& lits,int budget){
  int m=lits.size();if(budget>=m)return;if(budget==0){for(int x:lits)sat.clause(-x);return;}
  vector<vector<int>> count(m+1,vector<int>(budget+2,0));
  for(int i=1;i<=m;i++)for(int j=1;j<=min(i,budget+1);j++){
   count[i][j]=var();if(j==1)sat.clause(-lits[i-1],count[i][j]);
   if(count[i-1][j])sat.clause(-count[i-1][j],count[i][j]);
   if(j>1&&count[i-1][j-1])sat.clause(-lits[i-1],-count[i-1][j-1],count[i][j]);
  }
  sat.clause(-count[m][budget+1]);
 }
 bool target(int x){for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1))return true;return false;}
 Synth(int gates,int firstgate,int maxn,int seed,string hint="",int budget=3):s(gates),first(firstgate),maxnot(abs(maxn)){
  sat.set("quiet",1);sat.set("seed",seed);sat.connect_terminator(&timer);
  ops.resize(s);as.resize(s);bs.resize(s);used.assign(1<<n,0);
  for(int i=0;i<s;i++){
   for(int j=0;j<3;j++){ops[i][j]=var();sat.freeze(ops[i][j]);}
   one({ops[i][0],ops[i][1],ops[i][2]});
   for(int j=0;j<n+i;j++){as[i].push_back(var());bs[i].push_back(var());sat.freeze(as[i][j]);sat.freeze(bs[i][j]);}
   one(as[i]);one(bs[i]);
   for(int a=0;a<n+i;a++)for(int b=0;b<n+i;b++){
    if(a>b)sat.clause(-as[i][a],-bs[i][b]);
    if(a==b)sat.clause(-as[i][a],-bs[i][b],ops[i][2]);
    else sat.clause(-ops[i][2],-as[i][a],-bs[i][b]);
   }
  }
  vector<int> nots;for(auto op:ops)nots.push_back(op[2]);if(maxnot!=0)clause(nots);
  if(maxnot==1)for(int i=0;i<s;i++)for(int j=i+1;j<s;j++)sat.clause(-ops[i][2],-ops[j][2]);
  if(maxnot!=1)atmost(nots,maxnot);
  if(maxn<0){vector<int> negated;for(int v:nots)negated.push_back(-v);atmost(negated,s-maxnot);}
  for(int i=0;i<s-1;i++){
   vector<int> uses;
   for(int j=i+1;j<s;j++){uses.push_back(as[j][n+i]);uses.push_back(bs[j][n+i]);}
   clause(uses);
  }
  // A topological order chosen by the smallest greatest predecessor index exists.
  if(hint.empty())for(int i=0;i<s-1;i++)for(int a=0;a<n+i;a++)for(int b=0;b<a;b++)sat.clause(-bs[i][a],-bs[i+1][b]);
  if(!hint.empty()){
   ifstream f(hint);vector<int> changed;int output,op,a,b;
   for(int i=0;i<s;i++){f>>output>>op>>a>>b;if(op==2)b=a;else if(a>b)swap(a,b);
    int chg=var();changed.push_back(chg);sat.clause(chg,ops[i][op]);sat.clause(chg,as[i][a]);sat.clause(chg,bs[i][b]);
    sat.phase(ops[i][op]);sat.phase(as[i][a]);sat.phase(bs[i][b]);
   }
   vector<vector<int>> count(s+1,vector<int>(budget+2,0));
   for(int i=1;i<=s;i++){for(int j=1;j<=min(i,budget+1);j++){
    count[i][j]=var();if(j==1)sat.clause(-changed[i-1],count[i][j]);
    if(count[i-1][j])sat.clause(-count[i-1][j],count[i][j]);
    if(j>1&&count[i-1][j-1])sat.clause(-changed[i-1],-count[i-1][j-1],count[i][j]);
   }}
   sat.clause(-count[s][budget+1]);
  }
  if(first>=0){
    int op=first/2;int a=0,b=first%2?2:1;
    if(first==4){op=2;b=0;}
    sat.clause(ops[0][op]);sat.clause(as[0][a]);sat.clause(bs[0][b]);
  }
 }
 void instance(int x){
  if(used[x])return;used[x]=1;
  vector<int> val(n+s,0);
  for(int i=0;i<s;i++){
   int l=var(),r=var(),v=var();val[n+i]=v;
   for(int j=0;j<n+i;j++){
    for(int z=0;z<2;z++){
      int sel=z?bs[i][j]:as[i][j],zval=z?r:l;
      if(j<n)sat.clause(-sel, (x>>j&1)?zval:-zval);
      else {sat.clause(-sel,-zval,val[j]);sat.clause(-sel,zval,-val[j]);}
    }
   }
   int a=ops[i][0],o=ops[i][1],neg=ops[i][2];
   sat.clause(-a,-l,-r,v);sat.clause(-a,l,-v);sat.clause(-a,r,-v);
   sat.clause(-o,l,r,-v);sat.clause(-o,-l,v);sat.clause(-o,-r,v);
   sat.clause(-neg,l,v);sat.clause(-neg,-l,-v);
  }
  sat.clause(target(x)?val.back():-val.back());
 }
 vector<Gate> model(){
  vector<Gate> g;
  for(int i=0;i<s;i++){
   Gate h={-1,-1,-1};
   for(int j=0;j<3;j++)if(sat.val(ops[i][j])>0)h.op=j;
   for(int j=0;j<n+i;j++){if(sat.val(as[i][j])>0)h.a=j;if(sat.val(bs[i][j])>0)h.b=j;}
   g.push_back(h);
  }
  return g;
 }
 bool eval(const vector<Gate>& gs,int x){
  bool v[100];for(int i=0;i<n;i++)v[i]=x>>i&1;
  for(int i=0;i<s;i++){auto g=gs[i];v[n+i]=g.op==0?v[g.a]&&v[g.b]:g.op==1?v[g.a]||v[g.b]:!v[g.a];}
  return v[n+s-1];
 }
 void print(const vector<Gate>& gs){for(int i=0;i<s;i++){auto g=gs[i];cout<<n+i<<" "<<(g.op==0?"AND":g.op==1?"OR":"NOT")<<" "<<g.a<<" "<<g.b<<"\n";}cout.flush();}
 void run(int seconds){
  auto start=chrono::steady_clock::now();
  for(int x=0;x<(1<<n);x++){
   bool maximal=!target(x);
   if(maximal)for(int i=0;i<n;i++)if(!(x>>i&1)&&!target(x|1<<i))maximal=false;
   if(__builtin_popcount((unsigned)x)<=2||maximal||x==1023)instance(x);
  }
  for(int round=0;;round++){
   int elapsed=chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-start).count();
   if(elapsed>=seconds){cout<<"TIME LIMIT "<<elapsed<<"\n";return;}
   timer.until=start+chrono::seconds(seconds);
   cout<<"SOLVE round="<<round<<" tests="<<accumulate(used.begin(),used.end(),0)<<" vars="<<vars<<" elapsed="<<elapsed<<endl;
   int result=sat.solve();
   cout<<"RESULT "<<result<<" elapsed="<<chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-start).count()<<endl;
   if(result!=10)return;
   auto gs=model();vector<int> bad;
   for(int x=0;x<(1<<n);x++)if(eval(gs,x)!=target(x))bad.push_back(x);
   cout<<"COUNTEREXAMPLES "<<bad.size()<<endl;
   if(bad.empty()){cout<<"WITNESS\n";print(gs);return;}
   stable_sort(bad.begin(),bad.end(),[](int a,int b){return __builtin_popcount((unsigned)a)<__builtin_popcount((unsigned)b);});
   for(int i=0;i<min((int)bad.size(),16);i++)instance(bad[i]);
  }
 }
};
int main(int argc,char**argv){int s=argc>1?atoi(argv[1]):19;int first=argc>2?atoi(argv[2]):-1;int maxn=argc>3?atoi(argv[3]):1;int seed=argc>4?atoi(argv[4]):1;int seconds=argc>5?atoi(argv[5]):1200;string hint=argc>6?argv[6]:"";int budget=argc>7?atoi(argv[7]):3;Synth(s,first,maxn,seed,hint,budget).run(seconds);}
