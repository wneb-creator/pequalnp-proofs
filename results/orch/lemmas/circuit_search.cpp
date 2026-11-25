#include <array>
#include <algorithm>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <random>
#include <string>
#include <vector>
using namespace std;
using TT = array<unsigned long long,16>;
struct G { int op,a,b; };
using C = vector<G>;
const vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
array<TT,10> inputs;
TT goal,neg;
mt19937_64 rng;
int rnd(int n){ return rng()%n; }
int eval(const C &c, int *plain=nullptr) {
 array<TT,32> w;
 copy(inputs.begin(),inputs.end(),w.begin());
 for(int j=0;j<(int)c.size();j++) {
  const auto &g=c[j];
  for(int k=0;k<16;k++) w[10+j][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 int score=0,errors=0;
 for(int k=0;k<16;k++){auto d=w[9+c.size()][k]^goal[k]; errors+=popcount(d);score+=popcount(d)+7*popcount(d&neg[k]);}
 if(plain)*plain=errors;
 return score;
}
void dump(const C &c,const string &path,int score) {
 ofstream out(path);
 out<<"{\"score\":"<<score<<",\"gates\":[";
 for(int j=0;j<(int)c.size();j++){if(j)out<<",";out<<"["<<c[j].op<<","<<c[j].a<<","<<c[j].b<<"]";}
 out<<"]}\n";
}
C seed20() {
 vector<int> independent;
 for(int s=0;s<1024;s++)if(popcount((unsigned)s)==4){bool ok=true;for(auto [a,b]:edges)if((s>>a&1)&&(s>>b&1))ok=false;if(ok)independent.push_back(s);}
 int ind=independent[rnd(independent.size())];
 vector<int> cover;for(int i=0;i<10;i++)if(!(ind>>i&1))cover.push_back(i);
 shuffle(cover.begin(),cover.end(),rng);
 array<vector<int>,10> stars;
 for(auto [a,b]:edges){if(ind>>a&1)swap(a,b);else if(!(ind>>b&1)&&rnd(2))swap(a,b);stars[a].push_back(b);}
 C c;vector<int> tops;
 for(int i:cover){auto &vs=stars[i]; if(vs.empty())continue;shuffle(vs.begin(),vs.end(),rng);int v=vs[0];for(int k=1;k<(int)vs.size();k++){c.push_back({1,v,vs[k]});v=9+c.size();}c.push_back({0,i,v});tops.push_back(9+c.size());}
 shuffle(tops.begin(),tops.end(),rng);int v=tops[0];for(int k=1;k<(int)tops.size();k++){c.push_back({1,v,tops[k]});v=9+c.size();}
 return c;
}
C shrink(C c) {
 while(c.size()>19){int j=rnd(c.size()-1);int sub=rnd(2)?c[j].a:c[j].b;for(int k=j+1;k<(int)c.size();k++){for(int *v:{&c[k].a,&c[k].b}){if(*v==10+j)*v=sub;else if(*v>10+j)--*v;}}c.erase(c.begin()+j);}
 while(c.size()<19){int old=9+c.size();c.push_back({1,old,old});}
 return c;
}
int main(int argc,char **argv) {
 int seconds=argc>1?atoi(argv[1]):1200;unsigned long long sd=argc>2?strtoull(argv[2],nullptr,10):1;rng.seed(sd);
 string prefix=argc>3?argv[3]:"/tmp/oec/pequalnp-pilot-120/circuit_search";
 for(int s=0;s<1024;s++){for(int i=0;i<10;i++)if(s>>i&1)inputs[i][s/64]|=1ULL<<(s%64);bool f=false;for(auto[a,b]:edges)f|=(s>>a&1)&&(s>>b&1);(f?goal:neg)[s/64]|=1ULL<<(s%64);}
 auto start=chrono::steady_clock::now();long long evals=0;int best=10000;C bestc;int round=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  C c=shrink(seed20());if(round%5==0&&!bestc.empty())c=bestc;
  int val=eval(c),stale=0;
  for(int it=0;it<120000;it++){
   C d=c;int nm=rnd(100);int n=nm<88?1:nm<98?2:3;
   for(int z=0;z<n;z++){int j=rnd(19),kind=rnd(5);if(kind==0)d[j].op=rnd(3);else if(kind<3)d[j].a=rnd(10+j);else d[j].b=rnd(10+j);}
   int q=eval(d);evals++;
   double temp=(it%20000<19000)?0.15:1.25;
   bool take=q<=val||(q-val<20&&generate_canonical<double,32>(rng)<exp((val-q)/temp));
   if(take){c=move(d);val=q;}
   if(val<best){best=val;bestc=c;int plain;eval(c,&plain);dump(c,prefix+"_best.json",best);printf("best=%d errors=%d evaluations=%lld round=%d elapsed=%.1f\n",best,plain,evals,round,chrono::duration<double>(chrono::steady_clock::now()-start).count());fflush(stdout);stale=0;}
   else stale++;
   if(best==0){printf("FOUND\n");return 0;}
   if(stale>30000)break;
  }
  round++;
  if(round%50==0){printf("progress round=%d best=%d evaluations=%lld elapsed=%.1f\n",round,best,evals,chrono::duration<double>(chrono::steady_clock::now()-start).count());fflush(stdout);}
 }
 printf("DONE best=%d evaluations=%lld rounds=%d\n",best,evals,round);
}
