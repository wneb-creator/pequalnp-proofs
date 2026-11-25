#include <array>
#include <algorithm>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
using TT = array<uint64_t,16>;
struct Gate { int op,a,b; };
struct Candidate { array<Gate,19> g; int score,errors; };
const array<pair<int,int>,15> edges = {{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
array<TT,10> input;
TT target,negative;
mt19937 rng(73837);
int rr(int n){return int(rng()%n);}
double ur(){return double(rng())/double(rng.max());}
void assess(Candidate &c,int negWeight=2){
 array<TT,29> w;
 for(int i=0;i<10;i++)w[i]=input[i];
 int nnot=0;
 for(int k=0;k<19;k++){
  auto g=c.g[k]; nnot+=g.op==2;
  for(int q=0;q<16;q++) w[k+10][q]=g.op==0?(w[g.a][q]&w[g.b][q]):g.op==1?(w[g.a][q]|w[g.b][q]):~w[g.a][q];
 }
 c.score=0;c.errors=0;
 for(int q=0;q<16;q++){
  auto e=w[28][q]^target[q];
  c.errors+=popcount(e);
  c.score+=popcount(e&target[q])+negWeight*popcount(e&negative[q]);
 }
 if(!nnot)c.score+=1000;
}
void save(const Candidate &c,const string &file){
 ofstream out(file);
 out<<"score "<<c.score<<" errors "<<c.errors<<"\n";
 for(int i=0;i<19;i++)out<<10+i<<" "<<c.g[i].op<<" "<<c.g[i].a<<" "<<c.g[i].b<<"\n";
}
vector<Gate> seed(){
 vector<int> covers;
 for(int m=0;m<1024;m++) if(popcount((unsigned)m)==6){
  bool ok=true;for(auto [a,b]:edges)if(!(m>>a&1)&&!(m>>b&1))ok=false;
  if(ok)covers.push_back(m);
 }
 int mask=covers[rr(covers.size())];
 array<vector<int>,10> stars;
 for(auto [a,b]:edges){
  if(!(mask>>a&1))swap(a,b);
  else if((mask>>b&1)&&rr(2))swap(a,b);
  stars[a].push_back(b);
 }
 vector<Gate> g;
 vector<int> terms;
 for(int a=0;a<10;a++)if(!stars[a].empty()){
  shuffle(stars[a].begin(),stars[a].end(),rng);
  int w=stars[a][0];
  for(int j=1;j<int(stars[a].size());j++){
   g.push_back({1,w,stars[a][j]});w=9+g.size();
  }
  g.push_back({0,a,w});terms.push_back(9+g.size());
 }
 shuffle(terms.begin(),terms.end(),rng);
 int w=terms[0];
 for(int j=1;j<int(terms.size());j++){
  g.push_back({1,w,terms[j]});w=9+g.size();
 }
 return g;
}
Candidate start(){
 auto g=seed();
 while(g.size()>19){
  int k=rr(g.size()-1),replacement=rr(2)?g[k].a:g[k].b;
  g.erase(g.begin()+k);
  for(auto &h:g) for(int *p:{&h.a,&h.b}){
   if(*p==10+k)*p=replacement;
   if(*p>10+k)(*p)--;
  }
 }
 Candidate c;
 for(int i=0;i<19;i++)c.g[i]=g[i];
 // A negation is initially placed at a low-impact location; all positions remain mutable.
 c.g[rr(18)].op=2;
 assess(c);return c;
}
int main(int argc,char **argv){
 int seconds=argc>1?atoi(argv[1]):1800;
 string dest=argc>2?argv[2]:"counterexample-best.txt";
 for(int x=0;x<1024;x++){
  for(int j=0;j<10;j++)if(x>>j&1)input[j][x/64]|=uint64_t(1)<<(x%64);
  bool f=false;for(auto [a,b]:edges)f|=(x>>a&1)&&(x>>b&1);
  if(f)target[x/64]|=uint64_t(1)<<(x%64);
 }
 for(int q=0;q<16;q++)negative[q]=~target[q];
 Candidate best=start();save(best,dest);
 auto begin=chrono::steady_clock::now();
 long long total=0;int restarts=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-begin).count()<seconds){
  Candidate c=(restarts%3==0||best.errors>50)?start():best;
  int negWeight=1+rr(8);assess(c,negWeight);
  const int rounds=50000;
  for(int step=0;step<rounds;step++,total++){
   Candidate d=c;
   int mutations=1+(rr(100)<8?1+rr(3):0);
   for(int j=0;j<mutations;j++){
    int k=rr(19),type=rr(100);
    if(type<10)d.g[k].op=rr(3);
    else if(type<55)d.g[k].a=rr(k+10);
    else d.g[k].b=rr(k+10);
   }
   assess(d,negWeight);
   double temp=0.25+4.0*(1.0-double(step)/rounds);
   if(d.score<=c.score||ur()<exp(double(c.score-d.score)/temp))c=d;
   bool hasNot=any_of(d.g.begin(),d.g.end(),[](Gate g){return g.op==2;});
   if(hasNot&&d.errors<best.errors){
    best=d;save(best,dest);
    cout<<"best errors="<<best.errors<<" score="<<best.score<<" trials="<<total<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;
   }
   if(hasNot&&d.errors==0){save(d,dest+".EXACT");return 0;}
  }
  restarts++;
  if(restarts%100==0)cout<<"progress restarts="<<restarts<<" trials="<<total<<" best="<<best.errors<<endl;
 }
 cout<<"finished trials="<<total<<" best="<<best.errors<<endl;
}
