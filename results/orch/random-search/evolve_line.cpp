#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using U=uint64_t;
constexpr int n=15,m=38,nw=2;
struct Gate{int a,b,op;};
struct Circuit{std::array<Gate,m> g;int score;};
struct Bits{std::array<U,nw>b{};};
std::array<Bits,n> inputs;Bits target;std::vector<std::pair<int,int>>edges;std::vector<unsigned>covers;
std::mt19937_64 rng;
int score(Circuit &c){
 std::array<Bits,n+m>v;
 for(int i=0;i<n;i++)v[i]=inputs[i];
 for(int j=0;j<m;j++){
  auto g=c.g[j];
  for(int w=0;w<nw;w++)v[n+j].b[w]=g.op?(v[g.a].b[w]|v[g.b].b[w]):(v[g.a].b[w]&v[g.b].b[w]);
 }
 int s=0;
 for(int w=0;w<nw;w++)s+=std::popcount(v[n+m-1].b[w]^target.b[w]);
 c.score=s;return s;
}
void print(const Circuit&c,std::ostream&out){
 out<<"score "<<c.score<<" output "<<(n+m-1)<<"\n";
 for(int j=0;j<m;j++)out<<(n+j)<<" "<<(c.g[j].op?"or":"and")<<" "<<c.g[j].a<<" "<<c.g[j].b<<"\n";
 out.flush();
}
std::vector<Gate> optimum(){
 unsigned cover=covers[rng()%covers.size()];
 std::array<std::vector<int>,n>stars;
 for(auto[a,b]:edges){
  if(!(cover>>a&1))std::swap(a,b);
  else if((cover>>b&1)&&(rng()%2))std::swap(a,b);
  stars[a].push_back(b);
 }
 std::vector<int>ord;for(int i=0;i<n;i++)if(!stars[i].empty())ord.push_back(i);
 std::shuffle(ord.begin(),ord.end(),rng);std::vector<Gate>g;std::vector<int>terms;
 for(int a:ord){
  auto &vs=stars[a];std::shuffle(vs.begin(),vs.end(),rng);int q=vs[0];
  for(int k=1;k<(int)vs.size();k++){g.push_back({q,vs[k],1});q=n+g.size()-1;}
  g.push_back({a,q,0});terms.push_back(n+g.size()-1);
 }
 while(terms.size()>1){
  int a=rng()%terms.size();int q=terms[a];terms.erase(terms.begin()+a);
  int b=rng()%terms.size();int r=terms[b];terms.erase(terms.begin()+b);
  g.push_back({q,r,1});terms.push_back(n+g.size()-1);
 }
 if(g.size()!=m+1){std::cerr<<"bad optimum size "<<g.size()<<std::endl;exit(2);}
 return g;
}
Circuit seed(){
 auto g=optimum();Circuit best;best.score=100000;
 for(int kill=0;kill<m+1;kill++)for(int side=0;side<2;side++){
  if(kill==m)continue;
  int rep=side?g[kill].a:g[kill].b;Circuit c;int j=0;
  for(int k=0;k<m+1;k++)if(k!=kill){
   auto a=g[k];
   if(a.a==n+kill)a.a=rep;if(a.b==n+kill)a.b=rep;
   if(a.a>n+kill)a.a--;if(a.b>n+kill)a.b--;
   c.g[j++]=a;
  }
  score(c);if(c.score<best.score)best=c;
 }
 return best;
}
void mutate(Circuit&c,int mode){
 int cnt=1+(rng()%100<15)+(rng()%100<3);
 for(int z=0;z<cnt;z++){
  int j=rng()%m;int x=rng()%3;
  if(x==0)c.g[j].op^=1;
  else if(x==1)c.g[j].a=rng()%(n+j);
  else c.g[j].b=rng()%(n+j);
 }
 if(mode && rng()%40==0){
  int a=rng()%m,b=rng()%m;if(a>b)std::swap(a,b);
  if(a<b && c.g[b].a<n+a && c.g[b].b<n+a)std::swap(c.g[a],c.g[b]);
 }
}
int main(int argc,char**argv){
 long long rounds=argc>1?atoll(argv[1]):100000000;
 int rndseed=argc>2?atoi(argv[2]):2028;rng.seed(rndseed);
 std::vector<std::pair<int,int>>base;
 for(int i=0;i<5;i++){base.push_back({i,(i+1)%5});base.push_back({i,5+i});base.push_back({5+i,5+(i+2)%5});}
 std::array<unsigned,n>adj{};
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){
  auto[x,y]=base[a];auto[z,w]=base[b];
  if(x==z||x==w||y==z||y==w){edges.push_back({a,b});adj[a]|=1u<<b;adj[b]|=1u<<a;}
 }
 std::vector<unsigned>samples;
 for(auto[a,b]:edges)samples.push_back((1u<<a)|(1u<<b));
 for(unsigned s=0;s<(1u<<n);s++){
  unsigned covered=s;bool independent=true;
  for(int i=0;i<n;i++)if(s>>i&1){if(adj[i]&s)independent=false;covered|=adj[i];}
  if(independent && covered==(1u<<n)-1)samples.push_back(s);
 }
 std::cout<<"compressed constraints "<<samples.size()<<std::endl;
 if(samples.size()>nw*64){std::cerr<<"signature too large"<<std::endl;return 2;}
 for(int j=0;j<(int)samples.size();j++){
  for(int i=0;i<n;i++)if(samples[j]>>i&1)inputs[i].b[j>>6]|=U(1)<<(j&63);
  if(j<(int)edges.size())target.b[j>>6]|=U(1)<<(j&63);
 }
 int tau=n;
 for(unsigned s=0;s<(1u<<n);s++){
  bool ok=true;for(auto[a,b]:edges)if(!(s>>a&1)&&!(s>>b&1))ok=false;
  if(ok){int t=std::popcount(s);if(t<tau){tau=t;covers.clear();}if(t==tau)covers.push_back(s);}
 }
 std::cout<<"Line Petersen tau "<<tau<<" minimum covers "<<covers.size()<<" seed "<<rndseed<<" rounds "<<rounds<<std::endl;
 const int pop=32;std::array<Circuit,pop>pool;
 for(auto &c:pool)c=seed();Circuit best=pool[0];
 for(auto &c:pool)if(c.score<best.score)best=c;
 std::cout<<"initial best "<<best.score<<std::endl;print(best,std::cout);
 auto start=std::chrono::steady_clock::now();
 for(long long trial=0;trial<rounds;trial++){
  int k=rng()%pop;Circuit cand=pool[k];mutate(cand,1);score(cand);
  // neutral drift plus occasional annealing; reset individual after a fixed epoch.
  double T=(trial%2000000<200000)?1.0:0.10;
  if(cand.score<=pool[k].score || (rng()%1000000)<1000000*std::exp((pool[k].score-cand.score)/T))pool[k]=cand;
  if(cand.score<best.score){best=cand;std::cout<<"BEST "<<best.score<<" trial "<<trial<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;print(best,std::cout);}
  if(best.score==0){
   int errors=0;
   for(unsigned x=0;x<(1u<<n);x++){
    std::array<bool,n+m>v;for(int i=0;i<n;i++)v[i]=x>>i&1;
    for(int j=0;j<m;j++){auto g=best.g[j];v[n+j]=g.op?(v[g.a]||v[g.b]):(v[g.a]&&v[g.b]);}
    bool want=false;for(auto[a,b]:edges)want|=v[a]&&v[b];errors+=want!=v[n+m-1];
   }
   std::cout<<"COUNTEREXAMPLE full truth table errors "<<errors<<std::endl;return errors?2:0;
  }
  if(trial && trial%1000000==0){
   std::cout<<"progress "<<trial<<" best "<<best.score<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
   for(int z=0;z<4;z++)pool[rng()%pop]=seed();pool[0]=best;
  }
 }
 std::cout<<"DONE best "<<best.score<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;print(best,std::cout);
}
