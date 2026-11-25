#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <bit>
#include <unordered_map>
#include <cassert>
using namespace std;
constexpr int N=17,G=64,W=2;
struct Gate{int op,a,b;};
using Bits=array<uint64_t,W>;
struct Circuit{array<Gate,G> gates;int output;uint32_t missing;int cone;};
array<Bits,N> inputs;Bits target{};vector<pair<int,int>> edges;
vector<vector<Gate>> seeds;mt19937_64 rng;
unordered_map<uint32_t,pair<int,int>> covers;
int ri(int n){return rng()%n;}
pair<int,int> cover(uint32_t missing){
 auto it=covers.find(missing);if(it!=covers.end())return it->second;
 int best=100,choice=0;
 for(int s=0;s<64;s++){
  uint32_t lines=0;
  for(int e=0;e<(int)edges.size();e++)if((missing>>e&1)&&!(s>>edges[e].first&1))lines|=uint32_t(1)<<(edges[e].second-6);
  int count=popcount((unsigned)s)+popcount(lines);if(count<best){best=count;choice=s;}
 }
 return covers[missing]={popcount(missing)+best,choice};
}
int evaluate(Circuit& c){
 array<Bits,N+G> v;copy(inputs.begin(),inputs.end(),v.begin());array<uint64_t,N+G> cones{};
 int best=1000000,ties=0;
 for(int k=0;k<G;k++){
  auto g=c.gates[k];for(int w=0;w<W;w++)v[N+k][w]=g.op?(v[g.a][w]|v[g.b][w]):(v[g.a][w]&v[g.b][w]);
  cones[N+k]=cones[g.a]|cones[g.b]|(uint64_t(1)<<k);
  bool safe=true;for(int w=0;w<W;w++)safe &= (v[N+k][w]&~target[w])==0;
  uint32_t support=v[N+k][0]&target[0];if(!safe||!support)continue;
  uint32_t missing=uint32_t(target[0])^support;int size=popcount(cones[N+k]);int score=size+cover(missing).first;
  if(score<best){best=score;ties=0;}
  if(score==best&&ri(++ties)==0){c.output=N+k;c.missing=missing;c.cone=size;}
 }
 return best;
}
Circuit seed(){Circuit c;auto s=seeds[ri(seeds.size())];copy(s.begin(),s.end(),c.gates.begin());for(int k=s.size();k<G;k++)c.gates[k]={ri(2),ri(N+k),ri(N+k)};c.output=N+s.size()-1;return c;}
vector<Gate> complete(const Circuit& c){
 array<bool,N+G> used{};used[c.output]=true;
 for(int k=G-1;k>=0;k--)if(used[N+k])used[c.gates[k].a]=used[c.gates[k].b]=true;
 array<int,N+G> ren;for(int i=0;i<N;i++)ren[i]=i;
 vector<Gate> result;
 for(int k=0;k<G;k++)if(used[N+k]){auto g=c.gates[k];ren[N+k]=N+result.size();result.push_back({g.op,ren[g.a],ren[g.b]});}
 int output=ren[c.output],selected=cover(c.missing).second;
 array<vector<int>,N> neighbors;
 for(int e=0;e<(int)edges.size();e++)if(c.missing>>e&1){auto[a,b]=edges[e];if(selected>>a&1)neighbors[a].push_back(b);else neighbors[b].push_back(a);}
 auto add=[&](int op,int a,int b){result.push_back({op,a,b});return N+(int)result.size()-1;};
 for(int owner=0;owner<N;owner++)if(!neighbors[owner].empty()){
  int sum=neighbors[owner][0];for(int j=1;j<(int)neighbors[owner].size();j++)sum=add(1,sum,neighbors[owner][j]);
  int star=add(0,owner,sum);output=add(1,output,star);
 }
 assert(output==N+(int)result.size()-1);assert(result.size()==c.cone+cover(c.missing).first);
 return result;
}
void dump(const vector<Gate>& c,const string& path){ofstream f(path);f<<"[\n";for(int k=0;k<(int)c.size();k++){auto g=c[k];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<(int)c.size()?",":"")<<"\n";}f<<"]\n";}
int main(int argc,char**argv){
 if(argc!=6){cerr<<"usage: search_completion tests-edges.txt seeds.txt seconds seed prefix\n";return 2;}
 ifstream f(argv[1]);int m;f>>m;assert(m<=128);vector<uint32_t> test_inputs;
 for(int j=0;j<m;j++){uint32_t x;int y;f>>x>>y;test_inputs.push_back(x);for(int i=0;i<N;i++)if(x>>i&1)inputs[i][j/64]|=uint64_t(1)<<(j%64);if(y)target[j/64]|=uint64_t(1)<<(j%64);}
 int en;f>>en;for(int k=0;k<en;k++){int a,b;f>>a>>b;edges.push_back({a,b});}assert(en==24&&target[0]==0xffffff&&target[1]==0);
 for(int e=0;e<en;e++){auto[a,b]=edges[e];assert(a>=0&&a<6&&b>=6&&b<N);assert(test_inputs[e]==((uint32_t(1)<<a)|(uint32_t(1)<<b)));}
 ifstream s(argv[2]);int ns;s>>ns;while(ns--){int n;s>>n;assert(n>0&&n<=G);vector<Gate> gs(n);for(int j=0;j<n;j++){auto&g=gs[j];s>>g.op>>g.a>>g.b;assert((g.op==0||g.op==1)&&g.a>=0&&g.a<N+j&&g.b>=0&&g.b<N+j);}seeds.push_back(gs);}
 int duration=stoi(argv[3]);rng.seed(stoull(argv[4]));string prefix=argv[5];
 Circuit current=seed();int score=evaluate(current),best=1000000,report=-1;long long iterations=0,restarts=0;auto begin=chrono::steady_clock::now();
 while(true){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();if(elapsed>=duration)break;
  if((int)elapsed/10>report){report=elapsed/10;cout<<"seconds "<<elapsed<<" iterations "<<iterations<<" restarts "<<restarts<<" best "<<best<<" current "<<score<<" cone "<<current.cone<<" missing "<<popcount(current.missing)<<" cover_cache "<<covers.size()<<endl;}
  Circuit next=current;int mutations=1+(ri(4)==0)+(ri(12)==0);
  for(int k=0;k<mutations;k++){int j=ri(G),mode=ri(12);if(mode<5)next.gates[j].a=ri(N+j);else if(mode<10)next.gates[j].b=ri(N+j);else next.gates[j].op^=1;}
  int nextscore=evaluate(next);
  if(nextscore<best){best=nextscore;dump(complete(next),prefix+"-best.json");cout<<"BEST "<<best<<" cone "<<next.cone<<" missing "<<popcount(next.missing)<<" at "<<elapsed<<endl;}
  if(nextscore<=28){dump(complete(next),prefix+"-solution.json");cout<<"SOLUTION "<<prefix<<"-solution.json"<<endl;return 0;}
  double temp=((iterations/100000)%3==0)?0.1:(((iterations/100000)%3==1)?0.7:2.0);
  if(nextscore<=score||uniform_real_distribution<double>(0,1)(rng)<exp((score-nextscore)/temp)){current=next;score=nextscore;}
  iterations++;
  if(iterations%2000000==0){current=seed();score=evaluate(current);restarts++;}
 }
 cout<<"DONE iterations "<<iterations<<" best "<<best<<endl;
}
