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
using namespace std;
constexpr int N=26,G=63,W=12;
struct Gate {int op,a,b;};
using Circuit=array<Gate,G>;
using Bits=array<uint64_t,W>;
array<Bits,N> inputs;
Bits wanted{};
vector<pair<int,int>> edges;
vector<vector<Gate>> alternate_seeds;
mt19937_64 rng;
int ri(int n){return rng()%n;}
pair<int,int> errors(const Circuit& c){
 array<Bits,N+G> v;
 copy(inputs.begin(),inputs.end(),v.begin());
 for(int k=0;k<G;k++){
  auto g=c[k];
  for(int j=0;j<W;j++)v[N+k][j]=g.op?(v[g.a][j]|v[g.b][j]):(v[g.a][j]&v[g.b][j]);
 }
 int miss=0,wrong=0;
 for(int j=0;j<W;j++){
  miss+=popcount(wanted[j]&~v[N+G-1][j]);
  wrong+=popcount(~wanted[j]&v[N+G-1][j]);
 }
 return {miss,wrong};
}
Circuit seed(){
 vector<Gate> c;
 auto add=[&](int op,int a,int b){c.push_back({op,a,b});return N+(int)c.size()-1;};
 auto disj=[&](vector<int> vals){
  while(vals.size()>1){int i=ri(vals.size());int a=vals[i];vals.erase(vals.begin()+i);int j=ri(vals.size());int b=vals[j];vals.erase(vals.begin()+j);vals.push_back(add(1,a,b));}
  return vals[0];
 };
 vector<int> row(13),out;
 for(int p=0;p<13;p++)row[p]=p;
 shuffle(row.begin(),row.end(),rng);
 bool dual=ri(2);
 for(int p:row){
  vector<int> ns;
  for(auto [a,b]:edges)if((dual?b-13:a)==p)ns.push_back(dual?a:b);
  int s=disj(ns);out.push_back(add(0,dual?p+13:p,s));
 }
 disj(out);
 if(!alternate_seeds.empty())c=alternate_seeds[ri(alternate_seeds.size())];
 while(c.size()>G){
  vector<int> choices;
  for(int k=0;k<(int)c.size();k++)if(c[k].op==1&&k<52)choices.push_back(k);
  int del=choices[ri(choices.size())];int replacement=ri(2)?c[del].a:c[del].b;
  for(auto& g:c){for(int* p:{&g.a,&g.b}){if(*p==N+del)*p=replacement;else if(*p>N+del)--*p;}}
  c.erase(c.begin()+del);
 }
 Circuit result;copy(c.begin(),c.end(),result.begin());return result;
}
void dump(const Circuit& c,const string& path){
 ofstream f(path);f<<"[\n";
 for(int k=0;k<G;k++){auto g=c[k];f<<"  ["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<G?",":"")<<"\n";}f<<"]\n";
}
int main(int argc,char**argv){
 if(argc!=5&&argc!=6){cerr<<"usage: search tests.txt seconds seed output-prefix [alternate-seeds.txt]\n";return 2;}
 ifstream f(argv[1]);int m;f>>m;
 for(int j=0;j<m;j++){uint32_t x;int y;f>>x>>y;for(int i=0;i<N;i++)if((x>>i)&1)inputs[i][j/64]|=uint64_t(1)<<(j%64);if(y)wanted[j/64]|=uint64_t(1)<<(j%64);}
 int en;f>>en;for(int k=0;k<en;k++){int a,b;f>>a>>b;edges.push_back({a,b});}
 if(argc==6){ifstream s(argv[5]);int n;s>>n;while(n--){int k;s>>k;vector<Gate> c(k);for(auto& g:c)s>>g.op>>g.a>>g.b;alternate_seeds.push_back(c);}}
 int duration=stoi(argv[2]);rng.seed(stoull(argv[3]));string prefix=argv[4];
 auto begin=chrono::steady_clock::now();long long it=0,restarts=0;int best=100000,lastreport=-1;
 Circuit current=seed();auto [miss,wrong]=errors(current);int score=miss*16+wrong;
 Circuit global=current;
 while(true){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();if(elapsed>duration)break;
  if((int)elapsed/10>lastreport){lastreport=(int)elapsed/10;cout<<"seconds "<<elapsed<<" iterations "<<it<<" restarts "<<restarts<<" best "<<best<<" current "<<score<<" miss "<<miss<<" false "<<wrong<<endl;}
  Circuit next=current;int mutations=1+(ri(8)==0)+(ri(20)==0);
  for(int k=0;k<mutations;k++){int j=ri(G);int mode=ri(12);if(mode<5)next[j].a=ri(N+j);else if(mode<10)next[j].b=ri(N+j);else next[j].op^=1;}
  auto [nm,nw]=errors(next);int ns=nm*16+nw;
  if(ns<best){best=ns;global=next;dump(global,prefix+"-best.json");cout<<"BEST "<<best<<" miss "<<nm<<" false "<<nw<<" at "<<elapsed<<endl;}
  if(ns==0){dump(next,prefix+"-solution.json");cout<<"SOLUTION "<<prefix<<"-solution.json"<<endl;return 0;}
  // Alternating greedy and mild annealing phases allow equivalence plateaus.
  double temp=((it/200000)%3==0)?0.0:(((it/200000)%3==1)?0.4:1.2);
  if(ns<=score || (temp>0 && uniform_real_distribution<double>(0,1)(rng)<exp((score-ns)/temp))){current=next;score=ns;miss=nm;wrong=nw;}
  ++it;
  if(it%1000000==0){current=seed();auto er=errors(current);miss=er.first;wrong=er.second;score=miss*16+wrong;restarts++;}
 }
 cout<<"DONE iterations "<<it<<" best "<<best<<endl;
}
