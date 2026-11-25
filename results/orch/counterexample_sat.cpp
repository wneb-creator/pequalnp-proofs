#include <cadical.hpp>
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <vector>

struct Timer : CaDiCaL::Terminator {
  std::chrono::steady_clock::time_point end;
  bool terminate() override { return std::chrono::steady_clock::now()>=end; }
};
struct Gate { int op,a,b; };
const std::array<std::pair<int,int>,15> edges={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
bool target(int x) {for(auto [a,b]:edges)if((x&(1<<a))&&(x&(1<<b)))return true;return false;}

struct Synthesis {
 CaDiCaL::Solver sat;
 int next=0,n;
 std::vector<std::array<int,3>> op;
 std::vector<std::vector<int>> left,right;
 std::set<int> samples;
 int variable(){return ++next;}
 void clause(std::initializer_list<int> c){for(int l:c)sat.add(l);sat.add(0);}
 void clause(const std::vector<int>&c){for(int l:c)sat.add(l);sat.add(0);}
 void onehot(const std::vector<int>&v){clause(v);for(size_t i=0;i<v.size();i++)for(size_t j=0;j<i;j++)clause({-v[i],-v[j]});}
 Synthesis(int ng,int notMode,int seed):n(ng),op(n),left(n),right(n) {
  sat.set("quiet",1);sat.set("seed",seed);
  for(int i=0;i<n;i++) {
   for(int &v:op[i])v=variable();onehot({op[i][0],op[i][1],op[i][2]});
   for(int j=0;j<10+i;j++){left[i].push_back(variable());right[i].push_back(variable());}
   onehot(left[i]);onehot(right[i]);
   clause({-op[i][2],right[i][0]});
   for(int a=0;a<10+i;a++)for(int b=0;b<a;b++)clause({op[i][2],-left[i][a],-right[i][b]});
  }
  std::vector<int> nots;
  for(int i=0;i<n;i++)nots.push_back(op[i][2]);
  if(notMode==0)for(int v:nots)clause({-v});
  else if(notMode==1)onehot(nots);
  else {
   clause(nots);
   for(int a=0;a<n;a++)for(int b=0;b<a;b++)for(int c=0;c<b;c++)for(int d=0;d<c;d++)for(int e=0;e<d;e++)
    clause({-nots[a],-nots[b],-nots[c],-nots[d],-nots[e]});
  }
  if(std::getenv("PNP_ORDERED")) {
   std::vector<std::vector<int>> high(n);
   for(int i=0;i<n;i++)for(int j=0;j<10+i;j++) {
    int h=variable();high[i].push_back(h);
    clause({-op[i][2],-left[i][j],h});clause({-op[i][2],left[i][j],-h});
    clause({op[i][2],-right[i][j],h});clause({op[i][2],right[i][j],-h});
   }
   for(int i=1;i<n;i++)for(int k=0;k<10+i-1;k++)for(int j=0;j<k;j++)
    clause({-high[i-1][k],-high[i][j]});
  }
 }
 void sample(int input) {
  if(!samples.insert(input).second)return;
  std::vector<int> value;
  for(int i=0;i<n;i++)value.push_back(variable());
  for(int i=0;i<n;i++) {
   int a=variable(),b=variable(),v=value[i];
   for(int j=0;j<10+i;j++) {
    for(auto [selector,wire]:{std::pair{left[i][j],a},std::pair{right[i][j],b}}) {
     if(j<10) clause({-selector,(input&(1<<j))?wire:-wire});
     else {clause({-selector,-wire,value[j-10]});clause({-selector,wire,-value[j-10]});}
    }
   }
   int an=op[i][0],orr=op[i][1],nt=op[i][2];
   clause({-an,-v,a});clause({-an,-v,b});clause({-an,v,-a,-b});
   clause({-orr,v,-a});clause({-orr,v,-b});clause({-orr,-v,a,b});
   clause({-nt,v,a});clause({-nt,-v,-a});
  }
  clause({target(input)?value.back():-value.back()});
 }
 std::vector<Gate> model() {
  std::vector<Gate> c;
  for(int i=0;i<n;i++) {
   Gate g{};
   for(int j=0;j<3;j++)if(sat.val(op[i][j])>0)g.op=j;
   for(int j=0;j<10+i;j++){if(sat.val(left[i][j])>0)g.a=j;if(sat.val(right[i][j])>0)g.b=j;}
   c.push_back(g);
  }
  return c;
 }
};
bool eval(const std::vector<Gate>&c,int input) {
 std::vector<bool> v;
 for(int i=0;i<10;i++)v.push_back(input&(1<<i));
 for(auto g:c)v.push_back(g.op==0?v[g.a]&&v[g.b]:g.op==1?v[g.a]||v[g.b]:!v[g.a]);
 return v.back();
}
void dump(const std::vector<Gate>&c,const std::string&path) {
 std::ofstream f(path);
 for(size_t i=0;i<c.size();i++)f<<10+i<<" "<<(c[i].op==0?"and":c[i].op==1?"or":"not")<<" "<<c[i].a<<" "<<c[i].b<<"\n";
}
int main(int argc,char**argv) {
 if(argc!=6){std::cerr<<"usage: sat gates notmode seconds seed output-prefix\n";return 2;}
 int n=std::atoi(argv[1]),mode=std::atoi(argv[2]),seconds=std::atoi(argv[3]),seed=std::atoi(argv[4]);
 std::string prefix=argv[5];
 auto start=std::chrono::steady_clock::now();Timer timer;timer.end=start+std::chrono::seconds(seconds);
 Synthesis s(n,mode,seed);s.sat.connect_terminator(&timer);
 for(int x=0;x<1024;x++)if(!target(x)||std::popcount(unsigned(x))==2)s.sample(x);
 std::mt19937 rng(seed);
 std::cout<<"START gates="<<n<<" notMode="<<mode<<" seed="<<seed<<" samples="<<s.samples.size()<<std::endl;
 for(int round=0;;round++) {
  int result=s.sat.solve();
  std::cout<<"round="<<round<<" result="<<result<<" samples="<<s.samples.size()<<" variables="<<s.next<<" elapsed="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
  if(result!=10)return result==20?20:0;
  auto c=s.model();std::vector<int> errors;
  for(int x=0;x<1024;x++)if(eval(c,x)!=target(x))errors.push_back(x);
  dump(c,prefix+"-candidate.txt");
  std::cout<<"candidate errors="<<errors.size()<<std::endl;
  if(errors.empty()){dump(c,prefix+"-witness.txt");return 10;}
  std::shuffle(errors.begin(),errors.end(),rng);
  for(size_t i=0;i<std::min(size_t(12),errors.size());i++)s.sample(errors[i]);
 }
}
